/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper on linear solver
 */

#include "theory/arith/linear/linear_solver_sub.h"

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "options/smt_options.h"
#include "proof/unsat_core.h"
#include "theory/arith/arith_rewriter.h"
#include "theory/arith/theory_arith.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

Node ArithPurifyNodeConverter::postConvert(Node n)
{
  if (n.getNumChildren() > 0 && Theory::isLeafOf(n, THEORY_ARITH))
  {
    return d_nm->getSkolemManager()->mkPurifySkolem(n);
  }
  return n;
}

LinearSolverSub::LinearSolverSub(Env& env, TheoryArith& containing)
    : LinearSolver(env),
      d_containing(containing),
      d_astate(*containing.getTheoryState()),
      d_im(containing.getInferenceManager()),
      d_smap(context()),
      d_smapExp(context()),
      d_aconv(nodeManager())
{
  // determine the options to use for the verification subsolvers we spawn
  // we start with the provided options
  d_subOptions.copyValues(options());
  // requires full proofs
  d_subOptions.write_smt().produceProofs = true;
  // don't do simplification, which can preprocess quantifiers to those not
  // occurring in the main solver
  d_subOptions.write_smt().simplificationMode =
      options::SimplificationMode::NONE;
  // requires unsat cores
  d_subOptions.write_smt().produceUnsatCores = true;
  // don't do this strategy
  d_subOptions.write_arith().arithSubSolver = false;
  // common terms
  d_true = nodeManager()->mkConst(true);
  d_false = nodeManager()->mkConst(false);
}

void LinearSolverSub::finishInit(eq::EqualityEngine* ee)
{
  // d_internal.finishInit(ee);
}
void LinearSolverSub::preRegisterTerm(TNode n)
{  // d_internal.preRegisterTerm(n);
}
void LinearSolverSub::propagate(Theory::Effort e)
{  // d_internal.propagate(e);
}

TrustNode LinearSolverSub::explain(TNode n)
{
  return TrustNode::null();  // d_internal.explain(n);
}

void LinearSolverSub::collectModelValues(
    const std::set<Node>& termSet,
    std::map<Node, Node>& arithModel,
    std::map<Node, Node>& arithModelIllTyped)
{
  // TODO
}

void LinearSolverSub::presolve() {}

void LinearSolverSub::notifyRestart() {}

Theory::PPAssertStatus LinearSolverSub::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return Theory::PP_ASSERT_STATUS_UNSOLVED;
}
void LinearSolverSub::ppStaticLearn(TNode in, NodeBuilder& learned) {}
EqualityStatus LinearSolverSub::getEqualityStatus(TNode a, TNode b)
{
  return EQUALITY_UNKNOWN;
}
void LinearSolverSub::notifySharedTerm(TNode n) {}
Node LinearSolverSub::getCandidateModelValue(TNode var) { return Node::null(); }
std::pair<bool, Node> LinearSolverSub::entailmentCheck(TNode lit)
{
  return std::pair<bool, Node>(false, Node::null());
}
bool LinearSolverSub::preCheck(Theory::Effort level, bool newFacts)
{
  return false;
}
void LinearSolverSub::preNotifyFact(TNode fact)
{
  Node cfact = d_aconv.convert(fact);
  Node crfact = d_smap.apply(cfact, d_env.getRewriter());
  if (crfact == d_false)
  {
    std::vector<Node> conflict = getSubsRewConflict(cfact);
    conflict.push_back(fact);
    Trace("sub-conflict") << "Conflict: " << conflict << std::endl;
    Node conf = nodeManager()->mkAnd(conflict);
    d_im.conflict(conf, InferenceId::ARITH_LINEAR_SUB_EAGER_SR);
  }
  else if (cfact.getKind() == Kind::EQUAL)
  {
    for (size_t i = 0; i < 2; i++)
    {
      if (cfact[i].isVar() && !d_smap.hasSubstitution(cfact[i]))
      {
        Node ns = d_smap.apply(cfact[1 - i]);
        if (!expr::hasSubterm(ns, cfact[i]))
        {
          d_smapExp[cfact[i]] = fact;
          d_smap.addSubstitution(cfact[i], cfact[1 - i]);
          break;
        }
      }
    }
  }
}

std::vector<Node> LinearSolverSub::getSubsRewConflict(const Node& lit)
{
  Trace("sub-conflict") << "Get conflict " << lit << std::endl;
  std::vector<Node> conflict;
  std::unordered_set<Node> processed;
  std::vector<Node> toProcess;
  toProcess.push_back(lit);
  do
  {
    Node curr = toProcess.back();
    Trace("sub-conflict") << "...process " << curr << std::endl;
    toProcess.pop_back();
    if (processed.find(curr) != processed.end())
    {
      continue;
    }
    processed.insert(curr);
    std::unordered_set<Node> syms;
    expr::getSymbols(curr, syms);
    context::CDHashMap<Node, Node>::iterator it;
    for (const Node& sym : syms)
    {
      it = d_smapExp.find(sym);
      if (it != d_smapExp.end())
      {
        Trace("sub-conflict") << "...substitution " << sym << std::endl;
        if (std::find(conflict.begin(), conflict.end(), it->second)==conflict.end())
        {
          conflict.push_back(it->second);
          Trace("sub-conflict") << "......include " << it->second << std::endl;
          toProcess.push_back(d_aconv.convert(it->second));
        }
      }
    }
  } while (!toProcess.empty());
  return conflict;
}

bool LinearSolverSub::postCheck(Theory::Effort level)
{
  if (level != Theory::EFFORT_FULL)
  {
    return false;
  }

  SubsolverSetupInfo ssi(d_env, d_subOptions);
  initializeSubsolver(d_subsolver, ssi, false);
  // assert and check-sat
  std::vector<Node> asserts;
  std::map<Node, Node> revMap;
  size_t nasserts = 0;
  Trace("linear-sub-solver") << "Check with subsolver..." << std::endl;
  for (Theory::assertions_iterator it = d_astate.factsBegin(THEORY_ARITH);
       it != d_astate.factsEnd(THEORY_ARITH);
       ++it)
  {
    nasserts++;
    Node fact = it->d_assertion;
    Node cfact = d_aconv.convert(fact);
    Node crfact = d_smap.apply(cfact, d_env.getRewriter());
    if (crfact == d_false)
    {
      std::vector<Node> conflict = getSubsRewConflict(cfact);
      conflict.push_back(fact);
      Node conf = nodeManager()->mkAnd(conflict);
      d_im.conflict(conf, InferenceId::ARITH_LINEAR_SUB_UC_SIMPLE);
      Trace("linear-sub-solver") << "...found conflict for " << fact << std::endl;
      Trace("linear-sub-solver") << "conflict is " << conflict << std::endl;
      return true;
    }
    else if (crfact != d_true)
    {
      asserts.push_back(cfact);
      revMap[cfact] = fact;
    }
  }
  Trace("linear-sub-solver") << asserts.size() << " / " << nasserts
                             << " relevant assertions" << std::endl;
  for (const Node& lit : asserts)
  {
    Trace("linear-sub-assert") << "- " << lit << std::endl;
    d_subsolver->assertFormula(lit);
  }
  Result r = d_subsolver->checkSat();
  Trace("linear-sub-solver") << "<<< ...result is " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    UnsatCore uc = d_subsolver->getUnsatCore();
    const std::vector<Node>& core = uc.getCore();
    std::vector<Node> origCore;
    std::map<Node, Node>::iterator itr;
    for (const Node& lit : core)
    {
      itr = revMap.find(lit);
      Assert(itr != revMap.end());
      origCore.push_back(itr->second);
    }
    Node ucc = nodeManager()->mkAnd(origCore);
    Trace("linear-sub-solver") << "Unsat core is " << ucc << std::endl;
    Trace("linear-sub-solver")
        << "Core size = " << uc.getCore().size() << std::endl;
    d_im.lemma(ucc.notNode(), InferenceId::ARITH_LINEAR_SUB_UC);
    return true;
  }
  return false;
}
bool LinearSolverSub::foundNonlinear() const { return false; }
ArithCongruenceManager* LinearSolverSub::getCongruenceManager()
{
  return nullptr;
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
