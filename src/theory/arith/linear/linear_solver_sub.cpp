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
#include "theory/arith/arith_rewriter.h"
#include "options/smt_options.h"
#include "theory/arith/theory_arith.h"
#include "proof/unsat_core.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

LinearSolverSub::LinearSolverSub(Env& env, TheoryArith& containing)
    : LinearSolver(env),
      d_containing(containing),
      d_astate(*containing.getTheoryState()),
      d_im(containing.getInferenceManager())
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

void LinearSolverSub::collectModelValues(const std::set<Node>& termSet,
                                      std::map<Node, Node>& arithModel,
                                      std::map<Node, Node>& arithModelIllTyped)
{

}

void LinearSolverSub::presolve()
{
}

void LinearSolverSub::notifyRestart()
{
}

Theory::PPAssertStatus LinearSolverSub::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return Theory::PP_ASSERT_STATUS_UNSOLVED;
}
void LinearSolverSub::ppStaticLearn(TNode in, NodeBuilder& learned)
{
}
EqualityStatus LinearSolverSub::getEqualityStatus(TNode a, TNode b)
{
  return EQUALITY_UNKNOWN;
}
void LinearSolverSub::notifySharedTerm(TNode n)
{
}
Node LinearSolverSub::getCandidateModelValue(TNode var)
{
  return Node::null();
}
std::pair<bool, Node> LinearSolverSub::entailmentCheck(TNode lit)
{
  return std::pair<bool, Node>(
      false, Node::null());
}
bool LinearSolverSub::preCheck(Theory::Effort level, bool newFacts)
{
  return false;
}
void LinearSolverSub::preNotifyFact(TNode fact)
{
}
bool LinearSolverSub::postCheck(Theory::Effort level)
{
  if (level!=Theory::EFFORT_FULL)
  {
    return false;
  }
  
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  initializeSubsolver(d_subsolver, ssi, false);
  // assert and check-sat  
  for (Theory::assertions_iterator it = d_astate.factsBegin(THEORY_ARITH);
       it != d_astate.factsEnd(THEORY_ARITH);
       ++it)
  {
    Node lit = it->d_assertion;
    Trace("opaque-assert") << "- " << lit << std::endl;
    d_subsolver->assertFormula(lit);
  }
  Result r = d_subsolver->checkSat();
  Trace("linear-sub-solver") << "<<< ...result is " << r << std::endl;
  if (r.getStatus() == Result::UNSAT)
  {
    UnsatCore uc = d_subsolver->getUnsatCore();
    Node ucc = nodeManager()->mkAnd(uc.getCore());
    Trace("linear-sub-solver") << "Unsat core is " << ucc << std::endl;
    Trace("linear-sub-solver") << "Core size = " << uc.getCore().size()
                           << std::endl;
    d_im.lemma(ucc.notNode(), InferenceId::ARITH_LINEAR_SUB_UC);
  }
  return false;
}
bool LinearSolverSub::foundNonlinear() const
{
  return false;
}
ArithCongruenceManager* LinearSolverSub::getCongruenceManager()
{
  return nullptr;
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
