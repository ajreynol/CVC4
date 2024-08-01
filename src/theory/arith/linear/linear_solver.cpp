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

#include "theory/arith/linear/linear_solver.h"

#include "expr/attribute.h"
#include "theory/arith/arith_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

LinearSolver::LinearSolver(Env& env,
                           TheoryState& ts,
                           InferenceManager& im,
                           BranchAndBound& bab)
    : EnvObj(env),
      d_im(im),
      d_internal(env, *this, ts, bab),
      d_allTerms(context()),
      d_arithTerms(context()),
      d_allPreds(context()),
      d_arithPreds(context()),
      d_nonArithAsserts(context()),
      d_arithReduced(userContext())
{
}

void LinearSolver::finishInit(eq::EqualityEngine* ee)
{
  d_internal.finishInit(ee);
}
void LinearSolver::preRegisterTerm(TNode n) { preRegisterTermDebug(n, false); }

void LinearSolver::preRegisterTermDebug(TNode n, bool isArith)
{
  TypeNode tn = n.getType();
  if (tn.isRealOrInt())
  {
    if (d_allTerms.find(n) == d_allTerms.end())
    {
      d_allTerms.insert(n);
      if (!Theory::isLeafOf(n, THEORY_ARITH))
      {
        isArith = true;
        for (const Node& nc : n)
        {
          preRegisterTermDebug(nc, true);
        }
        d_internal.preRegisterTerm(n);
      }
    }
    if (isArith)
    {
      Trace("ajr-temp") << "term " << n << std::endl;
      d_arithTerms.insert(n);
    }
  }
  else if (tn.isBoolean())
  {
    d_allPreds.insert(n);
    Node na = isArithmeticFact(n);
    if (!na.isNull())
    {
      Trace("ajr-temp") << "predicate " << na << std::endl;
      d_arithPreds.insert(na);
      for (const Node& nc : na)
      {
        preRegisterTermDebug(nc, true);
      }
      d_internal.preRegisterTerm(na);
    }
  }
  Trace("ajr-temp") << "at " << d_arithTerms.size() << " / "
                    << d_allTerms.size() << " terms, " << d_arithPreds.size()
                    << " / " << d_allPreds.size() << " predicates" << std::endl;
}

Node LinearSolver::isArithmeticFact(TNode n)
{
  Kind nk = n.getKind();
  if (nk == Kind::EQUAL)
  {
    if (!Theory::isLeafOf(n[0], THEORY_ARITH)
        || !Theory::isLeafOf(n[1], THEORY_ARITH))
    {
      return n;
    }
    return Node::null();
  }
  else if (nk == Kind::EQ)
  {
    return nodeManager()->mkNode(Kind::EQUAL, n[0], n[1]);
  }
  return n;
}

void LinearSolver::propagate(Theory::Effort e) { d_internal.propagate(e); }

TrustNode LinearSolver::explain(TNode n) { return d_internal.explain(n); }

void LinearSolver::collectModelValues(const std::set<Node>& termSet,
                                      std::map<Node, Node>& arithModel,
                                      std::map<Node, Node>& arithModelIllTyped)
{
  std::set<Node> atermSet;
  std::vector<Node> natermSet;
  for (const Node& t : termSet)
  {
    if (d_arithTerms.find(t) != d_arithTerms.end())
    {
      atermSet.insert(t);
    }
    else
    {
      natermSet.push_back(t);
    }
  }
  d_internal.collectModelValues(atermSet, arithModel, arithModelIllTyped);
}

void LinearSolver::presolve() { d_internal.presolve(); }

void LinearSolver::notifyRestart() { d_internal.notifyRestart(); }

Theory::PPAssertStatus LinearSolver::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  return d_internal.ppAssert(tin, outSubstitutions);
}
void LinearSolver::ppStaticLearn(TNode in, NodeBuilder& learned)
{
  d_internal.ppStaticLearn(in, learned);
}
EqualityStatus LinearSolver::getEqualityStatus(TNode a, TNode b)
{
  return d_internal.getEqualityStatus(a, b);
}
void LinearSolver::notifySharedTerm(TNode n) { d_internal.notifySharedTerm(n); }
Node LinearSolver::getCandidateModelValue(TNode var)
{
  return d_internal.getCandidateModelValue(var);
}
std::pair<bool, Node> LinearSolver::entailmentCheck(TNode lit)
{
  return d_internal.entailmentCheck(lit);
}
bool LinearSolver::preCheck(Theory::Effort level, bool newFacts)
{
  return d_internal.preCheck(level, newFacts);
}
void LinearSolver::preNotifyFact(TNode fact)
{
  bool pol = (fact.getKind() != Kind::NOT);
  Node atom = pol ? fact : fact[0];
  Node aatom = isArithmeticFact(atom);
  if (!aatom.isNull())
  {
    Node afact = fact;
    if (aatom != atom)
    {
      afact = pol ? aatom : aatom.notNode();
    }
    Trace("ajr-temp2") << "pre-notify " << afact << " from " << fact
                      << std::endl;
    d_internal.preNotifyFact(afact);
  }
  else if (d_arithReduced.find(atom) == d_arithReduced.end())
  {
    Trace("ajr-temp2") << "wait " << fact << std::endl;
    d_nonArithAsserts.push_back(fact);
  }
}
bool LinearSolver::postCheck(Theory::Effort level)
{
  bool ret = d_internal.postCheck(level);
  if (!ret && !d_im.hasSent())
  {
    Trace("ajr-temp2") << "Checking " << d_nonArithAsserts.size()
                      << " waiting assertions..." << std::endl;
    for (const Node& fact : d_nonArithAsserts)
    {
      bool pol = (fact.getKind() != Kind::NOT);
      Node atom = pol ? fact : fact[0];
      size_t count = 0;
      for (const Node& t : atom)
      {
        Assert(atom.getKind() == Kind::EQUAL);
        if (d_arithTerms.find(t) != d_arithTerms.end() || t.isConst())
        {
          count++;
        }
      }
      if (count==2)
      {
        // reduce
        d_arithReduced.insert(atom);
        Node atomr = rewrite(atom);
        Node eqAtom = nodeManager()->mkNode(Kind::EQ, atomr[0], atomr[1]);
        Node lem = atom.eqNode(eqAtom);
        TrustNode tlem = TrustNode::mkTrustLemma(lem);
        outputTrustedLemma(tlem, InferenceId::ARITH_EQUAL_EQ_INTRO);
      }
    }
  }
  return ret;
}
bool LinearSolver::foundNonlinear() const
{
  return d_internal.foundNonlinear();
}
ArithCongruenceManager* LinearSolver::getCongruenceManager()
{
  return d_internal.getCongruenceManager();
}

bool LinearSolver::outputTrustedLemma(TrustNode lemma, InferenceId id)
{
  return d_im.trustedLemma(lemma, id);
}

void LinearSolver::outputTrustedConflict(TrustNode conf, InferenceId id)
{
  d_im.trustedConflict(conf, id);
}

void LinearSolver::outputPropagate(TNode lit) { d_im.propagateLit(lit); }

void LinearSolver::spendResource(Resource r) { d_im.spendResource(r); }

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
