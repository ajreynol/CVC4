/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Wrapper on linear solver
 */

#include "theory/arith/linear/linear_solver.h"

#include "theory/arith/arith_rewriter.h"
#include "expr/attribute.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

LinearSolver::LinearSolver(Env& env,
                           TheoryState& ts,
                           InferenceManager& im,
                           BranchAndBound& bab)
    : EnvObj(env), d_im(im), d_internal(env, *this, ts, bab), d_internalToExternal(userContext())
{
}

void LinearSolver::finishInit(eq::EqualityEngine* ee)
{
  d_internal.finishInit(ee);
}
void LinearSolver::preRegisterTerm(TNode n) { d_internal.preRegisterTerm(n); }
void LinearSolver::propagate(Theory::Effort e) { d_internal.propagate(e); }

TrustNode LinearSolver::explain(TNode n)
{
  Node in = convert(n, true);
  TrustNode ret = d_internal.explain(in);
  return convertTrust(ret, false);
}

void LinearSolver::collectModelValues(const std::set<Node>& termSet,
                                      std::map<Node, Node>& arithModel,
                                      std::map<Node, Node>& arithModelIllTyped)
{
  d_internal.collectModelValues(termSet, arithModel, arithModelIllTyped);
}

void LinearSolver::presolve() { d_internal.presolve(); }

void LinearSolver::notifyRestart() { d_internal.notifyRestart(); }

Theory::PPAssertStatus LinearSolver::ppAssert(
    TrustNode tin, TrustSubstitutionMap& outSubstitutions)
{
  TrustNode tini = convertTrust(tin, true);
  return d_internal.ppAssert(tini, outSubstitutions);
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
  Node ilit = convert(lit, true);
  return d_internal.entailmentCheck(ilit);
}
bool LinearSolver::preCheck(Theory::Effort level, bool newFacts)
{
  return d_internal.preCheck(level, newFacts);
}
void LinearSolver::preNotifyFact(TNode fact)
{
  Node ifact = convert(fact, true);
  d_internal.preNotifyFact(ifact);
}
bool LinearSolver::postCheck(Theory::Effort level)
{
  return d_internal.postCheck(level);
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
  return d_im.trustedLemma(convertTrust(lemma, false), id);
}

void LinearSolver::outputTrustedConflict(TrustNode conf, InferenceId id)
{
  d_im.trustedConflict(convertTrust(conf, false), id);
}

void LinearSolver::outputPropagate(TNode lit)
{
  Node elit = convert(lit, false);
  d_im.propagateLit(elit);
}

void LinearSolver::spendResource(Resource r) { d_im.spendResource(r); }

/**
 * Internal attribute
 */
struct LinearInternalAttributeId
{
};
using LinearInternalAttribute =
    expr::Attribute<LinearInternalAttributeId, Node>;

Node LinearSolver::convert(Node n, bool toInternal)
{
  return n;
  Kind nk = n.getKind();
  switch (nk)
  {
    case Kind::EQUAL:
    {
      Node nr;
      context::CDHashMap<Node, Node>::iterator it;
      if (toInternal)
      {
        LinearInternalAttribute iattr;
        nr = n.getAttribute(iattr);
        if (nr.isNull())
        {
          // remember the attribute
          nr = ArithRewriter::rewriteEquality(n);
          n.setAttribute(iattr, nr);
        }
        if (nr.isConst())
        {
          // constant!
        }
        it = d_internalToExternal.find(nr);
        if (it!=d_internalToExternal.end())
        {
          // already mapped, we have discovered equivalent atoms
          
        }
        else
        {
          d_internalToExternal[nr] = n;
        }
      }
      else
      {
        // should be mapped
        it = d_internalToExternal.find(nr);
        Assert (it!=d_internalToExternal.end());
        return it->second;
      }
      return nr;
    }
      break;
    case Kind::NOT:
    {
      return convert(n[0], toInternal).notNode();
    }
    case Kind::OR:
    case Kind::AND:
    {
      Assert (!toInternal);
      bool childChanged = false;
      std::vector<Node> echildren;
      for (const Node& nc : n)
      {
        Node nce = convert(nc, toInternal);
        childChanged = childChanged || nce != nc;
        echildren.emplace_back(nce);
      }
      if (childChanged)
      {
        return NodeManager::currentNM()->mkNode(nk, echildren);
      }
    }
    break;
    default: break;
  }
  return n;
}

TrustNode LinearSolver::convertTrust(const TrustNode& tn, bool toInternal)
{
  Node nn = tn.getProven();
  Node nnc = convert(nn, toInternal);
  if (nn != nnc)
  {
    // TODO: preserve proof
    return TrustNode::mkTrustNode(tn.getKind(), nnc);
  }
  return tn;
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
