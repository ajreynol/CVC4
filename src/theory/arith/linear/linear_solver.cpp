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

#include "expr/attribute.h"
#include "theory/arith/arith_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace arith::linear {

std::string toStringNode(TNode n, TNode on)
{
  std::stringstream ss;
  ss << n;
  if (n != on)
  {
    ss << " (from " << on << ")";
  }
  return ss.str();
}

LinearSolver::LinearSolver(Env& env,
                           TheoryState& ts,
                           InferenceManager& im,
                           BranchAndBound& bab)
    : EnvObj(env),
      d_im(im),
      d_internal(env, *this, ts, bab),
      d_acm(nullptr),
      d_externalToInternal(userContext()),
      d_internalToExternal(userContext()),
      d_inFlushPending(false)
{
}

void LinearSolver::finishInit(eq::EqualityEngine* ee)
{
  d_internal.finishInit(ee);
  // Set the congruence manager on the equality solver. If the congruence
  // manager exists, it is responsible for managing the notifications from
  // the equality engine, which the equality solver forwards to it.
  d_acm = d_internal.getCongruenceManager();
}

void LinearSolver::preRegisterTerm(TNode n)
{
  if (n.getType().isBoolean())
  {
    Node in = convertAssertToInternal(n);
    if (in.isNull())
    {
      flushPending();
    }
    else
    {
      Trace("linear-solver")
          << "preRegisterTerm: " << toStringNode(in, n) << std::endl;
      d_internal.preRegisterTerm(in);
    }
    return;
  }
  Trace("linear-solver") << "preRegisterTerm: " << n << std::endl;
  d_internal.preRegisterTerm(n);
}

void LinearSolver::propagate(Theory::Effort e) { d_internal.propagate(e); }

TrustNode LinearSolver::explain(TNode n)
{
  Node in = convert(n, true);
  Trace("linear-solver") << "explain: " << toStringNode(in, n) << std::endl;
  // came from external, thus should have an internal mapping
  Assert(!in.isNull());
  TrustNode ret = d_internal.explain(in);
  TrustNode eret = convertTrust(ret, false);
  Trace("linear-solver") << "explain returns: "
                         << toStringNode(eret.getNode(), ret.getNode())
                         << std::endl;
  return eret;
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
  Trace("linear-solver") << "ppAssert: " << tin.getNode() << std::endl;
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
void LinearSolver::notifySharedTerm(TNode n)
{
  Trace("linear-solver") << "notifySharedTerm: " << n << std::endl;
  d_internal.notifySharedTerm(n);
}
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
  Node ifact = convertAssertToInternal(fact);
  Trace("linear-solver") << "preNotifyFact: " << toStringNode(ifact, fact)
                         << std::endl;
  if (ifact.isNull())
  {
    // add pending
    flushPending();
  }
  else
  {
    d_internal.preNotifyFact(ifact);
  }
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
  TrustNode elemma = convertTrust(lemma, false);
  Trace("linear-solver") << "outputTrustedLemma: "
                         << toStringNode(elemma.getNode(), lemma.getNode())
                         << std::endl;
  return d_im.trustedLemma(elemma, id);
}

void LinearSolver::outputTrustedConflict(TrustNode conf, InferenceId id)
{
  TrustNode econf = convertTrust(conf, false);
  Trace("linear-solver") << "outputTrustedConflict: "
                         << toStringNode(econf.getNode(), conf.getNode())
                         << std::endl;
  d_im.trustedConflict(econf, id);
}

void LinearSolver::outputPropagate(TNode lit)
{
  Node elit = convert(lit, false);
  Trace("linear-solver") << "outputPropagate: " << toStringNode(elit, lit)
                         << std::endl;
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

Node LinearSolver::convertAssertToInternal(TNode n)
{
  bool pol = n.getKind() != Kind::NOT;
  TNode natom = pol ? n : n[0];
  if (natom.getKind() != Kind::EQUAL)
  {
    return n;
  }
  Node nr;
  context::CDHashMap<Node, Node>::iterator it =
      d_externalToInternal.find(natom);
  if (it != d_externalToInternal.end())
  {
    nr = it->second;
  }
  else
  {
    nr = convert(natom, true);
    if (nr.isConst())
    {
      // constant!
      d_pending.emplace_back(nr.getConst<bool>() ? Node(natom)
                                                 : natom.notNode());
      nr = Node::null();
      Trace("linear-solver") << "* reduce: " << natom << std::endl;
    }
    else
    {
      it = d_internalToExternal.find(nr);
      if (it != d_internalToExternal.end())
      {
        // already mapped, we have discovered equivalent atoms
        d_pending.emplace_back(natom.eqNode(it->second));
        nr = Node::null();
        Trace("linear-solver") << "* reduce: " << natom << std::endl;
      }
      else
      {
        d_internalToExternal[nr] = natom;
      }
    }
    d_externalToInternal[natom] = nr;
  }
  return (pol || nr.isNull()) ? nr : nr.notNode();
}

Node LinearSolver::convert(Node n, bool toInternal)
{
  Kind nk = n.getKind();
  switch (nk)
  {
    case Kind::EQUAL:
    {
      if (toInternal)
      {
        LinearInternalAttribute iattr;
        Node nr = n.getAttribute(iattr);
        if (nr.isNull())
        {
          // remember the attribute
          nr = ArithRewriter::rewriteEquality(n);
          n.setAttribute(iattr, nr);
          Trace("linear-solver")
              << "Rewrite equality: " << n << " --> " << nr << std::endl;
        }
        return nr;
      }
      // should be mapped
      context::CDHashMap<Node, Node>::iterator it =
          d_internalToExternal.find(n);
      if (it != d_internalToExternal.end())
      {
        return it->second;
      }
      Trace("linear-solver")
          << "WARN: assuming internal is external: " << n << std::endl;
      return n;
    }
    break;
    case Kind::NOT:
    {
      return convert(n[0], toInternal).notNode();
    }
    case Kind::IMPLIES:
    case Kind::OR:
    case Kind::AND:
    {
      Assert(!toInternal);
      bool childChanged = false;
      std::vector<Node> echildren;
      for (const Node& nc : n)
      {
        Node nce = convert(nc, toInternal);
        Assert(!nce.isNull());
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

void LinearSolver::flushPending()
{
  if (d_inFlushPending)
  {
    return;
  }
  d_inFlushPending = true;
  Trace("linear-solver") << "...flushPending" << std::endl;
  for (const Node& lem : d_pending)
  {
    Trace("linear-solver") << "...lemma " << lem << std::endl;
    TrustNode tlem = TrustNode::mkTrustLemma(lem);
    d_im.trustedLemma(tlem, InferenceId::ARITH_REWRITE_EQ_NORM);
  }
  d_pending.clear();
  Trace("linear-solver") << "...flushPending finished" << std::endl;
  d_inFlushPending = false;
}

TrustNode LinearSolver::eqExplain(TNode lit)
{
  if (d_acm != nullptr)
  {
    Node ilit = convert(lit, true);
    Trace("linear-solver") << "eqExplain " << toStringNode(ilit, lit)
                           << std::endl;
    // if we are using the congruence manager, consult whether it can explain
    if (d_acm->canExplain(ilit))
    {
      TrustNode texp = d_acm->explain(ilit);
      TrustNode etexp = convertTrust(texp, false);
      Trace("linear-solver")
          << "...return " << toStringNode(etexp.getNode(), texp.getNode())
          << std::endl;
      return etexp;
    }
    else
    {
      Trace("linear-solver") << "...not via congruence manager" << std::endl;
    }
  }
  // otherwise, don't explain
  return TrustNode::null();
}

bool LinearSolver::eqPropagate(Node lit, bool& conflict)
{
  if (d_acm != nullptr)
  {
    Trace("linear-solver") << "eqPropagate " << lit << std::endl;
    conflict = d_acm->propagate(lit);
    return true;
  }
  return false;
}

bool LinearSolver::eqConflictEqConstantMerge(TNode a, TNode b)
{
  if (d_acm != nullptr)
  {
    Node eq = a.eqNode(b);
    Trace("linear-solver") << "eqConflictEqConstantMerge " << a << " " << b
                           << std::endl;
    d_acm->propagate(eq);
    return true;
  }
  return false;
}

}  // namespace arith::linear
}  // namespace theory
}  // namespace cvc5::internal
