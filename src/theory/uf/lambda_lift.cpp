/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of lambda lifting.
 */

#include "theory/uf/lambda_lift.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/sort_type_size.h"
#include "options/uf_options.h"
#include "proof/proof.h"
#include "smt/env.h"
#include "theory/uf/function_const.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace uf {

LambdaLift::LambdaLift(Env& env)
    : EnvObj(env),
      d_lifted(userContext()),
      d_lambdaMap(userContext()),
      d_epg(env.isTheoryProofProducing()
                ? new EagerProofGenerator(env, userContext(), "LambdaLift::epg")
                : nullptr)
{
}

TrustNode LambdaLift::lift(Node node)
{
  if (d_lifted.find(node) != d_lifted.end())
  {
    return TrustNode::null();
  }
  d_lifted.insert(node);
  Node assertion = getAssertionFor(node);
  if (assertion.isNull())
  {
    return TrustNode::null();
  }
  // if no proofs, return lemma with no generator
  if (d_epg == nullptr)
  {
    return TrustNode::mkTrustLemma(assertion);
  }
  Node skolem = getSkolemFor(node);
  Assert(!skolem.isNull());
  Node eq = skolem.eqNode(node);
  // --------------- MACRO_SR_PRED_INTRO
  // k = lambda x. t
  // ------------------- MACRO_SR_PRED_INTRO
  // forall x. (k x) = t
  // We do this in two steps, where k -> lambda x. t is used as a subsitution
  // to avoid rare proof checking errors where the conclusion is not
  // provable in one step. In particular, in some rare cases we have that
  // rewrite(toOriginal(rewrite(F))) is not true. For instance, we may end
  // up with (@ (@ f a) b) = (f a b) which does not rewrite to true.
  CDProof cdp(d_env);
  cdp.addStep(eq, ProofRule::MACRO_SR_PRED_INTRO, {}, {eq});
  cdp.addStep(assertion, ProofRule::MACRO_SR_PRED_INTRO, {eq}, {assertion});
  std::shared_ptr<ProofNode> pf = cdp.getProofFor(assertion);
  return d_epg->mkTrustNode(assertion, pf);
}

bool LambdaLift::needsLift(const Node& lam)
{
  Assert(lam.getKind() == Kind::LAMBDA);
  std::map<Node, bool>::iterator it = d_needsLift.find(lam);
  if (it != d_needsLift.end())
  {
    return it->second;
  }
  // Model construction considers types in order of their type size
  // (SortTypeSize::getTypeSize). If the lambda has a free variable, that
  // comes later in the model construction, it may need to be lifted eagerly.
  // As an example, say f : Int -> Int, g : Int x Int -> Int
  // The following lambdas require eager lifting:
  // - (lambda ((x Int)) (g x x))
  // - (lambda ((x Int) (y Int)) (f (g x y)))
  // The following lambads do not require eager lifting:
  // - (lambda ((x Int)) (+ x 1)), since it has no free symbols.
  // - (lambda ((x Int) (y Int)) (f x)), since its free symbol f has a type
  // Int -> Int which is processed before the type of the lambda, i.e.
  // Int x Int -> Int.
  // Note that we only eagerly lift lambdas that furthermore impact model
  // construction, which is only the case if the lambda occurs as an argument
  // to a APPLY_UF or is equated to another function symbol.
  bool shouldLift = false;
  std::unordered_set<Node> syms;
  expr::getSymbols(lam[1], syms);
  SortTypeSize sts;
  size_t lsize = sts.getTypeSize(lam.getType());
  Trace("uf-lazy-ll") << "Lift " << lam << "?" << std::endl;
  for (const Node& v : syms)
  {
    TypeNode tn = v.getType();
    if (!tn.isFirstClass())
    {
      // don't need to worry about constructor/selector/testers/etc.
      continue;
    }
    size_t vsize = sts.getTypeSize(tn);
    if (vsize >= lsize)
    {
      shouldLift = true;
      Trace("uf-lazy-ll") << "...yes due to " << v << std::endl;
      break;
    }
  }
  d_needsLift[lam] = shouldLift;
  return shouldLift;
}

bool LambdaLift::isLifted(const Node& node) const
{
  return d_lifted.find(node)!=d_lifted.end();
}

TrustNode LambdaLift::ppRewrite(Node node, std::vector<SkolemLemma>& lems)
{
  Node lam = FunctionConst::toLambda(node);
  TNode skolem = getSkolemFor(lam);
  if (skolem.isNull())
  {
    return TrustNode::null();
  }
  d_lambdaMap[skolem] = lam;
  bool shouldLift = true;
  if (options().uf.ufHoLazyLambdaLift)
  {
    // We never lift eagerly. Lambdas that may induce inconsistencies based
    // on the symbols in their bodies are lifted lazily if/when they become
    // equal to ordinary function symbols. This is handled in the ho extension.
    shouldLift = false;
  }
  if (shouldLift)
  {
    TrustNode trn = lift(lam);
    if (!trn.isNull())
    {
      lems.push_back(SkolemLemma(trn, skolem));
    }
  }
  // if no proofs, return lemma with no generator
  if (d_epg == nullptr)
  {
    return TrustNode::mkTrustRewrite(node, skolem);
  }
  Node eq = node.eqNode(skolem);
  return d_epg->mkTrustedRewrite(
      node, skolem, ProofRule::MACRO_SR_PRED_INTRO, {eq});
}

Node LambdaLift::getLambdaFor(TNode skolem) const
{
  NodeNodeMap::const_iterator it = d_lambdaMap.find(skolem);
  if (it == d_lambdaMap.end())
  {
    return Node::null();
  }
  return it->second;
}

bool LambdaLift::isLambdaFunction(TNode n) const
{
  return !getLambdaFor(n).isNull();
}

Node LambdaLift::getAssertionFor(TNode node)
{
  Node assertion;
  Node lambda = FunctionConst::toLambda(node);
  if (!lambda.isNull())
  {
    TNode skolem = getSkolemFor(node);
    Assert(!skolem.isNull());
    NodeManager* nm = node.getNodeManager();
    // The new assertion
    std::vector<Node> children;
    // bound variable list
    children.push_back(lambda[0]);
    // body
    std::vector<Node> skolem_app_c;
    skolem_app_c.push_back(skolem);
    skolem_app_c.insert(skolem_app_c.end(), lambda[0].begin(), lambda[0].end());
    Node skolem_app = nm->mkNode(Kind::APPLY_UF, skolem_app_c);
    skolem_app_c[0] = lambda;
    Node rhs = nm->mkNode(Kind::APPLY_UF, skolem_app_c);
    // For the sake of proofs, we use
    // (= (k t1 ... tn) ((lambda (x1 ... xn) s) t1 ... tn)) here. This is instead of
    // (= (k t1 ... tn) s); the former is more accurate since
    // beta reduction uses capture-avoiding substitution, which implies that
    // ((lambda (y1 ... yn) s) t1 ... tn) is alpha-equivalent but not
    // necessarily syntactical equal to s.
    children.push_back(skolem_app.eqNode(rhs));
    // axiom defining skolem
    assertion = nm->mkNode(Kind::FORALL, children);

    // Lambda lifting is trivial to justify, hence we don't set a proof
    // generator here. In particular, replacing the skolem introduced
    // here with its original lambda ensures the new assertion rewrites
    // to true.
    // For example, if (lambda y. t[y]) has skolem k, then this lemma is:
    //   forall x. k(x)=t[x]
    // whose witness form rewrites
    //   forall x. (lambda y. t[y])(x)=t[x] --> forall x. t[x]=t[x] --> true
  }
  return assertion;
}

Node LambdaLift::getSkolemFor(TNode node)
{
  Node skolem;
  Node lambda = FunctionConst::toLambda(node);
  if (!lambda.isNull())
  {
    // if a lambda, return the purification variable for the node. We ignore
    // lambdas with free variables, which can occur beneath quantifiers
    // during preprocessing.
    if (!expr::hasFreeVar(node))
    {
      Trace("rtf-proof-debug")
          << "RemoveTermFormulas::run: make LAMBDA skolem" << std::endl;
      // Make the skolem to represent the lambda
      skolem = SkolemManager::mkPurifySkolem(node);
    }
  }
  return skolem;
}

TrustNode LambdaLift::betaReduce(TNode node) const
{
  Kind k = node.getKind();
  if (k == Kind::APPLY_UF)
  {
    Node op = node.getOperator();
    Node opl = getLambdaFor(op);
    if (!opl.isNull())
    {
      std::vector<Node> args(node.begin(), node.end());
      Node app = betaReduce(opl, args);
      Trace("uf-lazy-ll") << "Beta reduce: " << node << " -> " << app
                          << std::endl;
      if (d_epg == nullptr)
      {
        return TrustNode::mkTrustRewrite(node, app);
      }
      return d_epg->mkTrustedRewrite(
          node, app, ProofRule::MACRO_SR_PRED_INTRO, {node.eqNode(app)});
    }
  }
  // otherwise, unchanged
  return TrustNode::null();
}

Node LambdaLift::betaReduce(TNode lam, const std::vector<Node>& args) const
{
  Assert(lam.getKind() == Kind::LAMBDA);
  std::vector<Node> betaRed;
  betaRed.push_back(lam);
  betaRed.insert(betaRed.end(), args.begin(), args.end());
  Node app = nodeManager()->mkNode(Kind::APPLY_UF, betaRed);
  app = rewrite(app);
  return app;
}

}  // namespace uf
}  // namespace theory
}  // namespace cvc5::internal
