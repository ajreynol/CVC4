/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Hans-Jörg Schurr, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * The module for basic (non-DSL-dependent) automatic reconstructing proofs of
 * THEORY_REWRITE steps.
 */

#include "rewriter/basic_rewrite_rcons.h"

#include "proof/proof_checker.h"
#include "rewriter/rewrites.h"
#include "smt/env.h"
#include "theory/bv/theory_bv_rewrite_rules.h"
#include "theory/rewriter.h"
#include "theory/strings/arith_entail.h"
#include "util/rational.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace rewriter {

BasicRewriteRCons::BasicRewriteRCons(Env& env) : EnvObj(env) {}

bool BasicRewriteRCons::prove(
    CDProof* cdp, Node a, Node b, theory::TheoryId tid, MethodId mid)
{
  Node eq = a.eqNode(b);
  Trace("trewrite-rcons") << "Reconstruct " << eq << " (from " << tid << ", "
                          << mid << ")" << std::endl;
  Node lhs = eq[0];
  Node rhs = eq[1];
  // this probably should never happen
  if (eq[0] == eq[1])
  {
    Trace("trewrite-rcons") << "...REFL" << std::endl;
    cdp->addStep(eq, ProofRule::REFL, {}, {eq[0]});
    return true;
  }
  // first, check that maybe its just an evaluation step
  if (tryRule(cdp, eq, ProofRule::EVALUATE, {eq[0]}))
  {
    Trace("trewrite-rcons") << "...EVALUATE" << std::endl;
    return true;
  }

  // try theory rewrite (pre-rare)
  ProofRewriteRule prid =
      d_env.getRewriter()->findRule(a, b, theory::TheoryRewriteCtx::PRE_DSL);
  if (prid != ProofRewriteRule::NONE)
  {
    if (tryRule(
            cdp, eq, ProofRule::THEORY_REWRITE, {mkRewriteRuleNode(prid), a}))
    {
      Trace("trewrite-rcons") << "Reconstruct " << eq << " (from " << prid
                              << ", " << mid << ")" << std::endl;
      return true;
    }
  }
  Trace("trewrite-rcons") << "...(fail)" << std::endl;
  return false;
}

bool BasicRewriteRCons::postProve(
    CDProof* cdp, Node a, Node b, theory::TheoryId tid, MethodId mid)
{
  Node eq = a.eqNode(b);

  // try theory rewrite (post-rare)
  ProofRewriteRule prid =
      d_env.getRewriter()->findRule(a, b, theory::TheoryRewriteCtx::POST_DSL);
  if (prid != ProofRewriteRule::NONE)
  {
    if (tryRule(
            cdp, eq, ProofRule::THEORY_REWRITE, {mkRewriteRuleNode(prid), a}))
    {
      Trace("trewrite-rcons") << "Reconstruct (post) " << eq << " (from "
                              << prid << ", " << mid << ")" << std::endl;
      return true;
    }
  }

  Trace("trewrite-rcons") << "...(fail)" << std::endl;
  return false;
}

bool BasicRewriteRCons::tryRule(CDProof* cdp,
                                Node eq,
                                ProofRule r,
                                const std::vector<Node>& args)
{
  Trace("trewrite-rcons-debug") << "Try " << r << std::endl;
  ProofChecker* pc = d_env.getProofNodeManager()->getChecker();
  // do not provide expected, as this will always succeed if proof checking
  // is disabled
  Node res = pc->checkDebug(r, {}, args, Node::null(), "trewrite-rcons");
  if (!res.isNull() && res == eq)
  {
    cdp->addStep(eq, r, {}, args);
    return true;
  }
  return false;
}

bool BasicRewriteRCons::ensureProofForTheoryRewrite(CDProof* cdp,
                                                    ProofRewriteRule id,
                                                    const Node& lhs,
                                                    std::vector<Node>& subgoals)
{
  switch (id)
  {
    case ProofRewriteRule::MACRO_BOOL_NNF_NORM:
      if (ensureProofMacroBoolNnfNorm(cdp, lhs, subgoals))
      {
        return true;
      }
      break;
    case ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL:
      if (ensureProofMacroArithStringPredEntail(cdp, lhs, subgoals))
      {
        return true;
      }
      break;
    case ProofRewriteRule::MACRO_RE_INTER_UNION_INCLUSION:
      if (ensureProofMacroReInterUnionInclusion(cdp, lhs, subgoals))
      {
        return true;
      }
      break;
    default: break;
  }
  // default, just add the rewrite
  std::vector<Node> args;
  args.push_back(
      nodeManager()->mkConstInt(Rational(static_cast<uint32_t>(id))));
  args.push_back(lhs);
  Node rhs = d_env.getRewriter()->rewriteViaRule(id, lhs);
  Node eq = lhs.eqNode(rhs);
  cdp->addStep(eq, ProofRule::THEORY_REWRITE, {}, args);
  return true;
}

bool BasicRewriteRCons::ensureProofMacroBoolNnfNorm(CDProof* cdp,
                                                    const Node& lhs,
                                                    std::vector<Node>& subgoals)
{
  return false;
}

bool BasicRewriteRCons::ensureProofMacroArithStringPredEntail(
    CDProof* cdp, const Node& lhs, std::vector<Node>& subgoals)
{
  return false;
  theory::strings::ArithEntail ae(d_env.getRewriter());
  Node exp;
  Node ret = ae.rewritePredViaEntailment(lhs, exp);
  Node expRew = rewrite(exp);
  Node zero = nodeManager()->mkConstInt(Rational(0));
  Node geq = nodeManager()->mkNode(Kind::GEQ, expRew, zero);
  Node approx = ae.findApprox(expRew);
  if (approx.isNull())
  {
    Assert(false);
    return false;
  }
  Node truen = nodeManager()->mkConst(true);
  // (>= approx 0) = true
  Node approxGeq = nodeManager()->mkNode(Kind::GEQ, approx, zero);
  Node teq = approxGeq.eqNode(truen);
  cdp->addTheoryRewriteStep(teq, ProofRewriteRule::ARITH_STRING_PRED_ENTAIL);
  if (approx != expRew)
  {
    Node aeq = geq.eqNode(approxGeq);
    // (>= expRew 0) = (>= approx 0)
    cdp->addTheoryRewriteStep(aeq,
                              ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX);
    std::vector<Node> transEq;
    transEq.push_back(aeq);
    transEq.push_back(teq);
    teq = geq.eqNode(truen);
    cdp->addStep(teq, ProofRule::TRANS, transEq, {});
  }
  // now have (>= expRew 0) = true

  Node eqRet = lhs.eqNode(ret);
  if (eqRet != teq)
  {
    cdp->addStep(geq, ProofRule::TRUE_ELIM, {teq}, {});
    Assert(exp.getKind() == Kind::SUB);
    Node posTerm = exp[0].getKind() == Kind::SUB ? exp[0][0] : exp[0];
    Assert(posTerm == lhs[0] || posTerm == lhs[1]);
    bool isLhs = posTerm == lhs[0];
    ProofChecker* pc = d_env.getProofNodeManager()->getChecker();

    // e.g. (= t -1) = false  is implied by  (>= (- (- 1 t) 1) 0) = true
  }
  return true;
}

bool BasicRewriteRCons::ensureProofMacroReInterUnionInclusion(
    CDProof* cdp, const Node& lhs, std::vector<Node>& subgoals)
{
  return false;
}

}  // namespace rewriter
}  // namespace cvc5::internal
