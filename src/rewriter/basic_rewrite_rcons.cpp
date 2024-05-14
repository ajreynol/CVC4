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
#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/arith_proof_utilities.h"
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
  Trace("brc-macro") << "Expand entailment for " << lhs << " == " << ret
                     << std::endl;
  Trace("brc-macro") << "- explanation is " << exp << std::endl;
  Node expRew = rewrite(exp);
  Node zero = nodeManager()->mkConstInt(Rational(0));
  Node geq = nodeManager()->mkNode(Kind::GEQ, expRew, zero);
  Trace("brc-macro") << "- rewritten predicate is " << geq << std::endl;
  Node approx = ae.findApprox(expRew);
  if (approx.isNull())
  {
    Trace("brc-macro") << "...failed to find approximation" << std::endl;
    AlwaysAssert(false);
    return false;
  }
  Node truen = nodeManager()->mkConst(true);
  // (>= approx 0) = true
  Node approxGeq = nodeManager()->mkNode(Kind::GEQ, approx, zero);
  Trace("brc-macro") << "- approximation predicate is " << approxGeq
                     << std::endl;
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
  // now have (>= expRew 0) = true, stored in teq

  if (lhs == expRew)
  {
    Trace("brc-macro") << "...success (no normalization)" << std::endl;
    return true;
  }
  Node retEq = lhs.eqNode(ret);
  if (!ret.getConst<bool>())
  {
    Trace("brc-macro") << "- false case, setting up conflict" << std::endl;
    cdp->addStep(geq, ProofRule::TRUE_ELIM, {teq}, {});
    Assert(exp.getKind() == Kind::SUB);
    Node posTerm = exp[0].getKind() == Kind::SUB ? exp[0][0] : exp[0];
    Assert(posTerm == lhs[0] || posTerm == lhs[1]);
    bool isLhs = posTerm == lhs[0];
    Trace("brc-macro") << "- isLhs is " << isLhs << std::endl;
    std::vector<Node> children;
    children.push_back(geq);
    children.push_back(lhs);
    std::vector<Node> args;
    // must flip signs to ensure it is <=, as required by MACRO_ARITH_SUM_UB.
    args.push_back(nodeManager()->mkConstInt(Rational(-1)));
    args.push_back(nodeManager()->mkConstInt(Rational(isLhs ? 1 : -1)));
    Trace("brc-macro") << "- compute sum bound for " << children << " " << args
                       << std::endl;
    Node sumBound = theory::arith::expandMacroSumUb(children, args, cdp);
    Trace("brc-macro") << "- sum bound is " << sumBound << std::endl;
    if (sumBound.isNull())
    {
      AlwaysAssert(false);
      Trace("brc-macro") << "...failed to add" << std::endl;
      return false;
    }
    Assert(sumBound.getNumChildren() == 2);
    Node py = nodeManager()->mkNode(Kind::SUB, sumBound[0], sumBound[1]);
    theory::arith::PolyNorm pn = theory::arith::PolyNorm::mkPolyNorm(py);
    Rational pyr;
    if (!pn.isConstant(pyr))
    {
      Trace("brc-macro") << "...failed to prove constant after normalization"
                         << std::endl;
      AlwaysAssert(false);
      return false;
    }
    Node cpred = nodeManager()->mkNode(
        sumBound.getKind(), nodeManager()->mkConstInt(pyr), zero);
    if (!theory::arith::PolyNorm::isArithPolyNormAtom(sumBound, cpred))
    {
      Trace("brc-macro") << "...failed to show normalization" << std::endl;
      AlwaysAssert(false);
      return false;
    }
    Node peq = sumBound.eqNode(cpred);
    cdp->addStep(peq, ProofRule::ARITH_POLY_NORM, {}, {peq});
    Node cceq = cpred.eqNode(ret);
    cdp->addStep(cceq, ProofRule::EVALUATE, {}, {cpred});
    Node sumEqFalse = sumBound.eqNode(ret);
    cdp->addStep(sumEqFalse, ProofRule::TRANS, {peq, cceq}, {});
    Node notSum = sumBound.notNode();
    cdp->addStep(notSum, ProofRule::FALSE_ELIM, {sumEqFalse}, {});
    cdp->addStep(ret, ProofRule::CONTRA, {sumBound, notSum}, {});
    Node notLhs = lhs.notNode();
    cdp->addStep(notLhs, ProofRule::SCOPE, {ret}, {lhs});
    cdp->addStep(retEq, ProofRule::FALSE_INTRO, {notLhs}, {});
  }
  else
  {
    Trace("brc-macro") << "- true case, prove equal" << std::endl;
    Assert(lhs.getKind() == Kind::GEQ);
    // should be able to show equivalent by polynomial normalization
    if (!theory::arith::PolyNorm::isArithPolyNormAtom(lhs, geq))
    {
      Trace("brc-macro") << "...failed to show normalization (true case) "
                         << lhs << " and " << geq << std::endl;
      AlwaysAssert(false);
      return false;
    }
    Node peq = lhs.eqNode(geq);
    cdp->addStep(peq, ProofRule::ARITH_POLY_NORM, {}, {peq});
    cdp->addStep(retEq, ProofRule::TRANS, {peq, teq}, {});
  }
  Trace("brc-macro") << "...success" << std::endl;
  return true;
}

bool BasicRewriteRCons::ensureProofMacroReInterUnionInclusion(
    CDProof* cdp, const Node& lhs, std::vector<Node>& subgoals)
{
  return false;
}

}  // namespace rewriter
}  // namespace cvc5::internal
