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

#include "proof/conv_proof_generator.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "rewriter/rewrites.h"
#include "smt/env.h"
#include "theory/arith/arith_poly_norm.h"
#include "theory/arith/arith_proof_utilities.h"
#include "theory/booleans/theory_bool_rewriter.h"
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
  // clear the current subgoals
  d_subgoals.clear();
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
            cdp, eq, ProofRule::THEORY_REWRITE, {mkRewriteRuleNode(prid), eq}))
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
            cdp, eq, ProofRule::THEORY_REWRITE, {mkRewriteRuleNode(prid), eq}))
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
    // Theory rewrites may require the expansion below
    if (r == ProofRule::THEORY_REWRITE)
    {
      Assert(args.size() == 2);
      ProofRewriteRule id;
      if (rewriter::getRewriteRule(args[0], id))
      {
        ensureProofForTheoryRewrite(cdp, id, args[1]);
        return true;
      }
    }
    cdp->addStep(eq, r, {}, args);
    return true;
  }
  return false;
}

void BasicRewriteRCons::ensureProofForEncodeTransform(CDProof* cdp, const Node& eq, const Node& eqi)
{
  cdp->addStep(eq, ProofRule::ENCODE_PRED_TRANSFORM, {eqi}, {eq});
}
  
void BasicRewriteRCons::ensureProofForTheoryRewrite(CDProof* cdp,
                                                    ProofRewriteRule id,
                                                    const Node& eq)
{
  switch (id)
  {
    case ProofRewriteRule::MACRO_BOOL_NNF_NORM:
      if (ensureProofMacroBoolNnfNorm(cdp, eq))
      {
        return;
      }
      break;
    case ProofRewriteRule::MACRO_ARITH_STRING_PRED_ENTAIL:
      if (ensureProofMacroArithStringPredEntail(cdp, eq))
      {
        return;
      }
      break;
    default: break;
  }
  // default, just add the rewrite
  std::vector<Node> args;
  args.push_back(
      nodeManager()->mkConstInt(Rational(static_cast<uint32_t>(id))));
  args.push_back(eq);
  cdp->addStep(eq, ProofRule::THEORY_REWRITE, {}, args);
}

bool BasicRewriteRCons::ensureProofMacroBoolNnfNorm(CDProof* cdp,
                                                    const Node& eq)
{
  Trace("brc-macro") << "Expand Bool NNF norm " << eq[0] << " == " << eq[1]
                     << std::endl;
  // Call the utility again with proof tracking and construct the term
  // conversion proof. This proof itself may have trust steps in it.
  TConvProofGenerator tcpg(d_env, nullptr);
  Node nr = theory::booleans::TheoryBoolRewriter::computeNnfNorm(
      nodeManager(), eq[0], &tcpg);
  std::shared_ptr<ProofNode> pfn = tcpg.getProofFor(eq);
  Trace("brc-macro") << "...proof is " << *pfn.get() << std::endl;
  cdp->addProof(pfn);
  // the small steps are trust steps, record them here
  expr::getSubproofRule(pfn, ProofRule::TRUST, d_subgoals);
  return true;
}

bool BasicRewriteRCons::ensureProofMacroArithStringPredEntail(CDProof* cdp,
                                                              const Node& eq)
{
  Assert(eq.getKind() == Kind::EQUAL);
  Node lhs = eq[0];
  theory::strings::ArithEntail ae(nullptr);
  Node exp;
  Node ret = ae.rewritePredViaEntailment(lhs, exp, true);
  Assert(ret == eq[1]);
  Trace("brc-macro") << "Expand entailment for " << lhs << " == " << ret
                     << std::endl;
  Trace("brc-macro") << "- explanation is " << exp << std::endl;
  Node expRew = ae.rewriteArith(exp);
  Node zero = nodeManager()->mkConstInt(Rational(0));
  Node geq = nodeManager()->mkNode(Kind::GEQ, expRew, zero);
  Trace("brc-macro") << "- rewritten predicate is " << geq << std::endl;
  Node approx = ae.findApprox(expRew, true);
  if (approx.isNull())
  {
    Trace("brc-macro") << "...failed to find approximation" << std::endl;
    AlwaysAssert(false);
    return false;
  }
  Node truen = nodeManager()->mkConst(true);
  Node approxRew = ae.rewriteArith(approx);
  Node approxGeq = nodeManager()->mkNode(Kind::GEQ, approx, zero);
  Node approxRewGeq = nodeManager()->mkNode(Kind::GEQ, approxRew, zero);
  Trace("brc-macro") << "- approximation predicate is " << approxGeq
                     << std::endl;
  std::vector<Node> transEq;
  if (expRew != approx)
  {
    Node aeq = geq.eqNode(approxGeq);
    // (>= expRew 0) = (>= approx 0)
    Trace("brc-macro") << "- prove " << aeq << " via pred-safe-approx"
                       << std::endl;
    cdp->addTheoryRewriteStep(aeq,
                              ProofRewriteRule::ARITH_STRING_PRED_SAFE_APPROX);
    transEq.push_back(aeq);
  }
  if (approxRew != approx)
  {
    Node areq = approxGeq.eqNode(approxRewGeq);
    Trace("brc-macro") << "- prove " << areq << " via arith-poly-norm"
                       << std::endl;
    cdp->addStep(areq, ProofRule::ARITH_POLY_NORM, {}, {areq});
    transEq.push_back(areq);
  }
  // (>= approx 0) = true
  Node teq = approxRewGeq.eqNode(truen);
  // it might be trivial to show, use evaluate???
  Trace("brc-macro") << "- prove " << teq << " via pred-entail" << std::endl;
  cdp->addTheoryRewriteStep(teq, ProofRewriteRule::ARITH_STRING_PRED_ENTAIL);
  transEq.push_back(teq);
  // put the above three steps together with TRANS
  if (transEq.size() > 1)
  {
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
  Trace("brc-macro") << "...proof is " << *cdp->getProofFor(retEq) << std::endl;
  return true;
}

std::vector<std::shared_ptr<ProofNode>>& BasicRewriteRCons::getSubgoals()
{
  return d_subgoals;
}

}  // namespace rewriter
}  // namespace cvc5::internal
