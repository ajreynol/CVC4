/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Preprocess equality rewriter for arithmetic
 */

#include "theory/arith/pp_rewrite_eq.h"

#include "options/arith_options.h"
#include "smt/env.h"
#include "theory/builtin/proof_checker.h"
#include "theory/rewriter.h"
#include "theory/arith/arith_rewriter.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

PreprocessRewriteEq::PreprocessRewriteEq(Env& env)
    : EnvObj(env), d_ppPfGen(env, context(), "Arith::ppRewrite")
{
}

TrustNode PreprocessRewriteEq::ppRewriteEq(TNode atom)
{
  Assert(atom.getKind() == Kind::EQUAL);
  Assert(atom[0].getType().isRealOrInt());
  Trace("linear-solver") << "ppRewriteEq: " << atom << std::endl;
  // always rewrite now
  Node rewritten = ArithRewriter::rewriteEquality(atom);
  if (options().arith.arithRewriteEq)
  {
    Node leq = NodeBuilder(Kind::LEQ) << rewritten[0] << rewritten[1];
    Node geq = NodeBuilder(Kind::GEQ) << rewritten[0] << rewritten[1];
    rewritten = rewrite(leq.andNode(geq));
    Trace("arith::preprocess")
        << "arith::preprocess() : returning " << rewritten << std::endl;
    // don't need to rewrite terms since rewritten is not a non-standard op
    if (d_env.isTheoryProofProducing())
    {
      Node t = builtin::BuiltinProofRuleChecker::mkTheoryIdNode(THEORY_ARITH);
      Node eq = atom.eqNode(rewritten);
      return d_ppPfGen.mkTrustedRewrite(
          atom,
          rewritten,
          d_env.getProofNodeManager()->mkTrustedNode(
              TrustId::THEORY_INFERENCE, {}, {}, eq));
    }
  }
  else if (atom==rewritten)
  {
    return TrustNode::null();
  }
  return TrustNode::mkTrustRewrite(atom, rewritten, nullptr);
}

}  // namespace arith
}  // namespace theory
}  // namespace cvc5::internal
