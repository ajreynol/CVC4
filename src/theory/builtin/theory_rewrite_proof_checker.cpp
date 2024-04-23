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
 * Builtin proof checker utility for THEORY_REWRITE.
 */

#include "theory/builtin/theory_rewrite_proof_checker.h"

namespace cvc5::internal {
namespace theory {
namespace builtin {

TheoryRewriteProofChecker::TheoryRewriteProofChecker(NodeManager* nm) : d_nm(nm)
{
}

Node TheoryRewriteProofChecker::checkRewrite(ProofRewriteRule id,
                                             const Node& lhs)
{
  Trace("theory-rewrite-pc") << "Check " << id << " " << lhs << std::endl;
  Node ret = d_rew->rewriteViaRule(id, lhs);
  return ret;
}

}  // namespace builtin
}  // namespace theory
}  // namespace cvc5::internal
