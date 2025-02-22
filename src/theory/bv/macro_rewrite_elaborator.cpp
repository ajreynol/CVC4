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
 * Methods for elaborating MACRO_BV_* proof rewrites.
 */

#include "theory/bv/macro_rewrite_elaborator.h"

namespace cvc5::internal {
namespace theory {
namespace bv {

MacroRewriteElaborator::MacroRewriteElaborator(Env& env) : EnvObj(env){}
MacroRewriteElaborator::~MacroRewriteElaborator() {}
bool MacroRewriteElaborator::ensureProofFor(CDProof* cdp,
                                  ProofRewriteRule id,
                                  const Node& eq)
{
  switch (id)
  {
    case ProofRewriteRule::MACRO_BV_EXTRACT_CONCAT:
    case ProofRewriteRule::MACRO_BV_EXTRACT_SIGN_EXTEND:
    case ProofRewriteRule::MACRO_BV_ASHR_BY_CONST:
    case ProofRewriteRule::MACRO_BV_OR_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_AND_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_XOR_SIMPLIFY:
    case ProofRewriteRule::MACRO_BV_AND_OR_XOR_CONCAT_PULLUP:
    case ProofRewriteRule::MACRO_BV_MULT_SLT_MULT:
    case ProofRewriteRule::MACRO_BV_CONCAT_EXTRACT_MERGE:
    case ProofRewriteRule::MACRO_BV_CONCAT_CONSTANT_MERGE:
    case ProofRewriteRule::MACRO_BV_FLATTEN_ASSOC_COMMUT:
      break;
    default:
      break;
  }
  return false;
}

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal
