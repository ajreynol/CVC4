/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A utility for converting proof nodes.
 */

#include "proof/unrewrite_proof_converter.h"

namespace cvc5::internal {

UnrewriteConverterCallback::UnrewriteConverterCallback(Env& env) : EnvObj(env), d_nconv(nodeManager()) {}

Node UnrewriteConverterCallback::convert(Node res,
              ProofRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp)
{
  
}


}  // namespace cvc5::internal

