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

#include "proof/proof.h"
#include "proof/proof_checker.h"
#include "proof/proof_node_algorithm.h"
#include "proof/proof_node_manager.h"
#include "smt/env.h"

namespace cvc5::internal {

UnrewriteConverterCallback::UnrewriteConverterCallback(Env& env) : EnvObj(env) {}

Node UnrewriteConverterCallback::convert(Node res,
              ProofRule id,
              const std::vector<Node>& children,
              const std::vector<Node>& args,
              CDProof* cdp)
{
  
}


bool UnrewriteConverterCallback::tryWith(ProofRule id,
                                         const std::vector<Node>& children,
                                         const std::vector<Node>& args,
                                         Node expected,
                                         Node& newRes,
                                         CDProof* cdp)
{
  newRes = d_pc->checkDebug(id, children, args);
  if (!newRes.isNull())
  {
    // check if the new result matches the result
    if (expected == newRes)
    {
      cdp->addStep(newRes, id, children, args);
      return true;
    }
  }
  return false;
}
}  // namespace cvc5::internal

