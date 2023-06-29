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
 * Proof rewriter
 */

#include "cvc5_private.h"

#ifndef CVC5__PROOF__PROOF_REWRITER_H
#define CVC5__PROOF__PROOF_REWRITER_H

#include <map>
#include <memory>

#include "expr/node.h"
#include "proof/proof_node.h"
#include "proof/proof_node_manager.h"

namespace cvc5::internal {

/**
 * A virtual callback class for updating ProofNode. An example use case of this
 * class is to eliminate a proof rule by expansion.
 */
class ProofRewriter
{
 public:
  ProofRewriter(ProofNodeManager* pnm);
  void rewrite(std::shared_ptr<ProofNode> pn);
 private:
   ProofNodeManager * d_pnm;
};

}  // namespace cvc5::internal

#endif
