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
 * A generic utility for infer proofs for arithmetic lemmas.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__ARITH__ARITH_PROOF_RCONS_H
#define CVC5__THEORY__ARITH__ARITH_PROOF_RCONS_H

#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "proof/trust_id.h"
#include "smt/env_obj.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace arith {

/**
 * Proof generator implementing the "diamonds" preprocessing step, performed
 * by TheoryUF.
 */
class ArithProofRCons : protected EnvObj, public ProofGenerator
{
 public:
  /**
   * @param env Reference to the environment
   * @param id The trust id to use if the proof reconstruction fails.
   */
  ArithProofRCons(Env& env, TrustId id);
  virtual ~ArithProofRCons();
  /**
   * Get proof for an arithmetic lemma
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;
private:
  /** The trust id to use if the proof reconstruction fails. */
  TrustId d_id;
  /** False node */
  Node d_false;
};

}
}
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__ARITH__ARITH_PROOF_RCONS_H */
