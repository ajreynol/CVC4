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
 * Diamonds proof generator utility.
 */

#include "theory/uf/diamonds_proof_generator.h"

#include "proof/proof.h"

namespace cvc5::internal {

DiamondsProofGenerator::DiamondsProofGenerator(Env& env) : EnvObj(env) {}

DiamondsProofGenerator::~DiamondsProofGenerator() {}

std::shared_ptr<ProofNode> DiamondsProofGenerator::getProofFor(Node fact)
{
  Trace("valid-witness") << "Prove " << fact << std::endl;
  // proofs not yet supported
  CDProof cdp(d_env);
  cdp.addTrustedStep(fact, TrustId::DIAMONDS, {}, {});
  return cdp.getProofFor(fact);
}

std::string DiamondsProofGenerator::identify() const
{
  return "DiamondsProofGenerator";
}

}  // namespace cvc5::internal
