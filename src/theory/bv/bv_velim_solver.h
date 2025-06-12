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
 * A solver based on variable elimination.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__BV__BV_VELIM_SOLVER_H
#define CVC5__THEORY__BV__BV_VELIM_SOLVER_H

#include "context/cdhashmap.h"
#include "proof/proof_generator.h"
#include "proof/trust_node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {

namespace bv {

/**
 * A class for implementing TheoryBv::ppAssert along with its proof tracking.
 */
class BvVElimSolver : protected EnvObj, public ProofGenerator
{
 public:
  /** Constructor */
  BvVElimSolver(Env& env);
  ~BvVElimSolver();
  /**
   * @param asserts The input assertions
   * @return a trust node corresponding to a theory lemma if asserts are
   * determined to be unsat, or null otherwise if the satisfiability of
   * asserts is unknown.
   */
  TrustNode check(const std::vector<Node>& asserts);
  /**
   */
  std::shared_ptr<ProofNode> getProofFor(Node fact) override;
  /** identify */
  std::string identify() const override;
};

}  // namespace bv
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BV__BV_VELIM_SOLVER_H */
