/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict-based conjecture generation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CONFLICT_CONJECTURE_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__CONFLICT_CONJECTURE_GENERATOR_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 */
class ConflictConjectureGenerator : public QuantifiersModule
{
 public:
  ConflictConjectureGenerator(Env& env,
                   QuantifiersState& qs,
                   QuantifiersInferenceManager& qim,
                   QuantifiersRegistry& qr,
                   TermRegistry& tr);
  ~ConflictConjectureGenerator() {}
  /** Presolve */
  void presolve() override;
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  /** Reset round. */
  void reset_round(Theory::Effort e) override;
  /** Register quantified formula q */
  void registerQuantifier(Node q) override;
  /** Check ownership for q */
  void checkOwnership(Node q) override;
  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Identify. */
  std::string identify() const override;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
