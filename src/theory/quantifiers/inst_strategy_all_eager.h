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
 * All eager quantifier instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_ALL_EAGER_H
#define CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_ALL_EAGER_H

#include <map>
#include <unordered_map>

#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * InstStrategyAllEager
 *
 * This instantiation strategy double checks the eager term database to
 * add all instantiations it can find.
 */
class InstStrategyAllEager : public QuantifiersModule
{
 public:
  InstStrategyAllEager(Env& env,
                       QuantifiersState& qs,
                       QuantifiersInferenceManager& qim,
                       QuantifiersRegistry& qr,
                       TermRegistry& tr);
  ~InstStrategyAllEager() {}
  /** reset round */
  void reset_round(Theory::Effort e) override;
  /** needs check */
  bool needsCheck(Theory::Effort e) override;
  /** check */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** identify */
  std::string identify() const override { return "InstStrategyAllEager"; }

 private:
  /** Pointer to the term database eager class */
  TermDbEager* d_tde;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__INST_STRATEGY_ALL_EAGER_H */
