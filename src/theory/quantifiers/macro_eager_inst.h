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
 * Eager instantiation based on macros.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__MACRO_EAGER_INST_H
#define CVC5__THEORY__QUANTIFIERS__MACRO_EAGER_INST_H

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/quantifiers/quantifiers_macros.h"
#include "theory/substitutions.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 */
class MacroEagerInst : public QuantifiersModule
{
 public:
  MacroEagerInst(Env& env,
                 QuantifiersState& qs,
                 QuantifiersInferenceManager& qim,
                 QuantifiersRegistry& qr,
                 TermRegistry& tr);
  ~MacroEagerInst();
  /** Presolve */
  void presolve() override;
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  /** Reset round. */
  void reset_round(Theory::Effort e) override;
  /** Register quantified formula q */
  void registerQuantifier(Node q) override;
  /** Assert node. */
  void assertNode(Node q) override;
  /** Check ownership for q */
  void checkOwnership(Node q) override;
  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Identify. */
  std::string identify() const override;

 private:
   QuantifiersMacros d_qm;
   SubstitutionMap d_smap;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
