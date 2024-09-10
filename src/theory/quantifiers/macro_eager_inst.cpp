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

#include "theory/quantifiers/macro_eager_inst.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

MacroEagerInst::MacroEagerInst(Env& env,
                               QuantifiersState& qs,
                               QuantifiersInferenceManager& qim,
                               QuantifiersRegistry& qr,
                               TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}
MacroEagerInst::~MacroEagerInst() {}
void MacroEagerInst::presolve() {}
bool MacroEagerInst::needsCheck(Theory::Effort e) { return false; }
void MacroEagerInst::reset_round(Theory::Effort e) {}
void MacroEagerInst::registerQuantifier(Node q) {}
void MacroEagerInst::checkOwnership(Node q) {}
void MacroEagerInst::check(Theory::Effort e, QEffort quant_e) {}
std::string MacroEagerInst::identify() const { return "MacroEagerInst"; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
