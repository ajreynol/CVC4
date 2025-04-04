/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
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

#include "theory/quantifiers/conflict_conjecture_generator.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/term_pools.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

ConflictConjectureGenerator::ConflictConjectureGenerator(Env& env,
                                   QuantifiersState& qs,
                                   QuantifiersInferenceManager& qim,
                                   QuantifiersRegistry& qr,
                                   TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

void ConflictConjectureGenerator::presolve() {}

bool ConflictConjectureGenerator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void ConflictConjectureGenerator::reset_round(Theory::Effort e) {}

void ConflictConjectureGenerator::registerQuantifier(Node q)
{
}

void ConflictConjectureGenerator::checkOwnership(Node q)
{
}

void ConflictConjectureGenerator::check(Theory::Effort e, QEffort quant_e)
{
}

std::string ConflictConjectureGenerator::identify() const { return "conflict-conjecture-gen"; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
