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
 * Eager instantiation trigger utilities.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_TRIGGER_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_TRIGGER_H

#include <cstdint>
#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/eager/eager_info.h"
#include "theory/quantifiers/eager/eager_term_database.h"

namespace cvc5::internal {

class Env;

namespace theory {
namespace quantifiers {

class QuantifiersInferenceManager;
class QuantifiersRegistry;
class QuantifiersState;
class TermDb;
class TermRegistry;

namespace eager {

/** Get simple pattern info for pat, returns false if unsupported. */
bool getPatternInfo(TermDb& tdb, Node q, Node pat, PatternInfo& pinfo);

/** Add instantiations for trigger ti of quantified formula q. */
void addInstantiations(Env& env,
                       QuantifiersState& qstate,
                       QuantifiersInferenceManager& qim,
                       TermRegistry& treg,
                       TermDb& tdb,
                       const TermDatabase& termDb,
                       Node q,
                       const TriggerInfo& ti,
                       uint64_t& addedLemmas,
                       std::vector<Node>& addedInstantiations);

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
