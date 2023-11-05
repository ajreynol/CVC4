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
 * Quantifier info for eager instantiation
 */

#include "theory/quantifiers/eager/trigger_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

TriggerInfo::TriggerInfo(context::Context* c) {}
/** Initialize */
void TriggerInfo::initialize(TermDbEager& tde, const Node& t) {}


void TriggerInfo::doMatching(TermDbEager& tde, TNode t)
{
}

void TriggerInfo::doMatchingEqc(TermDbEager& tde, TNode eqc)
{
}

void TriggerInfo::doMatchingAll(TermDbEager& tde)
{
}


}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
