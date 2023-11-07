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
 * Quantifiers statistics class.
 */

#include "theory/quantifiers/eager/stats.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

Stats::Stats(StatisticsRegistry& sr)
    : d_ntriggers(sr.registerInt("quantifiers::eager::num_triggers")),
    d_ntriggersUnique(sr.registerInt("quantifiers::eager::num_triggers_unique")),
    d_nquant(sr.registerInt("quantifiers::eager::num_quant")),
    d_nquantNoTrigger(sr.registerInt("quantifiers::eager::num_quant_no_trigger"))
{
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
