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
    : d_ntriggers(sr.registerInt("quantifiers::eager::triggers")),
      d_ntriggersUnique(sr.registerInt("quantifiers::eager::triggers_unique")),
      d_ntriggersActivated(
          sr.registerInt("quantifiers::eager::triggers_activated")),
      d_nquant(sr.registerInt("quantifiers::eager::quant")),
      d_nquantNoTrigger(sr.registerInt("quantifiers::eager::quant_no_trigger")),
      d_nquantMultiTrigger(sr.registerInt("quantifiers::eager::quant_multi_trigger")),
      d_nquantActivated(sr.registerInt("quantifiers::eager::quant_activated")),
      d_nterms(sr.registerInt("quantifiers::eager::terms")),
      d_ntermsMatched(sr.registerInt("quantifiers::eager::terms_matched")),
      d_ntermsAdded(sr.registerInt("quantifiers::eager::fterms_added")),
      d_ntermsAddedCongruent(
          sr.registerInt("quantifiers::eager::fterms_added_congruent")),
      d_matches(sr.registerInt("quantifiers::eager::matches")),
      d_matchesAll(sr.registerInt("quantifiers::eager::match_alls")),
      d_matchesSuccess(sr.registerInt("quantifiers::eager::matches_success")),
      d_matchesSuccessConflict(
          sr.registerInt("quantifiers::eager::matches_success_conflict")),
      d_inst(sr.registerInt("quantifiers::eager::inst")),
      d_instSuccess(sr.registerInt("quantifiers::eager::inst_success"))
{
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
