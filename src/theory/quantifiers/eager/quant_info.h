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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__QUANT_INFO_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__QUANT_INFO_H

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/eager/trigger_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbEager;
class QuantifiersRegistry;

namespace eager {

class QuantInfo
{
 public:
  QuantInfo(TermDbEager& tde);
  /** Initialize */
  void initialize(QuantifiersRegistry& qr, const Node& q);
  /** Set that we are asserted */
  void notifyAsserted();

 private:
  enum class TriggerStatus
  {
    INACTIVE,
    WAIT,
    ACTIVE
  };
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** List of triggers */
  std::vector<TriggerInfo*> d_triggers;
  /** Status of each trigger */
  context::CDHashMap<size_t, TriggerStatus> d_status;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
