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
namespace expr {
class TermCanonize;
}
namespace theory {
namespace quantifiers {

class TermDbEager;
class QuantifiersRegistry;

namespace eager {

class QuantInfo
{
 public:
  QuantInfo(TermDbEager& tde);
  /** Initialize this for quantified formula q */
  void initialize(QuantifiersRegistry& qr,
                  expr::TermCanonize& canon,
                  const Node& q);
  /** Set that the quantified formula for this class is asserted */
  bool notifyAsserted();
  /** Get quantified formula */
  Node getQuant() const { return d_quant; }
  /** Is the quantified formula asserted? */
  bool isAsserted() const { return d_asserted.get(); }
  /**
   * Notify that a trigger has been assigned a status, return true if conflict.
   */
  bool notifyTriggerStatus(TriggerInfo* tinfo, TriggerStatus status);
  /** Get the active trigger */
  TriggerInfo* getActiveTrigger();
  /** Get the status */
  TriggerStatus getStatus() const { return d_tstatus.get(); }

 private:
  bool updateStatus();
  bool watchAndActivateTrigger(size_t i);
  /** The quantified formula */
  Node d_quant;
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** List of triggers */
  std::vector<TriggerInfo*> d_triggers;
  /** Variable list per trigger */
  std::vector<std::vector<Node>> d_vlists;
  /** Have we indicated that we want to watch */
  std::vector<bool> d_triggerWatching;
  /** Is asserted */
  context::CDO<bool> d_asserted;
  /**
   * The index in d_triggers that is inactive if we are inactive,
   * or one that we are watching if we are active.
   */
  context::CDO<size_t> d_tindex;
  /** The current status */
  context::CDO<TriggerStatus> d_tstatus;
  /** Have we ever activated this? */
  bool d_hasActivated;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
