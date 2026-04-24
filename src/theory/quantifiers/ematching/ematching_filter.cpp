/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A conservative filter for excluding quantified formulas from E-matching.
 */

#include "theory/quantifiers/ematching/ematching_filter.h"

#include <algorithm>

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EmatchingFilter::EmatchingFilter(Env& env,
                                 QuantifiersState& qs,
                                 QuantifiersInferenceManager& qim,
                                 QuantifiersRegistry& qr,
                                 TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_hasMasterEqEventSnapshot(false)
{
}

bool EmatchingFilter::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void EmatchingFilter::check(CVC5_UNUSED Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  updateMasterEqEvents();
}

void EmatchingFilter::registerQuantifier(Node q)
{
  d_excluded[q] = shouldExclude(q);
}

bool EmatchingFilter::exclude(Node q) const
{
  std::map<Node, bool>::const_iterator it = d_excluded.find(q);
  return it != d_excluded.end() && it->second;
}

std::string EmatchingFilter::identify() const { return "ematching-filter"; }

void EmatchingFilter::updateMasterEqEvents()
{
  std::vector<TermRegistry::MasterEqEvent> currentEvents;
  d_treg.getMasterEqEvents(currentEvents);
  const size_t previousSize = d_masterEqEventSnapshot.size();
  d_masterEqEventsRemoved.clear();
  d_masterEqEventsAdded.clear();
  if (d_hasMasterEqEventSnapshot)
  {
    size_t prefix = 0;
    size_t maxPrefix =
        std::min(d_masterEqEventSnapshot.size(), currentEvents.size());
    while (prefix < maxPrefix
           && d_masterEqEventSnapshot[prefix] == currentEvents[prefix])
    {
      ++prefix;
    }
    d_masterEqEventsRemoved.insert(d_masterEqEventsRemoved.end(),
                                   d_masterEqEventSnapshot.begin() + prefix,
                                   d_masterEqEventSnapshot.end());
    d_masterEqEventsAdded.insert(d_masterEqEventsAdded.end(),
                                 currentEvents.begin() + prefix,
                                 currentEvents.end());
  }
  d_masterEqEventSnapshot.swap(currentEvents);
  if (TraceIsOn("ematching-filter-events"))
  {
    traceMasterEqEventDiff(previousSize);
  }
  d_hasMasterEqEventSnapshot = true;
}

void EmatchingFilter::traceMasterEqEventDiff(size_t previousSize) const
{
  Trace("ematching-filter-events")
      << "Master equality engine events: previous=" << previousSize
      << ", current="
      << d_masterEqEventSnapshot.size();
  if (!d_hasMasterEqEventSnapshot)
  {
    Trace("ematching-filter-events") << " (initial snapshot)." << std::endl;
    return;
  }
  Trace("ematching-filter-events")
      << ", removed=" << d_masterEqEventsRemoved.size()
      << ", added=" << d_masterEqEventsAdded.size() << "." << std::endl;
  for (const TermRegistry::MasterEqEvent& event : d_masterEqEventsRemoved)
  {
    Trace("ematching-filter-events") << "  removed: " << event << std::endl;
  }
  for (const TermRegistry::MasterEqEvent& event : d_masterEqEventsAdded)
  {
    Trace("ematching-filter-events") << "  added: " << event << std::endl;
  }
}

bool EmatchingFilter::shouldExclude(CVC5_UNUSED Node q) const
{
  // Criteria will be added incrementally. Exclude nothing until then.
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
