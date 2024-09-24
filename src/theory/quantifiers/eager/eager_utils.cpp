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
 * Eager instantiation.
 */

#include "theory/quantifiers/eager/eager_utils.h"

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_util.h"

// #define MULTI_TRIGGER_NEW

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void EagerWatchList::add(const EagerTrie* et, const std::vector<Node>& t)
{
  d_matchJobs.push_back(std::pair<const EagerTrie*, std::vector<Node>>(et, t));
}

EagerWatchList* EagerWatchInfo::getOrMkList(const Node& r, bool doMk)
{
  context::CDHashMap<Node, std::shared_ptr<EagerWatchList>>::iterator it =
      d_eqWatch.find(r);
  if (it != d_eqWatch.end())
  {
    return it->second.get();
  }
  else if (!doMk)
  {
    return nullptr;
  }
  std::shared_ptr<EagerWatchList> eoi = std::make_shared<EagerWatchList>(d_ctx);
  d_eqWatch.insert(r, eoi);
  return eoi.get();
}

EagerOpInfo::EagerOpInfo(context::Context* c,
                         const Node& op,
                         EagerGroundDb* gdb)
    : d_galloc(nullptr),
      d_gtrie(nullptr),
      d_rlvTerms(c),
      d_rlvTermsWaiting(c),
      d_active(c, false),
      d_ewl(c)
{
  if (gdb != nullptr)
  {
    d_galloc = gdb->getAlloc();
    d_gtrie = gdb->getTrie(op);
  }
}

bool EagerOpInfo::addGroundTerm(QuantifiersState& qs, const Node& n)
{
  if (d_gtrie == nullptr)
  {
    d_rlvTerms.insert(n);
    return true;
  }
  if (!d_active.get())
  {
    // index now
    return addGroundTermInternal(qs, n);
  }
  d_rlvTermsWaiting.insert(n);
  return false;
}

bool EagerOpInfo::addGroundTermInternal(QuantifiersState& qs, const Node& n)
{
  Assert(d_gtrie != nullptr);
  if (d_gtrie->add(qs, d_galloc, n))
  {
    d_rlvTerms.insert(n);
    return true;
  }
  return false;
}

void EagerOpInfo::setActive(QuantifiersState& qs)
{
  Assert(!d_active.get());
  for (const Node& nw : d_rlvTermsWaiting)
  {
    addGroundTerm(qs, nw);
  }
}

bool EagerOpInfo::isRelevant(QuantifiersState& qs,
                             const std::vector<TNode>& args) const
{
  Assert(d_gtrie != nullptr);
  return d_gtrie->contains(qs, args);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
