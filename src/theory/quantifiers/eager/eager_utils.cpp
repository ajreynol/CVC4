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

void EagerWatchList::add(const EagerTrie* et, TNode t)
{
  d_matchJobs.push_back(std::pair<const EagerTrie*, TNode>(et, t));
}

void EagerWatchList::addMatchJobs(EagerWatchList* ewl)
{
  context::CDList<std::pair<const EagerTrie*, TNode>>& wmj = ewl->d_matchJobs;
  for (const std::pair<const EagerTrie*, TNode>& p : wmj)
  {
    d_matchJobs.push_back(p);
  }
}

EagerWatchList* EagerRepInfo::getOrMkListForRep(const Node& r, bool doMk)
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
      d_active(c, d_gtrie == nullptr),  // initially active if not indexing
      d_etrie(c)
{
  if (gdb != nullptr)
  {
    d_galloc = gdb->getAlloc();
    d_gtrie = gdb->getTrie(op);
  }
}

bool EagerOpInfo::addGroundTerm(QuantifiersState& qs, const Node& n)
{
  if (d_active.get())
  {
    // index now
    return addGroundTermInternal(qs, n);
  }
  d_rlvTermsWaiting.insert(n);
  return false;
}

const context::CDHashSet<Node>& EagerOpInfo::getGroundTerms(
    QuantifiersState& qs)
{
  if (!d_active.get())
  {
    // go back and index now
    for (const Node& nw : d_rlvTermsWaiting)
    {
      addGroundTermInternal(qs, nw);
    }
    d_active = true;
  }
  return d_rlvTerms;
}

bool EagerOpInfo::addGroundTermInternal(QuantifiersState& qs, const Node& n)
{
  if (d_gtrie == nullptr)
  {
    d_rlvTerms.insert(n);
    return true;
  }
  std::vector<TNode> args;
  for (const Node& nc : n)
  {
    // the operator of terms matters currently
    if (nc.getNumChildren() == 0)
    {
      args.emplace_back(qs.getRepresentative(nc));
    }
    else
    {
      args.emplace_back(nc);
    }
  }
  return d_gtrie->add(qs, d_galloc, args, n);
}

void EagerOpInfo::markWatchOp() {}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
