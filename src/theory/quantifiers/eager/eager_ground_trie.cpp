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

#include "theory/quantifiers/eager/eager_ground_trie.h"

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EagerGroundTrie::EagerGroundTrie(context::Context* c)
    : d_cmap(c), d_csize(c, 0), d_active(c, false)
{
}

bool EagerGroundTrie::add(QuantifiersState& qs,
                          EagerGroundTrieAllocator* al,
                          TNode t)
{
  std::vector<TNode> args(t.begin(), t.end());
  return add(qs, al, args, t, args.size());
}

bool EagerGroundTrie::add(QuantifiersState& qs,
                          EagerGroundTrieAllocator* al,
                          const std::vector<TNode>& args,
                          TNode t,
                          size_t nargs)
{
  EagerGroundTrie* cur = this;
  context::CDHashMap<Node, EagerGroundTrie*>::const_iterator it;
  if (nargs == 0)
  {
    nargs = args.size();
  }
  Assert (nargs<=args.size());
  for (size_t i = 0; i < nargs; i++)
  {
    TNode a = args[i];
    it = cur->d_cmap.find(a);
    if (it == cur->d_cmap.end())
    {
      cur = cur->push_back(al, a);
    }
    else
    {
      cur = it->second;
    }
  }
  // set data, which will return false if we already have data
  return cur->setData(al, t);
}

const EagerGroundTrie* EagerGroundTrie::contains(QuantifiersState& qs,
                                                 const std::vector<TNode>& args,
                                                 size_t nargs) const
{
  if (nargs == 0)
  {
    nargs = args.size();
  }
  return containsInternal(qs, args, 0, nargs);
}

const EagerGroundTrie* EagerGroundTrie::containsInternal(
    QuantifiersState& qs,
    const std::vector<TNode>& args,
    size_t i,
    size_t total) const
{
  if (i == total)
  {
    return this;
  }
  TNode tc = args[i];
  context::CDHashMap<Node, EagerGroundTrie*>::const_iterator it =
      d_cmap.find(tc);
  if (d_cmap.find(tc) != d_cmap.end())
  {
    const EagerGroundTrie* egt =
        it->second->containsInternal(qs, args, i + 1, total);
    if (egt != nullptr)
    {
      return egt;
    }
  }
  // if null, there is no containment
  if (tc.isNull())
  {
    return nullptr;
  }
  // NOTE: we assume no mixing of wildcards, e.g. null does not contain
  // specific classes.
  // check modulo equality
  TNode r = qs.getRepresentative(tc);
  for (it = d_cmap.begin(); it != d_cmap.end(); ++it)
  {
    if (it->first != tc && qs.getRepresentative(it->first) == r)
    {
      const EagerGroundTrie* egt =
          it->second->containsInternal(qs, args, i + 1, total);
      if (egt != nullptr)
      {
        return egt;
      }
    }
  }
  return nullptr;
}

EagerGroundTrie* EagerGroundTrie::push_back(EagerGroundTrieAllocator* al,
                                            TNode r)
{
  Assert(d_cmap.find(r) == d_cmap.end());
  EagerGroundTrie* ret;
  if (d_csize < d_children.size())
  {
    ret = d_children[d_csize];
    Assert(ret != nullptr);
  }
  else
  {
    ret = al->alloc();
    d_children.emplace_back(ret);
  }
  Assert(ret != nullptr);
  Assert(d_children[d_csize] == ret);
  d_cmap[r] = ret;
  d_csize = d_csize + 1;
  return ret;
}

bool EagerGroundTrie::setData(EagerGroundTrieAllocator* al, TNode t)
{
  // data is stored as an element in the domain of d_repMap
  if (d_cmap.empty())
  {
    // just set the data, without constructing child
    d_cmap[t] = nullptr;
    return true;
  }
  else if (d_cmap.begin()->first == t)
  {
    // if being readded, we also return true
    return true;
  }
  // otherwise, t is congruent
  al->markCongruent(t);
  return false;
}

void EagerGroundTrie::getChildren(QuantifiersState& qs,
                                  TNode r,
                                  std::vector<EagerGroundTrie*>& children)
{
  if (d_cmap.empty())
  {
    return;
  }
  else if (d_cmap.begin()->first.isNull())
  {
    Assert(d_cmap.size() == 1);
    children.emplace_back(d_cmap.begin()->second);
    return;
  }
  context::CDHashMap<Node, EagerGroundTrie*>::const_iterator it;
  for (it = d_cmap.begin(); it != d_cmap.end(); ++it)
  {
    Assert(!it->first.isNull());
    if (qs.getRepresentative(it->first) == r)
    {
      children.emplace_back(it->second);
    }
  }
}

EagerGroundTrieAllocator::EagerGroundTrieAllocator(context::Context* c)
    : d_ctx(c), d_congruent(c)
{
}

EagerGroundDb::EagerGroundDb(Env& env, QuantifiersState& qs, TermDb* tdb)
    : EnvObj(env), d_qstate(qs), d_tdb(tdb), d_alloc(context())
{
}

/*
bool EagerGroundDb::add(const TNode& n)
{
  TNode op = d_tdb->getMatchOperator(n);
  if (op.isNull())
  {
    return false;
  }
  EagerGroundTrie* t = getTrie(op);
  std::vector<TNode> args;
  for (const TNode& nc : n)
  {
    args.emplace_back(d_qstate.getRepresentative(nc));
  }
  return t->add(&d_alloc, args, n);
}
*/

EagerGroundTrie* EagerGroundDb::getTrie(const TNode& op)
{
  std::map<TNode, EagerGroundTrie*>::iterator it = d_db.find(op);
  if (it != d_db.end())
  {
    return it->second;
  }
  EagerGroundTrie* t = d_alloc.alloc();
  d_db[op] = t;
  return t;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
