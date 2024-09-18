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

EagerGroundTrie::EagerGroundTrie(context::Context* c) : d_cmap(c), d_csize(c, 0)
{
}

bool EagerGroundTrie::add(QuantifiersState& qs,
                          EagerGroundTrieAllocator* al,
                          TNode t)
{
  std::vector<TNode> args;
  for (const Node& tc : t)
  {
    args.emplace_back(qs.getRepresentative(tc));
  }
  return add(al, args, t);
}

bool EagerGroundTrie::isCongruent(QuantifiersState& qs, TNode t) const
{
  return isCongruentInternal(qs, t, 0);
}

bool EagerGroundTrie::contains(QuantifiersState& qs, const std::vector<TNode>& args) const
{
  return containsInternal(qs, args, 0);
}

bool EagerGroundTrie::isCongruentInternal(QuantifiersState& qs,
                                          TNode t,
                                          size_t i) const
{
  if (i==t.getNumChildren())
  {
    return true;
  }
  const Node& tc = t[i];
  context::CDHashMap<TNode, size_t>::const_iterator it = d_cmap.find(tc);
  if (d_cmap.find(tc) != d_cmap.end())
  {
    if (d_children[it->second]->isCongruentInternal(qs, t, i + 1))
    {
      return true;
    }
  }
  TNode r = qs.getRepresentative(tc);
  for (it = d_cmap.begin(); it != d_cmap.end(); ++it)
  {
    if (it->first != tc && qs.getRepresentative(it->first) == r)
    {
      if (d_children[it->second]->isCongruentInternal(qs, t, i + 1))
      {
        return true;
      }
    }
  }
  return false;
}

bool EagerGroundTrie::containsInternal(QuantifiersState& qs, const std::vector<TNode>& args, size_t i) const
{
  if (i==args.size())
  {
    return true;
  }
  const Node& tc = args[i];
  context::CDHashMap<TNode, size_t>::const_iterator it = d_cmap.find(tc);
  if (d_cmap.find(tc) != d_cmap.end())
  {
    if (d_children[it->second]->containsInternal(qs, args, i + 1))
    {
      return true;
    }
  }
  TNode r = qs.getRepresentative(tc);
  for (it = d_cmap.begin(); it != d_cmap.end(); ++it)
  {
    if (it->first != tc && qs.getRepresentative(it->first) == r)
    {
      if (d_children[it->second]->containsInternal(qs, args, i + 1))
      {
        return true;
      }
    }
  }
  return false;
}

bool EagerGroundTrie::add(EagerGroundTrieAllocator* al,
                          const std::vector<TNode>& args,
                          TNode t)
{
  EagerGroundTrie* cur = this;
  context::CDHashMap<TNode, size_t>::const_iterator it;
  for (TNode a : args)
  {
    it = cur->d_cmap.find(a);
    if (it == cur->d_cmap.end())
    {
      cur = cur->push_back(al, a);
    }
    else
    {
      Assert(it->second < cur->d_children.size());
      cur = cur->d_children[it->second];
    }
  }
  // set data, which will return false if we already have data
  return cur->setData(al, t);
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
  d_cmap[r] = d_csize;
  d_csize = d_csize + 1;
  return ret;
}

bool EagerGroundTrie::setData(EagerGroundTrieAllocator* al, TNode t)
{
  // data is stored as an element in the domain of d_repMap
  if (d_cmap.empty())
  {
    // just set the data, without constructing child
    d_cmap[t] = 0;
    return true;
  }
  // otherwise, t is congruent
  al->markCongruent(t);
  return false;
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
bool EagerGroundDb::add(const Node& n)
{
  Node op = d_tdb->getMatchOperator(n);
  if (op.isNull())
  {
    return false;
  }
  EagerGroundTrie* t = getTrie(op);
  std::vector<TNode> args;
  for (const Node& nc : n)
  {
    args.emplace_back(d_qstate.getRepresentative(nc));
  }
  return t->add(&d_alloc, args, n);
}
*/

EagerGroundTrie* EagerGroundDb::getTrie(const Node& op)
{
  std::map<Node, EagerGroundTrie*>::iterator it = d_db.find(op);
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
