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
 * Eager term index
 */

#include "theory/quantifiers/eager/cd_tnode_trie.h"

#include "theory/quantifiers/quantifiers_state.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

CDTNodeTrie::CDTNodeTrie(context::Context* c)
    : d_data(c),
      d_repMap(c),
      d_repSize(c, 0),
      d_toMerge(c),
      d_toMergeProcessed(c, 0)
{
}

void CDTNodeTrie::clear()
{
  d_data = TNode::null();
  d_repSize = 0;
  d_toMergeProcessed = d_toMerge.size();
}

void CDTNodeTrie::add(CDTNodeTrieAllocator* al,
                      const std::vector<TNode>& args,
                      TNode t)
{
  CDTNodeTrie* cur = this;
  context::CDHashMap<TNode, size_t>::const_iterator it;
  for (TNode a : args)
  {
    it = cur->d_repMap.find(a);
    if (it == cur->d_repMap.end())
    {
      cur = cur->push_back(al, a);
    }
    else
    {
      cur = cur->d_repChildren[it->second];
    }
  }
  if (!cur->hasData())
  {
    // just set the data, without constructing child
    cur->d_data = t;
  }
}

CDTNodeTrie* CDTNodeTrie::push_back(CDTNodeTrieAllocator* al, TNode r)
{
  // TODO: optimization, can fill in empty child that was disabled?
  CDTNodeTrie* ret;
  if (d_repSize < d_repChildren.size())
  {
    ret = d_repChildren[d_repSize];
    ret->clear();
  }
  else
  {
    ret = al->alloc();
    d_repChildren.push_back(ret);
  }
  Assert(d_repChildren[d_repSize] == ret);
  ret->d_data = r;
  d_repMap[r] = d_repSize;
  d_repSize = d_repSize + 1;
  return ret;
}

CDTNodeTrieAllocator::CDTNodeTrieAllocator(context::Context* c)
    : d_ctx(c), d_alloc(c)
{
}

CDTNodeTrie* CDTNodeTrieAllocator::alloc()
{
  d_alloc.push_back(std::shared_ptr<CDTNodeTrie>(new CDTNodeTrie(d_ctx)));
  return d_alloc.back().get();
}

CDTNodeTrieIterator::CDTNodeTrieIterator(CDTNodeTrieAllocator* a,
                                         QuantifiersState& qs,
                                         CDTNodeTrie* cdtnt)
    : d_alloc(a), d_qs(qs)
{
  d_stack.emplace_back(d_alloc, qs, cdtnt);
}

TNode CDTNodeTrieIterator::pushNextChild()
{
  Assert(!d_stack.empty());
  CDTNodeTrie* next;
  TNode ret;
  do
  {
    StackFrame& sf = d_stack.back();
    if (sf.isFinished())
    {
      return d_null;
    }
    ret = sf.d_cit->first;
    next = sf.d_cit->second;
    ++sf.d_cit;
    if (!pushInternal(next))
    {
      ret = d_null;
    }
  }
  while (ret.isNull());
  return ret;
}

bool CDTNodeTrieIterator::push(TNode r)
{
  Assert(!d_stack.empty());
  StackFrame& sf = d_stack.back();
  std::map<TNode, CDTNodeTrie*>::iterator it = sf.d_curChildren.find(r);
  if (it == sf.d_curChildren.end())
  {
    return false;
  }
  return pushInternal(it->second);
}

bool CDTNodeTrieIterator::pushInternal(CDTNodeTrie* cdtnt)
{
  d_stack.emplace_back(d_alloc, d_qs, cdtnt);
  // if already finished (no children), we are done
  if (d_stack.back().isFinished())
  {
    d_stack.pop_back();
    return false;
  }
  return true;
}

void CDTNodeTrieIterator::pop()
{
  Assert(!d_stack.empty());
  d_stack.pop_back();
}

TNode CDTNodeTrieIterator::getData()
{
  Assert(!d_stack.empty());
  Assert(d_active != nullptr);
  Assert(d_active->hasData());
  return d_stack.back().d_active->getData();
}

CDTNodeTrieIterator::StackFrame::StackFrame(CDTNodeTrieAllocator* al,
                                            QuantifiersState& qs,
                                            CDTNodeTrie* active)
{
  d_active = active;
  std::map<TNode, CDTNodeTrie*>::iterator it;
  // process and merge the children
  CDTNodeTrie* cur;
  std::vector<CDTNodeTrie*> process;
  process.emplace_back(active);
  do
  {
    cur = process.back();
    process.pop_back();
    for (size_t i = 0, nreps = cur->d_repSize; i < nreps; i++)
    {
      CDTNodeTrie* cc = cur->d_repChildren[i];
      TNode n = cc->d_data;
      if (n.isNull())
      {
        // already merged
        continue;
      }
      TNode r = qs.getRepresentative(n);
      it = d_curChildren.find(r);
      // if we have yet to see this representative
      if (it == d_curChildren.end())
      {
        if (cur == active)
        {
          // if the original, we are done
          d_curChildren[r] = cc;
          if (n != r)
          {
            // keep the same but need to replace the representative, note that
            // n is stale and not cleaned up
            cc->d_data = r;
            cc->d_repMap[r] = i;
          }
        }
        else
        {
          // must add to active
          CDTNodeTrie* ccn = active->push_back(al, r);
          ccn->d_toMerge.push_back(cc);
          d_curChildren[r] = ccn;
        }
        i++;
      }
      else
      {
        // mark that it will need to be merged
        it->second->d_toMerge.push_back(cc);
        if (cur == active)
        {
          // if we are active, we must mark this as disabled
          cc->d_data = TNode::null();
        }
      }
    }
    // process those waiting to merge with this
    size_t ntomerge = cur->d_toMerge.size();
    size_t i = cur->d_toMergeProcessed.get();
    if (i < ntomerge)
    {
      do
      {
        process.emplace_back(cur->d_toMerge[i]);
        i++;
      } while (i < ntomerge);
      // mark we've processed all
      cur->d_toMergeProcessed = ntomerge;
    }
  } while (!process.empty());

  d_cit = d_curChildren.begin();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
