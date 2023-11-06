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

bool CDTNodeTrie::add(CDTNodeTrieAllocator* al,
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
      Assert(it->second < cur->d_repChildren.size());
      cur = cur->d_repChildren[it->second];
      Assert(cur->d_data.get() == a);
    }
  }
  // set data, which will return false if we already have data
  return cur->setData(al, t);
}

bool CDTNodeTrie::setData(CDTNodeTrieAllocator* al, TNode t)
{
  if (d_data.get().isNull())
  {
    // just set the data, without constructing child
    d_data = t;
    return true;
  }
  al->markCongruent(t);
  return false;
}

CDTNodeTrie* CDTNodeTrie::push_back(CDTNodeTrieAllocator* al, TNode r)
{
  // TODO: optimization, can fill in empty child that was disabled?
  // this would require being more careful since its internal data would be
  // stale
  CDTNodeTrie* ret;
  if (d_repSize < d_repChildren.size())
  {
    ret = d_repChildren[d_repSize];
    Assert(ret != nullptr);
    ret->clear();
  }
  else
  {
    ret = al->alloc();
    d_repChildren.push_back(ret);
  }
  Assert(ret != nullptr);
  Assert(d_repChildren[d_repSize] == ret);
  ret->d_data = r;
  d_repMap[r] = d_repSize;
  d_repSize = d_repSize + 1;
  return ret;
}

CDTNodeTrieAllocator::CDTNodeTrieAllocator(context::Context* c) : d_ctx(c), d_congruent(c) {}

CDTNodeTrie* CDTNodeTrieAllocator::alloc()
{
  d_alloc.emplace_back(std::shared_ptr<CDTNodeTrie>(new CDTNodeTrie(d_ctx)));
  return d_alloc.back().get();
}

CDTNodeTrieIterator::CDTNodeTrieIterator(CDTNodeTrieAllocator* a,
                                         QuantifiersState& qs,
                                         CDTNodeTrie* cdtnt,
                                         size_t depth)
    : d_alloc(a), d_qs(qs), d_depth(depth)
{
  pushInternal(cdtnt);
}

TNode CDTNodeTrieIterator::pushNextChild()
{
  Assert(!d_stack.empty());
  CDTNodeTrie* next;
  TNode ret;
  do
  {
    StackFrame& sf = d_stack.back();
    // shouldn't mix pushNextChild and push
    Assert (sf.d_pushed.empty());
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
  } while (ret.isNull());
  return ret;
}

bool CDTNodeTrieIterator::push(TNode r)
{
  Assert(!d_stack.empty());
  StackFrame& sf = d_stack.back();
  // can't push the same child more than once
  if (sf.d_pushed.find(r)!=sf.d_pushed.end())
  {
    return false;
  }
  sf.d_pushed.insert(r);
  std::map<TNode, CDTNodeTrie*>::iterator it = sf.d_curChildren.find(r);
  if (it == sf.d_curChildren.end())
  {
    return false;
  }
  return pushInternal(it->second);
}

bool CDTNodeTrieIterator::pushInternal(CDTNodeTrie* cdtnt)
{
  bool isChildLeaf = (d_stack.size()+1==d_depth);
  d_stack.emplace_back(d_alloc, d_qs, cdtnt, isChildLeaf);
  // if not at leaf, and already finished (no children), we are done
  if (!isChildLeaf && d_stack.back().isFinished())
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
  Assert(d_stack.size() == d_depth);
  Assert(d_stack.back().d_active->hasData());
  return d_stack.back().d_active->getData();
}

CDTNodeTrieIterator::StackFrame::StackFrame(CDTNodeTrieAllocator* al,
                                            QuantifiersState& qs,
                                            CDTNodeTrie* active,
                                            bool isChildLeaf)
{
  d_active = active;
  std::map<TNode, CDTNodeTrie*>::iterator it;
  // process and merge the children
  CDTNodeTrie* cur;
  std::vector<CDTNodeTrie*> process;
  process.emplace_back(active);
  CDTNodeTrie* ccTgt;
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
          continue;
        }
        else
        {
          // must add to active
          // note this could be made easier by a level of indirection,
          // i.e. have ccn point to cc directly
          ccTgt = active->push_back(al, r);
          d_curChildren[r] = ccTgt;
        }
      }
      else
      {
        // mark that it will need to be merged
        ccTgt = it->second;
      }
      // now, perform the merge cc to ccTgt.
      if (isChildLeaf)
      {
        // if we are at leaf, set the data
        Assert (!cc->d_data.get().isNull());
        ccTgt->setData(al, cc->d_data.get());
      }
      else
      {
        // if we are not at the leaf, add to merge vector
        ccTgt->d_toMerge.push_back(cc);
        // mark that cc's data should no longer be considered
        cc->d_data = TNode::null();
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
