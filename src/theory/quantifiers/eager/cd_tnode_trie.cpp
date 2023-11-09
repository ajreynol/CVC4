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
    : d_edge(c),
      d_repMap(c),
      d_repSize(c, 0),
      d_toMerge(c),
      d_toMergeProcessed(c, 0)
{
}

void CDTNodeTrie::clear()
{
  d_edge = TNode::null();
  d_repSize = 0;
  d_toMergeProcessed = d_toMerge.size();
}

bool CDTNodeTrie::add(CDTNodeTrieAllocator* al,
                      QuantifiersState& qs,
                      const std::vector<TNode>& args,
                      TNode t)
{
  size_t nargs = args.size();
  // push using the iterator
  CDTNodeTrieIterator itt(al, qs, this, nargs);
  for (size_t i = 0; i < nargs; i++)
  {
    if (!itt.push(args[i]))
    {
      // if we fail to push, we are a new sub-trie, add the rest directly
      CDTNodeTrie* cur = itt.getCurrent();
      for (size_t j = i; j < nargs; j++)
      {
        cur = cur->push_back(al, args[j]);
      }
      return cur->setData(al, t);
    }
  }
  return itt.setData(t);
}

bool CDTNodeTrie::addSimple(CDTNodeTrieAllocator* al,
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
      // NOTE: if using stale, we would confirm that the next has the right data
      cur = cur->push_back(al, a);
    }
    else
    {
      Assert(it->second < cur->d_repChildren.size());
      cur = cur->d_repChildren[it->second];
    }
    Assert(cur->d_edge.get() == a);
  }
  // set data, which will return false if we already have data
  return cur->setData(al, t);
}

bool CDTNodeTrie::setData(CDTNodeTrieAllocator* al, TNode t)
{
  // data is stored as an element in the domain of d_repMap
  if (d_repMap.empty())
  {
    // just set the data, without constructing child
    d_repMap[t] = 0;
    return true;
  }
  // otherwise, t is congruent
  al->markCongruent(t);
  return false;
}

CDTNodeTrie* CDTNodeTrie::push_back(CDTNodeTrieAllocator* al, TNode r)
{
  Assert(d_repMap.find(r) == d_repMap.end());
  // TODO: optimization, can fill in empty child that was disabled?
  // this would require being more careful since its internal data would be
  // stale
  CDTNodeTrie* ret;
  if (d_repSize < d_repChildren.size())
  {
    ret = d_repChildren[d_repSize];
    Assert(ret != nullptr);
    // NOTE clearing is not necessary currently
    ret->clear();
  }
  else
  {
    ret = al->alloc();
    d_repChildren.emplace_back(ret);
  }
  Assert(ret != nullptr);
  Assert(d_repChildren[d_repSize] == ret);
  ret->d_edge = r;
  d_repMap[r] = d_repSize;
  d_repSize = d_repSize + 1;
  return ret;
}

void CDTNodeTrie::addToMerge(CDTNodeTrieAllocator* al,
                             CDTNodeTrie* t,
                             bool isChildLeaf)
{
  if (isChildLeaf)
  {
    // if we are at leaf, set the data
    Assert(t->hasData());
    setData(al, t->getData());
  }
  else
  {
    // if we are not at the leaf, add to merge vector
    d_toMerge.push_back(t);
  }
  // mark that cc's should no longer be considered as a child
  t->d_edge = TNode::null();
}

CDTNodeTrieAllocator::CDTNodeTrieAllocator(context::Context* c)
    : d_ctx(c), d_congruent(c)
{
}

CDTNodeTrie* CDTNodeTrieAllocator::alloc()
{
  d_alloc.emplace_back(std::shared_ptr<CDTNodeTrie>(new CDTNodeTrie(d_ctx)));
  return d_alloc.back().get();
}

CDTNodeTrieIterator::CDTNodeTrieIterator(CDTNodeTrieAllocator* a,
                                         QuantifiersState& qs,
                                         CDTNodeTrie* cdtnt,
                                         size_t depth)
    : d_alloc(a), d_qs(qs), d_curData(nullptr), d_depth(depth)
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
    if (sf.isFinished())
    {
      // finished children at the current level
      return d_null;
    }
    Trace("ajr-temp") << "for index " << sf.d_index << " / " << sf.d_dom.size() << " | " << d_stack.size() << std::endl;
    ret = sf.d_dom[sf.d_index].first;
    Trace("ajr-temp") << "..return " << ret << std::endl;
    next = sf.d_dom[sf.d_index].second;
    Assert(next->d_edge.get() == ret);
    //++sf.d_cit;
    ++sf.d_index;
    if (!pushInternal(next))
    {
      // rare case where the current has no children?
      ret = d_null;
    }
  } while (ret.isNull());
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
  // if pushing to a leaf, set the data
  if (d_stack.size() == d_depth)
  {
    Assert(d_curData == nullptr);
    d_curData = cdtnt;
    return true;
  }
  // otherwise, compute the children
  // determine if the children are leafs, which impacts how we merge nodes
  bool isChildLeaf = (d_stack.size() + 1 == d_depth);
  d_stack.emplace_back(d_alloc, d_qs, cdtnt, isChildLeaf);
  /*
  // in the rare case we already finished (no children), we are done
  if (d_stack.back().isFinished())
  {
    d_stack.pop_back();
    return false;
  }
  */
  return true;
}

void CDTNodeTrieIterator::pop()
{
  // if at a leaf, undo the data
  if (d_curData != nullptr)
  {
    d_curData = nullptr;
    return;
  }
  // otherwise pop the stack
  Assert(!d_stack.empty());
  d_stack.pop_back();
}

TNode CDTNodeTrieIterator::getCurrentData()
{
  Assert(d_curData != nullptr);
  Assert(d_curData->hasData());
  return d_curData->getData();
}

CDTNodeTrie* CDTNodeTrieIterator::getCurrent()
{
  Assert(!d_stack.empty());
  if (d_curData != nullptr)
  {
    return d_curData;
  }
  return d_stack.back().d_active;
}

bool CDTNodeTrieIterator::setData(TNode n)
{
  Assert(d_curData != nullptr);
  return d_curData->setData(d_alloc, n);
}

CDTNodeTrieIterator::StackFrame::StackFrame(CDTNodeTrieAllocator* al,
                                            QuantifiersState& qs,
                                            CDTNodeTrie* active,
                                            bool isChildLeaf) : d_active(active), d_index(0)
{
  Assert(active != nullptr);
  std::map<TNode, CDTNodeTrie*>::iterator it;
  context::CDHashMap<TNode, size_t>::iterator itr;
  // process and merge the children
  CDTNodeTrie* cur;
  std::vector<CDTNodeTrie*> process;
  process.emplace_back(active);
  CDTNodeTrie* ccTgt;
  do
  {
    cur = process.back();
    process.pop_back();
    // process all children of the trie to process
    for (size_t i = 0, nreps = cur->d_repSize; i < nreps; i++)
    {
      CDTNodeTrie* cc = cur->d_repChildren[i];
      TNode n = cc->d_edge;
      if (n.isNull())
      {
        // child was already merged elsewhere
        continue;
      }
      TNode r = qs.getRepresentative(n);
      it = d_curChildren.find(r);
      // if we have yet to see this child edge
      if (it == d_curChildren.end())
      {
        if (cur == active)
        {
          // if the original, we are done
          if (n != r)
          {
            // maybe forward merge to another child
            itr = active->d_repMap.find(r);
            if (itr != active->d_repMap.end())
            {
              ccTgt = active->d_repChildren[itr->second];
              Assert(ccTgt->d_edge.get() == r);
              ccTgt->addToMerge(al, cc, isChildLeaf);
              // we will process the child later in the list
              continue;
            }
            // keep the same but need to replace the representative, note that
            // n is stale and not cleaned up
            cc->d_edge = r;
            cc->d_repMap[r] = i;
          }
          d_curChildren[r] = cc;
          d_dom.emplace_back(r, cc);
          Trace("cdt-debug") << "child " << r << std::endl;
          continue;
        }
        else
        {
          // must add to active
          // note this could be made easier by a level of indirection,
          // i.e. have ccn point to cc directly
          ccTgt = active->push_back(al, r);
          d_curChildren[r] = ccTgt;
          d_dom.emplace_back(r, ccTgt);
          Trace("cdt-debug") << "new child " << r << std::endl;
        }
      }
      else
      {
        // mark that it will need to be merged
        ccTgt = it->second;
      }
      // now, perform the merge cc to ccTgt.
      ccTgt->addToMerge(al, cc, isChildLeaf);
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
  // start the iterator
  d_index = 0;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
