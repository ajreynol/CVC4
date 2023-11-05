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
 * Eager term index.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__CD_TNODE_TRIE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__CD_TNODE_TRIE_H

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class CDTNodeTrieAllocator;

class CDTNodeTrie
{
 public:
  CDTNodeTrie(context::Context* c);
  context::CDO<TNode> d_data;
  /** List of reps and children, possible stale */
  context::CDHashMap<TNode, size_t> d_repMap;
  /** The children */
  std::vector<CDTNodeTrie*> d_repChildren;
  /** The size of d_reps that is valid */
  context::CDO<size_t> d_repSize;
  /** To merge */
  context::CDList<CDTNodeTrie*> d_toMerge;
  /** To merge index */
  context::CDO<size_t> d_toMergeProcessed;
  /** clear */
  void clear();
  /** Adds term without cleaning */
  void add(CDTNodeTrieAllocator* al, const std::vector<TNode>& args, TNode t);
  /** For leaf nodes : does this node have data? */
  bool hasData() const { return !d_data.get().isNull(); }
  /** For leaf nodes : get the node corresponding to this leaf. */
  TNode getData() const { return d_data.get(); }
  CDTNodeTrie* push_back(CDTNodeTrieAllocator* al, TNode r);
};

class CDTNodeTrieAllocator
{
 public:
  CDTNodeTrieAllocator(context::Context* c);
  /** Allocate a new trie node */
  CDTNodeTrie* alloc();

 private:
  context::Context* d_ctx;
  context::CDList<std::shared_ptr<CDTNodeTrie>> d_alloc;
};

/**
 * Traverses and automatically cleans a CDTNodeTrie.
 */
class CDTNodeTrieIterator
{
 public:
  CDTNodeTrieIterator(CDTNodeTrieAllocator* al,
                      QuantifiersState& qs,
                      CDTNodeTrie* cdtnt);
  /** Get the next child in this trie and push it */
  TNode pushNextChild();
  /** Push the child r */
  bool push(TNode r);
  /** Pop the last push */
  void pop();
  /** Get the term at the current leaf */
  TNode getData();

 private:
  CDTNodeTrieAllocator* d_alloc;
  QuantifiersState& d_qs;
  class StackFrame
  {
   public:
    StackFrame(CDTNodeTrieAllocator* al,
               QuantifiersState& qs,
               CDTNodeTrie* active);
    CDTNodeTrie* d_active;
    std::map<TNode, CDTNodeTrie*> d_curChildren;
    std::map<TNode, CDTNodeTrie*>::iterator d_cit;
    bool isFinished() const { return d_cit == d_curChildren.end(); }
  };
  std::vector<StackFrame> d_stack;
  Node d_null;
  bool pushInternal(CDTNodeTrie* cdtnt);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
