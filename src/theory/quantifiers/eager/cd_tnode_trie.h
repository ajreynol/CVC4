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
#include "context/cdhashset.h"
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
  /**
   * The data, which is either the leaf data, or the label of the incoming edge.
   * This is null for the root node.
   */
  context::CDO<TNode> d_data;
  /**
   * Mapping from reps to the index in d_repChildren, possible stale.
   * This data is kept for fast lookups to single children.
   */
  context::CDHashMap<TNode, size_t> d_repMap;
  /** The children, stored in a non-context-depedent manner. */
  std::vector<CDTNodeTrie*> d_repChildren;
  /**
   * The size of d_reps that may be valid in this context. Note that some
   * children in the valid range may be invalid.
   */
  context::CDO<size_t> d_repSize;
  /** List of cousins we are waiting to merge */
  context::CDList<CDTNodeTrie*> d_toMerge;
  /** The index in the above vector we have processed */
  context::CDO<size_t> d_toMergeProcessed;
  /** clear */
  void clear();
  /** Adds term without cleaning */
  bool add(CDTNodeTrieAllocator* al, const std::vector<TNode>& args, TNode t);
  /** For leaf nodes : does this node have data? */
  bool hasData() const { return !d_data.get().isNull(); }
  /** Set data, return true if we set */
  bool setData(CDTNodeTrieAllocator* al, TNode t);
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
  /** Mark congruent */
  void markCongruent(TNode t) { d_congruent.insert(t); }
  /** Is term congruent? */
  bool isCongruent(TNode t) const
  {
    return d_congruent.find(t) != d_congruent.end();
  }

 private:
  context::Context* d_ctx;
  context::CDHashSet<Node> d_congruent;
  std::vector<std::shared_ptr<CDTNodeTrie>> d_alloc;
};

/**
 * Traverses and automatically cleans a CDTNodeTrie.
 */
class CDTNodeTrieIterator
{
 public:
  CDTNodeTrieIterator(CDTNodeTrieAllocator* al,
                      QuantifiersState& qs,
                      CDTNodeTrie* cdtnt,
                      size_t depth);
  /** Get the next child in this trie and push it */
  TNode pushNextChild();
  /** Push the child r */
  bool push(TNode r);
  /** Pop the last push */
  void pop();
  /** Get the term at the current leaf */
  TNode getData();
  /** Get level */
  size_t getLevel() const { return d_stack.size(); }

 private:
  CDTNodeTrieAllocator* d_alloc;
  QuantifiersState& d_qs;
  class StackFrame
  {
   public:
    StackFrame(CDTNodeTrieAllocator* al,
               QuantifiersState& qs,
               CDTNodeTrie* active,
               bool isChildLeaf);
    CDTNodeTrie* d_active;
    std::map<TNode, CDTNodeTrie*> d_curChildren;
    std::map<TNode, CDTNodeTrie*>::iterator d_cit;
    std::unordered_set<TNode> d_pushed;
    bool isFinished() const { return d_cit == d_curChildren.end(); }
  };
  std::vector<StackFrame> d_stack;
  size_t d_depth;
  Node d_null;
  bool pushInternal(CDTNodeTrie* cdtnt);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
