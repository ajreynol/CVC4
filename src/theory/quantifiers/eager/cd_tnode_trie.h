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
   * The label of the incoming edge. This is null for the root node.
   */
  context::CDO<TNode> d_edge;
  /**
   * Mapping from reps to the index in d_repChildren, possible stale.
   * This data is kept for fast lookups to single children.
   *
   * This map is also used to store the data of leafs.
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
  /**
   * Adds a term, possibly refactoring this trie.
   * Returns true if t was added to the trie, false otherwise.
   */
  bool add(CDTNodeTrieAllocator* al,
           QuantifiersState& qs,
           const std::vector<TNode>& args,
           TNode t);
  /** Adds term without cleaning */
  bool addSimple(CDTNodeTrieAllocator* al,
                 const std::vector<TNode>& args,
                 TNode t);
  /** For leaf nodes : does this node have data? */
  bool hasData() const { return !d_repMap.empty(); }
  /** Set data, return true if sucessful, else t is marked congruent */
  bool setData(CDTNodeTrieAllocator* al, TNode t);
  /** For leaf nodes : get the node corresponding to this leaf. */
  TNode getData() const { return d_repMap.begin()->first; }
  /** Push an edge r and return the child */
  CDTNodeTrie* push_back(CDTNodeTrieAllocator* al, TNode r);
  /** Mark that t should be merged into this trie. */
  void addToMerge(CDTNodeTrieAllocator* al, CDTNodeTrie* t, bool isChildLeaf);
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
  /** The set of terms we have determined are congruent in the current ctx */
  context::CDHashSet<Node> d_congruent;
  /** All trie nodes we have allocated */
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
  /**
   * Get the next child in the iteration and push it.
   * Returns the term that was pushed if successful or the null node otherwise.
   */
  TNode pushNextChild();
  /** Push the child r. Returns true if successul. */
  bool push(TNode r);
  /** Pop the last push */
  void pop();
  /** Get the data at the leaf we are at */
  TNode getCurrentData();
  /** Get the leaf we are at */
  CDTNodeTrie* getCurrent();
  /** Set the data of the current leaf */
  bool setData(TNode n);
  /** Get level */
  size_t getLevel() const { return d_stack.size(); }

 private:
  /** Pointer to the allocator */
  CDTNodeTrieAllocator* d_alloc;
  QuantifiersState& d_qs;
  class StackFrame
  {
   public:
    StackFrame(CDTNodeTrieAllocator* al,
               QuantifiersState& qs,
               CDTNodeTrie* active,
               bool isChildLeaf);
    /** The trie whose children we are iterating */
    CDTNodeTrie* d_active;
    /** The children of d_active we computed, used for direct child lookups */
    std::map<TNode, CDTNodeTrie*> d_curChildren;
    /** Domain, used for full iterations */
    std::vector<std::pair<TNode, CDTNodeTrie*>> d_dom;
    /** The current index in the domain we are considering */
    size_t d_index;
    /** Is the iteration finished */
    bool isFinished() const { return d_index == d_dom.size(); }
  };
  /** The iteration stack */
  std::vector<StackFrame> d_stack;
  /** The leaf we iterated to, which is not added to d_stack */
  CDTNodeTrie* d_curData;
  /** The overall depth we are iterating to */
  size_t d_depth;
  /** The null node */
  Node d_null;
  /**
   * Push the iteration to the given node, which should be a child of the
   * current active node (d_stack.back().d_active).
   */
  void pushInternal(CDTNodeTrie* cdtnt);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
