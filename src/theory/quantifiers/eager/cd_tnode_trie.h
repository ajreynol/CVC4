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
  /** List of reps and children, possible stale */
  context::CDList<TNode> d_reps;
  /** The children */
  context::CDList<CDTNodeTrie*> d_repChildren;
  /** The size of d_reps that is valid */
  context::CDO<size_t> d_repSize;
  /** Adds term without cleaning */
  void add(CDTNodeTrieAllocator* a, const std::vector<TNode>& args, TNode t);
  /** For leaf nodes : does this node have data? */
  bool hasData() const { return !d_reps.empty(); }
  /** For leaf nodes : get the node corresponding to this leaf. */
  TNode getData() const { return *d_reps.begin(); }
};

class CDTNodeTrieAllocator
{
 public:
  CDTNodeTrieAllocator(context::Context* c);
  /** Allocate a new trie node */
  CDTNodeTrie* alloc();

 private:
  context::Context* d_ctx;
  std::vector<std::unique_ptr<CDTNodeTrie>> d_alloc;
};

/**
 * Traverses and automatically cleans a CDTNodeTrie.
 */
class CDTNodeTrieIterator
{
 public:
  CDTNodeTrieIterator(CDTNodeTrieAllocator* a,
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
  void setActive(const std::vector<CDTNodeTrie*>& active);
  CDTNodeTrieAllocator* d_alloc;
  QuantifiersState& d_qs;
  CDTNodeTrie* d_active;
  std::vector<std::pair<TNode, std::vector<CDTNodeTrie*>>> d_curChildren;
  size_t d_cindex;
  Node d_null;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
