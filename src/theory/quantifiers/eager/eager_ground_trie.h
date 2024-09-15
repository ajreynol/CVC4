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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_GROUND_TRIE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_GROUND_TRIE_H

#include "context/cdhashmap.h"
#include "context/cdhashset.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "smt/env_obj.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDb;
class QuantifiersState;
class EagerGroundTrieAllocator;

class EagerGroundTrie
{
 public:
  EagerGroundTrie(context::Context* c);
  /**
   * Adds a term, without refactoring this trie.
   * Returns true if t was added to the trie, false otherwise.
   */
  bool add(EagerGroundTrieAllocator* al,
           const std::vector<TNode>& args,
           TNode t);
  /** Push an edge r and return the child */
  EagerGroundTrie* push_back(EagerGroundTrieAllocator* al, TNode r);
  /** For leaf nodes : does this node have data? */
  bool hasData() const { return !d_cmap.empty(); }
  /** Set data, return true if sucessful, else t is marked congruent */
  bool setData(EagerGroundTrieAllocator* al, TNode t);
  /** For leaf nodes : get the node corresponding to this leaf. */
  TNode getData() const { return d_cmap.begin()->first; }

 private:
  /** */
  context::CDHashMap<TNode, size_t> d_cmap;
  /**
   * The size of d_children that are valid in this context.
   */
  context::CDO<size_t> d_csize;
  /** The children, stored in a non-context-dependent manner. */
  std::vector<EagerGroundTrie*> d_children;
};

class EagerGroundTrieAllocator
{
 public:
  EagerGroundTrieAllocator(context::Context* c);
  /** Allocate a new trie node */
  EagerGroundTrie* alloc()
  {
    d_alloc.emplace_back(
        std::shared_ptr<EagerGroundTrie>(new EagerGroundTrie(d_ctx)));
    return d_alloc.back().get();
  }
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
  std::vector<std::shared_ptr<EagerGroundTrie>> d_alloc;
};

class EagerGroundDb : protected EnvObj
{
 public:
  EagerGroundDb(Env& env, QuantifiersState& qs, TermDb* tdb);
  bool add(const Node& n);

 private:
  EagerGroundTrie* getTrie(const Node& op);
  /** */
  QuantifiersState& d_qstate;
  /** */
  TermDb* d_tdb;
  /** */
  EagerGroundTrieAllocator d_alloc;
  /** */
  std::map<Node, EagerGroundTrie*> d_db;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
