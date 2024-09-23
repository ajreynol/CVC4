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
  bool add(QuantifiersState& qs, EagerGroundTrieAllocator* al, TNode t);
  bool isCongruent(QuantifiersState& qs, TNode t) const;
  bool contains(QuantifiersState& qs, const std::vector<TNode>& args) const;
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
  /**
   * WANT: possible joins of args
   *
   *
   * P(x,y) P(y,z) P(z,w), Q(z)
   *
   * P(a,b)
   *
   *  a:
   *    b:
   *      _:
   *        _: 1
   *  _:
   *    a:
   *      b:
   *        _: 2
   *    _:
   *      a:
   *        b: 3
   *
   *
   * P(b,c)
   *
   *  a:
   *    b:
   *      _:
   *        _: 1
   *  b:
   *    c:
   *      _:
   *        _: 1
   *  _:
   *    a:
   *      b:
   *        _: 2
   *    b:
   *      c:
   *        _: 2
   *    _:
   *      a:
   *        b: 3
   *      b:
   *        c: 3
   *
   * P(c,d)
   *
   * Each pattern within a multi-trigger is added to the ordinary trie. Instead
   * of instantiation, we notify the match to the handling of multi triggers.
   *
   * Ground trie per (pattern, index), leaf stores (single?) ground term.
   * Arguments may be null.
   *
   * If notified (term g, pattern, n) -> [t1? ... tk?]
   * 1. add to trie, return if redundant.  Redundant is only on first add: g may
   * be re-added due to a watch.
   * 2. for each index = 1 ... p \ n, collect list of compatible term vectors
   * V_i. Take V_n = (g, [t1? ... tk?]).
   * 3. compute product of vectors.
   *    Start with V_n.
   *    Proceed with those with shared variables, smallest size.
   *    For each failure, add a watch to (one of) the ground terms if not
   * clearly disequal.
   *
   * In 3, compute step 2 only for those with shared variables.
   * In 2, traverse as we go. Do not compute vectors.
   * Track size per ground trie as a heuristic.
   *
   *
   * P(a,b) P(c,d) then b=c???
   *
   * Need SAT-context dependent computation of congruent term via e.g. equality
   * engine.
   *
   *
   */
 private:
  bool containsInternal(QuantifiersState& qs,
                        const std::vector<TNode>& args,
                        size_t i) const;
  bool isCongruentInternal(QuantifiersState& qs, TNode t, size_t i) const;
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
  EagerGroundTrieAllocator* getAlloc() { return &d_alloc; }
  EagerGroundTrie* getTrie(const Node& op);

 private:
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
