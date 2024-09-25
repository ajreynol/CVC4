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

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_TRIE_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__EAGER_TRIE_H

#include "context/cdlist.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDb;
class EagerInst;

/**
 *
 */
class EagerTermIterator
{
  friend class EagerInst;

 public:
  EagerTermIterator(TNode t);
  TNode getOriginal() const { return d_orig; }
  TNode getCurrent() const
  {
    Assert(!d_stack.empty());
    const std::pair<TNode, size_t>& cur = d_stack.back();
    Assert(cur.second <= cur.first.getNumChildren());
    return cur.first[cur.second];
  }
  void incrementChild() { d_stack.back().second++; }
  void decrementChild()
  {
    Assert(d_stack.back().second > 0);
    d_stack.back().second--;
  }
  bool needsBacktrack() const
  {
    Assert(!d_stack.empty());
    const std::pair<TNode, size_t>& cur = d_stack.back();
    return cur.second == cur.first.getNumChildren();
  }
  void push(TNode t) { d_stack.emplace_back(t, 0); }
  bool canPop() const { return d_stack.size() > 1; }
  bool pop()
  {
    if (d_stack.size() <= 1)
    {
      return false;
    }
    d_stack.pop_back();
    return true;
  }

 private:
  TNode d_orig;
  std::vector<std::pair<TNode, size_t>> d_stack;
};

class EagerTrie
{
 public:
  EagerTrie();
  std::map<uint64_t, EagerTrie> d_varChildren;
  std::map<uint64_t, EagerTrie> d_checkVarChildren;  // TODO: use???
  std::map<Node, EagerTrie> d_groundChildren;
  std::map<Node, EagerTrie> d_ngroundChildren;
  std::vector<Node> d_pats;
  /**
   * Permits adding pattern terms directly e.g. (P x), or instantiation pattern
   * terms of the form (INST_PATTERN (P x) t1 ... tn), where (P x) is a complete
   * single trigger and t1 ... tn do not have further variables to match.
   */
  EagerTrie* add(TermDb* tdb, TNode pat);
  void erase(TermDb* tdb, TNode pat);
  bool empty() const;

 private:
  EagerTrie* addInternal(TermDb* tdb,
                         EagerTermIterator& eti,
                         std::vector<uint64_t>& alreadyBound,
                         bool isErase);
};

class CDEagerTrie
{
 public:
  CDEagerTrie(context::Context* c);
  /** Add pattern */
  EagerTrie* addPattern(TermDb* tdb, TNode pat);
  /** */
  EagerTrie* getCurrent(TermDb* tdb);

 private:
  void makeCurrent(TermDb* tdb);
  EagerTrie d_trie;
  /** The patterns for this operator in the current context */
  context::CDList<Node> d_pats;
  std::vector<Node> d_triePats;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
