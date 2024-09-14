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

#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDb;

class EagerTermIterator
{
 public:
  EagerTermIterator(const Node& t) : d_orig(t), d_term(t), d_index(0) {}
  EagerTermIterator(const Node& n, const Node& t)
      : d_orig(n), d_term(t), d_index(0)
  {
  }
  TNode getOriginal() const { return d_orig; }
  TNode getCurrent() const
  {
    Assert(d_index < d_terms.size());
    return d_term[d_index];
  }
  bool needsBacktrack() const { return d_index == d_term.getNumChildren(); }
  void incrementChild() { d_index++; }
  void decrementChild()
  {
    Assert(d_index > 0);
    d_index--;
  }
  void push()
  {
    d_stack.emplace_back(d_term, d_index + 1);
    d_term = d_term[d_index];
    d_index = 0;
  }
  bool pop()
  {
    if (d_stack.empty())
    {
      return false;
    }
    std::pair<Node, size_t> p = d_stack.back();
    d_term = p.first;
    d_index = p.second;
    d_stack.pop_back();
    return true;
  }

 private:
  Node d_orig;
  Node d_term;
  size_t d_index;
  std::vector<std::pair<Node, size_t>> d_stack;
};

class EagerTrie
{
 public:
  EagerTrie();
  EagerTrie* d_parent;
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
  bool add(TermDb* tdb, const Node& pat);
  bool erase(TermDb* tdb, const Node& pat);
  bool empty() const;

 private:
  bool addInternal(TermDb* tdb,
                   EagerTermIterator& eti,
                   std::vector<uint64_t>& alreadyBound,
                   bool isErase);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
