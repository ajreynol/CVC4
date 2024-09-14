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
class EagerInst;

class EagerTermIterator
{
  friend class EagerInst;

 public:
  EagerTermIterator(const Node& t) : d_orig(t) { d_stack.emplace_back(t, 0); }
  EagerTermIterator(const Node& n, const Node& t) : d_orig(n)
  {
    d_stack.emplace_back(t, 0);
  }
  TNode getOriginal() const { return d_orig; }
  TNode getCurrent() const
  {
    Assert(!d_stack.empty());
    const std::pair<Node, size_t>& cur = d_stack.back();
    Assert(cur.second < cur.first.getNumChildren());
    return cur.first[cur.second];
  }
  bool needsBacktrack() const
  {
    Assert(!d_stack.empty());
    const std::pair<Node, size_t>& cur = d_stack.back();
    return cur.second == cur.first.getNumChildren();
  }
  void incrementChild() { d_stack.back().second++; }
  void decrementChild()
  {
    Assert(d_stack.back().second > 0);
    d_stack.back().second--;
  }
  void push(const Node& t) { d_stack.emplace_back(t, 0); }
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
  Node d_orig;
  std::vector<std::pair<Node, size_t>> d_stack;
};

class EagerTrie
{
 public:
  EagerTrie();
  /** An example of a pattern that was added */
  Node d_exPat;
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
