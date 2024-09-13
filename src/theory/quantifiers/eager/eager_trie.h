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

class EagerTrie
{
 public:
  std::map<uint64_t, EagerTrie> d_varChildren;
  std::map<uint64_t, EagerTrie> d_checkVarChildren;
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
                   const Node& pat,
                   const Node& n,
                   size_t i,
                   std::vector<std::pair<Node, size_t>>& ets,
                   std::vector<uint64_t>& alreadyBound,
                   bool isErase);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
