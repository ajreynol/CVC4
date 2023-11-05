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
 * Eager term database
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_EAGER_H
#define CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_EAGER_H

#include <vector>

#include "expr/node.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/cd_tnode_trie.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class TermDb;

/**
 */
class TermDbEager : protected EnvObj
{
 public:
  TermDbEager(Env& env, QuantifiersState& qs, TermDb& tdb);

  /** notification when master equality engine is updated */
  void eqNotifyNewClass(TNode t);
  /** notification when master equality engine is updated */
  void eqNotifyMerge(TNode t1, TNode t2);

  /** Is in relevant domain? */
  bool inRelevantDomain(TNode f, size_t i, TNode r);
  /** Get congruent term */
  TNode getCongruentTerm(TNode f, const std::vector<TNode>& args);

 private:
  CDTNodeTrie* getTrieFor(TNode op);
  Node d_null;
  QuantifiersState& d_qs;
  TermDb& d_tdb;
  CDTNodeTrieAllocator d_cdalloc;
  /** */
  std::map<TNode, std::shared_ptr<CDTNodeTrie>> d_trie;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_EAGER_H */
