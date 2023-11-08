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
 * Function info for eager instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__FUN_INFO_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__FUN_INFO_H

#include "context/cdhashmap.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/eager/cd_tnode_trie.h"
#include "theory/quantifiers/eager/util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbEager;

namespace eager {

class TriggerInfo;

#if 0
class RelDomInfo
{
 public:
  RelDomInfo(context::Context* c);
  /** The domain */
  context::CDHashSet<Node> d_dom;
  /** Has term? */
  bool hasTerm(QuantifiersState& qs, TNode r);
};
#endif

class FunInfo
{
 public:
  FunInfo(TermDbEager& tde);
  /** Initialize */
  void initialize(TNode f, size_t nchild);
  /** Add term */
  bool addTerm(TNode t);
  /** Is in relevant domain */
  bool inRelevantDomain(size_t i, TNode r);
  /** Get trie */
  CDTNodeTrie* getTrie();
  /** Number of terms */
  size_t getNumTerms() const;
  /** Triggers with this as top symbol */
  std::vector<TriggerInfo*> d_triggers;

 private:
  /** Activate */
  void setActive(bool active);
  /** Refresh */
  void refresh();
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** Relevant domain for the arguments of this function */
  // std::vector<std::unique_ptr<RelDomInfo>> d_rinfo;
  /** All terms */
  CDTNodeTrie d_trie;
  /** Number of terms for this function */
  context::CDO<size_t> d_count;
  /** Active? */
  context::CDO<bool> d_active;
  /** Wait list */
  WaitList d_terms;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
