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

class FunInfo
{
 public:
  FunInfo(TermDbEager& tde);
  /** Initialize */
  void initialize(TNode f, size_t nchild);
  /** Get arity */
  size_t getArity() const { return d_arity; }
  /** Add term */
  bool addTerm(TNode t);
  /** Do matching with term */
  bool notifyTriggers(TNode t, bool isAsserted);
  /** Is in relevant domain */
  bool inRelevantDomain(size_t i, TNode r);
  /** Get trie */
  CDTNodeTrie* getTrie();
  /** Number of terms */
  size_t getNumTerms() const;
  /** Add trigger */
  void addTrigger(TriggerInfo* tinfo);
  /** Triggers with this as top symbol */
  std::vector<TriggerInfo*>& getTriggers() { return d_triggers; }
 private:
  /** Activate */
  bool setActive(bool active);
  /** Refresh */
  bool refresh();
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** the operator */
  Node d_op;
  /** the arity */
  size_t d_arity;
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
  /** Triggers with this as top symbol */
  std::vector<TriggerInfo*> d_triggers;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
