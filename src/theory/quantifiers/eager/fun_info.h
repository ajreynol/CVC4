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

class RelDomInfo
{
 public:
  RelDomInfo(context::Context* c);
  /** The domain */
  context::CDHashSet<Node> d_dom;
  /** Has term? */
  bool hasTerm(QuantifiersState& qs, TNode r);
};

class FunInfo
{
 public:
  FunInfo(TermDbEager& tde);
  /** Add term */
  void addTerm(TNode t);
  /** Add relevant domain */
  void addRelevantDomain(size_t i, TNode r);
  /** Is in relevant domain */
  bool inRelevantDomain(size_t i, TNode r);
  /** Activate */
  void setActive(bool active);
  /** All terms */
  CDTNodeTrie d_trie;
  /** Number of terms for this function */
  context::CDO<size_t> d_count;
  /** Triggers with this as top symbol */
  std::vector<TriggerInfo*> d_triggers;
  /** Active? */
  context::CDO<bool> d_active;
  /** Wait list */
  WaitList d_terms;

 private:
  TermDbEager& d_tde;
  /** */
  std::vector<RelDomInfo> d_rinfo;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
