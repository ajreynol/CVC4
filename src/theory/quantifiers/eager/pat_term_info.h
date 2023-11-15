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
 * Pattern term info for eager instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__PAT_TERM_INFO_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__PAT_TERM_INFO_H

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/eager/cd_tnode_trie.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

namespace ieval {
class InstEvaluator;
}

class TermDbEager;
class CDTNodeTrieIterator;

namespace eager {

class TriggerInfo;

class PatTermInfo
{
  friend class TriggerInfo;

 public:
  PatTermInfo(TermDbEager& tde);
  /**
   * Initialize the pattern term for n whose parent is tr. This pattern will
   * be processed in a context where fvs are already bound.
   */
  void initialize(TriggerInfo* tr,
                  const Node& t,
                  std::unordered_set<Node>& fvs,
                  bool bindOrder,
                  bool isTop);
  /**
   * Do matching against ground term t. Returns true if successful, in which
   * case we bind all free variables in this pattern term in ie. Otherwise,
   * ie is unmodified.
   */
  bool doMatching(ieval::InstEvaluator* ie, TNode t);
  /**
   * Initialize this class to match terms in eq class r. Return false if
   * we can quickly determine it is not possible to do so.
   */
  bool initMatchingEqc(ieval::InstEvaluator* ie, TNode r);
  /**
   * Initialize this class to match the next term in the equivalence class
   * we are considering. Returns true if successful, in which case we bind all
   * free variables in this pattern term in ie. Otherwise, ie is unmodified.
   *
   * Must call initMatchingEqc successfully before this method.
   */
  bool doMatchingEqcNext(ieval::InstEvaluator* ie);
  /** initialize matching all */
  void initMatchingAll(ieval::InstEvaluator* ie);
  /**
   * Do the next step in matching all.
   *
   * Must call initMatchingAll before this method.
   */
  bool doMatchingAllNext(ieval::InstEvaluator* ie);
  /**
   * Get match, add to varToTerm.
   * This maps any variables bound by this trigger during doMatchingAllNext
   * to the syntactic term, based on the leaf of the trie we traversed to.
   */
  void getMatch(std::map<Node, Node>& varToTerm);

  size_t getNumBindings() const { return d_nbind; }

 private:
  bool isLegalCandidate(TNode n) const;
  bool doMatchingAllInternal(ieval::InstEvaluator* ie);
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** The pattern */
  Node d_pattern;
  /** The operator */
  Node d_op;
  /** ground arguments */
  std::vector<size_t> d_gargs;
  /** variable arguments */
  std::vector<size_t> d_vargs;
  /** ground arguments, post-binding */
  std::vector<size_t> d_gpargs;
  /** other arguments */
  std::vector<size_t> d_oargs;
  /** children */
  std::vector<PatTermInfo*> d_children;
  /** the number of variables bound by each child, in order */
  std::vector<size_t> d_bindings;
  /** Whether each child has bound variables */
  std::vector<bool> d_childrenBv;
  /** the sum of the number of bindings */
  size_t d_nbind;
  //======== eqc matching
  TNode d_eqc;
  eq::EqClassIterator d_eqi;
  //======== all matching
  CDTNodeTrieIterator d_itt;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
