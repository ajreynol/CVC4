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
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

namespace ieval {
class InstEvaluator;
}

class TermDbEager;

namespace eager {

class TriggerInfo;

class PatTermInfo
{
  friend class TriggerInfo;
 public:
  PatTermInfo(TermDbEager& tde);
  /** Initialize */
  void initialize(TriggerInfo* tr, const Node& t, std::unordered_set<Node>& fvs);
  /** Do matching */
  bool doMatching(ieval::InstEvaluator* ie, TNode t);
  bool initMatchingEqc(ieval::InstEvaluator* ie, TNode r);
  bool doMatchingEqcNext(ieval::InstEvaluator* ie);
  /** get ground args */
  const std::vector<size_t>& getGroundArgs() const { return d_gargs; }
  std::vector<PatTermInfo*>& getChildren() { return d_children; }
  size_t getNumBindings() const { return d_nbind; }
 private:
  bool isLegalCandidate(TNode n) const;
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
  /** the sum of the number of bindings */
  size_t d_nbind;
  //======== eqc matching
  TNode d_eqc;
  eq::EqClassIterator d_eqi;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
