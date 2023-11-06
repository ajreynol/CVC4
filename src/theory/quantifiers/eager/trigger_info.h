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
 * Quantifier info for eager instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__TRIGGER_INFO_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__TRIGGER_INFO_H

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbEager;

namespace eager {

class TriggerInfo
{
 public:
  TriggerInfo(context::Context* c);
  /** Initialize */
  void initialize(TermDbEager& tde, const Node& t, const Node& f);
  /** */
  void watch(const Node& q);

  bool doMatching(TermDbEager& tde, TNode t);


  bool doMatchingAll(TermDbEager& tde);

 private:
  bool initMatchingEqc(TermDbEager& tde, TNode r);
  bool doMatchingEqcNext(TermDbEager& tde, ieval::InstEvaluator* ie, size_t& npush);
  bool doMatchingInternal(TermDbEager& tde, ieval::InstEvaluator* ie, TNode t, size_t& npush);
  /** Are ground children */
  bool d_isAllGargs;
  /** Instantiation evaluator */
  std::unique_ptr<ieval::InstEvaluator> d_ieval;
  /** The pattern */
  Node d_pattern;
  /** The operator */
  Node d_op;
  /** The arity */
  size_t d_arity;
  /** ground arguments */
  std::vector<size_t> d_gargs;
  /** variable arguments */
  std::vector<size_t> d_vargs;
  /** other arguments */
  std::vector<size_t> d_oargs;
  /** children */
  std::vector<TriggerInfo*> d_children;
  //======== eqc matching
  TNode d_eqc;
  eq::EqClassIterator d_eqi;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
