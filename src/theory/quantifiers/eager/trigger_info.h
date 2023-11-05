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
  void initialize(TermDbEager& tde, const Node& t);
  /** */
  void watch(const Node& q);

  void doMatching(TermDbEager& tde, TNode t);

  void doMatchingEqc(TermDbEager& tde, TNode eqc);

  void doMatchingAll(TermDbEager& tde);

 private:
  /** Instantiation evaluator */

  Node d_pattern;
  /** ground arguments */
  std::vector<size_t> d_gargs;
  /** variable arguments */
  std::vector<size_t> d_vargs;
  /** other arguments */
  std::vector<size_t> d_oargs;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
