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
 * Instantiation watch
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__INST_WATCH_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__INST_WATCH_H

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbEager;

namespace eager {

class QuantInfo;

class InstWatch
{
 public:
  InstWatch(TermDbEager& tde);
  void watch(const Node& q, std::vector<Node>& terms, const Node& entv);

 private:
  /** Reference to the eager term database */
  TermDbEager& d_tde;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
