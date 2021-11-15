/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2021 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Information for each search level in ccfv
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__SEARCH_LEVEL_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__SEARCH_LEVEL_H

#include <vector>

#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

class SearchLevel
{
 public:
  SearchLevel() {}
  /** the list of variables we assign at this search level */
  std::vector<TNode> d_varsToAssign;
  /** The quantified formulas that are fully assigned at this level */
  std::vector<TNode> d_finalQuants;
  /** The quantified formulas that are rooted as this level */
  std::vector<TNode> d_startQuants;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
