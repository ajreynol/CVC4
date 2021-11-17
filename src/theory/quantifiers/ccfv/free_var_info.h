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
 * Info per free variable in CCFV.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__CCFV__FREE_VAR_INFO_H
#define CVC5__THEORY__QUANTIFIERS__CCFV__FREE_VAR_INFO_H

#include <unordered_set>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5 {
namespace theory {
namespace quantifiers {
namespace ccfv {

/**
 * Information for a free variable.
 */
class FreeVarInfo
{
  using NodeList = context::CDList<Node>;
  using NodeSet = context::CDHashSet<Node>;

 public:
  FreeVarInfo(context::Context* c);
  /**
   * Final term list, all pattern terms that are fully assigned when we have an
   * assignment for this variable, based on the global variable ordering.
   */
  NodeSet d_finalTerms;
  /** List of quantifiers that contain this variable */
  NodeList d_quantList;
  /** Get next quantifier, and increment the quantifier index. */
  TNode getNextQuantifier();

 private:
  /** The current index in d_quantList we are looking at, for matching */
  context::CDO<size_t> d_quantIndex;
};

}  // namespace ccfv
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5

#endif
