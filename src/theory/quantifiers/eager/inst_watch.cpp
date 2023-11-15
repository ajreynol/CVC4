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

#include "theory/quantifiers/eager/inst_watch.h"

#include "context/cdo.h"
#include "expr/node.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

InstWatch::InstWatch(TermDbEager& tde) : d_tde(tde) {}

void InstWatch::watch(const Node& q, std::vector<Node>& terms, const Node& entv)
{
}

bool InstWatch::eqNotifyMerge(TNode t1, TNode t2)
{
  return false;
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
