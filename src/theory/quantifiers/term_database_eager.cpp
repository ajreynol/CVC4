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
 * Eager term database
 */

#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TermDbEager::TermDbEager(Env& env, QuantifiersState& qs) : EnvObj(env) {}

void TermDbEager::eqNotifyNewClass(TNode t)
{
}

void TermDbEager::eqNotifyMerge(TNode t1, TNode t2)
{
  
}

bool TermDbEager::inRelevantDomain(TNode f, size_t i, TNode r)
{
  return false;
}

TNode TermDbEager::getCongruentTerm(Node f, const std::vector<TNode>& args)
{
  return d_null;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

