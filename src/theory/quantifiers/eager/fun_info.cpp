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

#include "theory/quantifiers/eager/fun_info.h"

#include "theory/quantifiers/eager/trigger_info.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

FunInfo::FunInfo(context::Context* c) : d_trie(c), d_count(c, 0) {}

bool FunInfo::addTerm(TermDbEager& tde, TNode t, const std::vector<TNode>& reps)
{
  if (!d_trie.add(tde.getCdtAlloc(), reps, t))
  {
    return false;
  }
  d_count = d_count + 1;
  for (size_t i = 0, nchildren = reps.size(); i < nchildren; i++)
  {
    // add relevant domains
    addRelevantDomain(i, reps[i]);
  }
  // try matching?
  for (TriggerInfo* tr : d_triggers)
  {
    tr->doMatching(tde, t);
    // TODO: break?
  }
  return true;
}

void FunInfo::addRelevantDomain(size_t i, TNode r)
{
  // TODO
}

bool FunInfo::inRelevantDomain(size_t i, TNode r) const { return false; }

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
