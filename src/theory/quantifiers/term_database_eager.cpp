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

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"


namespace cvc5::internal {
namespace theory {
namespace quantifiers {

TermDbEager::TermDbEager(Env& env, QuantifiersState& qs, TermDb& tdb) : EnvObj(env), d_qs(qs), d_tdb(tdb), d_cdalloc(context()) {}

void TermDbEager::eqNotifyNewClass(TNode t) {
  // add to the eager trie
  TNode mop = d_tdb.getMatchOperator(t);
  if (mop.isNull())
  {
    std::vector<TNode> reps;
    for (const Node& tc : t)
    {
      reps.emplace_back(d_qs.getRepresentative(tc));
    }
    CDTNodeTrie* tt = getTrieFor(mop);
    tt->add(&d_cdalloc, reps, t);
  }
}

void TermDbEager::eqNotifyMerge(TNode t1, TNode t2) {}

bool TermDbEager::inRelevantDomain(TNode f, size_t i, TNode r) { return false; }

TNode TermDbEager::getCongruentTerm(TNode f, const std::vector<TNode>& args)
{
  return d_null;
}

CDTNodeTrie* TermDbEager::getTrieFor(TNode op)
{
  std::map<TNode, std::shared_ptr<CDTNodeTrie>>::iterator it = d_trie.find(op);
  if (it==d_trie.end())
  {
    auto itt = d_trie.insert({op, std::make_shared<CDTNodeTrie>(context())});
    Assert (itt.second);
    return itt.first->second.get();
  }
  return it->second.get();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
