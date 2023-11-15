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
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

InstWatch::InstWatch(TermDbEager& tde) : d_tde(tde), d_qs(tde.getState()) {}

void InstWatch::watch(const Node& q,
                      const std::vector<Node>& terms,
                      const Node& entv)
{
  Trace("eager-inst-watch") << "Watch " << entv << std::endl;
}

bool InstWatch::eqNotifyMerge(TNode t1, TNode t2) { return false; }

WatchTermInfo* InstWatch::getWatchTermInfo(const Node& t)
{
  Assert(!t.isNull());
  std::map<Node, WatchTermInfo>::iterator it = d_wtInfo.find(t);
  if (it == d_wtInfo.end())
  {
    d_wtInfo.emplace(t, d_tde.getEnv().getContext());
    it = d_wtInfo.find(t);
  }
  return &it->second;
}

WatchQuantInfo* InstWatch::getWatchQuantInfo(const Node& q)
{
  Assert(!q.isNull());
  std::map<Node, WatchQuantInfo>::iterator it = d_wqInfo.find(q);
  if (it == d_wqInfo.end())
  {
    d_wqInfo.emplace(q, d_tde.getEnv().getContext());
    it = d_wqInfo.find(q);
    // initialize the evaluator
    it->second.d_ieval.reset(
        new ieval::InstEvaluator(d_tde.getEnv(),
                                 d_tde.getState(),
                                 d_tde.getTermDb(),
                                 ieval::TermEvaluatorMode::PROP,
                                 false,
                                 false,
                                 false,
                                 true));
  }
  return &it->second;
}

Node InstWatch::mkInstantiation(const Node& q, const std::vector<Node>& terms)
{
  Assert(!terms.empty());
  std::vector<Node> sterms;
  sterms.push_back(q);
  sterms.insert(sterms.end(), terms.begin(), terms.end());
  return NodeManager::currentNM()->mkNode(Kind::SEXPR, sterms);
}

Node InstWatch::getInstantiation(const Node& inst, std::vector<Node>& terms)
{
  Assert(inst.getKind() == Kind::SEXPR && inst.getNumChildren() >= 2);
  terms.insert(terms.end(), inst.begin() + 1, inst.end());
  return inst[0];
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
