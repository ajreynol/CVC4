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

#include "theory/quantifiers/eager/quant_info.h"

#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

namespace eager {

QuantInfo::QuantInfo(context::Context* c) {}

void QuantInfo::initialize(QuantifiersRegistry& qr,
                           TermDbEager& tde,
                           const Node& q)
{
  Assert(q.getKind() == Kind::FORALL);
  Stats& s = tde.getStats();
  ++(s.d_nquant);
  expr::TermCanonize& canon = tde.getTermCanon();
  inst::PatternTermSelector pts(q, options::TriggerSelMode::MAX);
  std::vector<Node> patTerms;
  std::map<Node, inst::TriggerTermInfo> tinfo;
  Node bd = qr.getInstConstantBody(q);
  pts.collect(bd, patTerms, tinfo);
  size_t nvars = q[0].getNumChildren();
  std::unordered_set<Node> processed;
  for (const Node& p : patTerms)
  {
    inst::TriggerTermInfo& tip = tinfo[p];
    // must be a single trigger
    if (tip.d_fv.size() != nvars)
    {
      continue;
    }
    if (processed.find(p) != processed.end())
    {
      // in rare cases there may be a repeated pattern??
      continue;
    }
    processed.insert(p);
    // convert back to bound variables
    Node t = qr.substituteInstConstantsToBoundVariables(p, q);
    // now, canonize
    std::map<TNode, Node> visited;
    Node tc = canon.getCanonicalTerm(t, visited);
    eager::TriggerInfo* ti = tde.getTriggerInfo(tc);
    // get the variable list that we canonized to
    std::vector<Node> vlist;
    for (const Node& v : q[0])
    {
      Assert(visited.find(v) != visited.end());
      vlist.emplace_back(visited[v]);
    }
    ti->watch(q, vlist);
    d_triggers.emplace_back(ti);
    ++(s.d_ntriggers);
  }
  if (d_triggers.empty())
  {
    ++(s.d_nquantNoTrigger);
  }
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
