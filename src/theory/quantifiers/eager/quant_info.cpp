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

#include "options/quantifiers_options.h"
#include "smt/env.h"
#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

namespace eager {

QuantInfo::QuantInfo(TermDbEager& tde)
    : d_tde(tde), d_asserted(tde.getSatContext())
{
}

void QuantInfo::initialize(QuantifiersRegistry& qr, const Node& q)
{
  Assert(d_quant.isNull());
  Assert(q.getKind() == Kind::FORALL);
  d_quant = q;
  Stats& s = d_tde.getStats();
  ++(s.d_nquant);
  const Options& opts = d_tde.getEnv().getOptions();
  expr::TermCanonize& canon = d_tde.getTermCanon();
  std::map<Node, inst::TriggerTermInfo> tinfo;
  inst::PatternTermSelector pts(q, options::TriggerSelMode::MAX);
  // get the user patterns
  std::vector<Node> userPatTerms;
  options::UserPatMode pmode = opts.quantifiers.userPatternsQuant;
  if (pmode != options::UserPatMode::IGNORE)
  {
    if (q.getNumChildren() == 3)
    {
      for (const Node& p : q[2])
      {
        // only consider single triggers
        if (p.getKind() == Kind::INST_PATTERN && p.getNumChildren() == 1)
        {
          Node patu = pts.getIsUsableTrigger(p[0], q);
          if (!patu.isNull())
          {
            userPatTerms.emplace_back(patu);
          }
        }
      }
    }
  }
  std::vector<Node> patTerms;
  if (userPatTerms.empty()
      || (pmode != options::UserPatMode::TRUST
          && pmode != options::UserPatMode::STRICT))
  {
    // auto-infer the patterns
    Node bd = qr.getInstConstantBody(q);
    pts.collect(bd, patTerms, tinfo);
  }
  for (const Node& up : userPatTerms)
  {
    Node upc = qr.substituteBoundVariablesToInstConstants(up, q);
    if (tinfo.find(upc) != tinfo.end())
    {
      // user pattern also chosen as an auto-pattern
      continue;
    }
    tinfo[upc].init(q, upc);
    patTerms.emplace_back(upc);
  }
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
    eager::TriggerInfo* ti = d_tde.getTriggerInfo(tc);
    // get the variable list that we canonized to
    std::vector<Node> vlist;
    for (const Node& v : q[0])
    {
      Assert(visited.find(v) != visited.end());
      vlist.emplace_back(visited[v]);
    }
    ti->watch(this, vlist);
    d_triggers.emplace_back(ti);
    ++(s.d_ntriggers);
  }
  if (d_triggers.empty())
  {
    ++(s.d_nquantNoTrigger);
  }
}

void QuantInfo::notifyAsserted() { d_asserted = true; }

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal