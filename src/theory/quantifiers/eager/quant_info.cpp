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
    : d_tde(tde),
      d_asserted(tde.getSatContext()),
      d_tinactiveIndex(tde.getSatContext(), 0),
      d_tstatus(tde.getSatContext(), TriggerStatus::NONE)
{
}

void QuantInfo::initialize(QuantifiersRegistry& qr, const Node& q)
{
  Assert(d_quant.isNull());
  Assert(q.getKind() == Kind::FORALL);
  d_quant = q;
  // TODO: if we have a nested quantified, don't bother
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
  // TODO: could aggressively merge triggers

  Trace("eager-inst-trigger") << "Triggers for " << q << ":" << std::endl;
  size_t nvars = q[0].getNumChildren();
  std::unordered_set<Node> processed;
  for (const Node& p : patTerms)
  {
    Trace("eager-inst-trigger") << "  * " << p << std::endl;
    inst::TriggerTermInfo& tip = tinfo[p];
    // must be a single trigger
    if (tip.d_fv.size() != nvars)
    {
      continue;
    }
    // TODO: could use the polarity information in tip to initialize the trigger
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
    d_vlists.emplace_back();
    std::vector<Node>& vlist = d_vlists.back();
    for (const Node& v : q[0])
    {
      Assert(visited.find(v) != visited.end());
      vlist.emplace_back(visited[v]);
    }
    d_triggers.emplace_back(ti);
    d_triggerWatching.emplace_back(false);
    ++(s.d_ntriggers);
  }
  Trace("eager-inst-trigger") << "#triggers=" << d_triggers.size() << std::endl;
  if (d_triggers.empty())
  {
    ++(s.d_nquantNoTrigger);
  }
  else
  {
    d_tstatus = TriggerStatus::INACTIVE;
  }
}

bool QuantInfo::notifyAsserted()
{
  Assert(!d_asserted.get());
  d_asserted = true;
  return updateStatus();
}

bool QuantInfo::notifyTriggerStatus(TriggerInfo* tinfo, TriggerStatus status)
{
  // if we are inactive and we just updated the inactive trigger, update status
  if (d_tstatus == TriggerStatus::INACTIVE)
  {
    Assert(d_tinactiveIndex.get() < d_triggers.size());
    if (d_triggers[d_tinactiveIndex.get()] == tinfo)
    {
      return updateStatus();
    }
  }
  return false;
}

bool QuantInfo::updateStatus()
{
  if (d_tstatus != TriggerStatus::INACTIVE)
  {
    // nothing to do
    return false;
  }
  Assert(d_tinactiveIndex.get() < d_triggers.size());
  do
  {
    TriggerInfo* tnext = d_triggers[d_tinactiveIndex.get()];
    if (tnext->getStatus() == TriggerStatus::INACTIVE)
    {
      // the current trigger is still inactive
      return false;
    }
    d_tinactiveIndex = d_tinactiveIndex.get() + 1;
  } while (d_tinactiveIndex.get() < d_triggers.size());

  // TODO: activate all policy?

  Trace("eager-inst-debug") << "Activate quant: " << d_quant << std::endl;
  // we are at the end, choose a trigger to activate
  d_tstatus = TriggerStatus::ACTIVE;
  size_t minTerms = 0;
  size_t bestIndex = 0;
  bool bestIndexSet = false;
  for (size_t i = 0, ntriggers = d_triggers.size(); i < ntriggers; i++)
  {
    TriggerInfo* tinfo = d_triggers[i];
    TriggerStatus s = tinfo->getStatus();
    Assert(s != TriggerStatus::INACTIVE);
    if (s == TriggerStatus::ACTIVE)
    {
      bestIndex = i;
      break;
    }
    else
    {
      Node op = tinfo->getOperator();
      FunInfo* finfo = d_tde.getFunInfo(op);
      size_t cterms = finfo->getNumTerms();
      if (!bestIndexSet || cterms < minTerms)
      {
        bestIndex = i;
        minTerms = cterms;
      }
      bestIndexSet = true;
    }
  }
  Assert(d_triggers.size() == d_vlists.size());
  Assert(d_triggers.size() == d_triggerWatching.size());
  TriggerInfo* bestTrigger = d_triggers[bestIndex];
  // ensure we are signed up to watch
  if (!d_triggerWatching[bestIndex])
  {
    Trace("eager-inst-debug")
        << "Add to watch " << bestTrigger->getPattern() << std::endl;
    d_triggerWatching[bestIndex] = true;
    bestTrigger->watch(this, d_vlists[bestIndex]);
  }
  // activate the best trigger
  if (bestTrigger->setStatus(TriggerStatus::ACTIVE))
  {
    return true;
  }
  // match all
  return bestTrigger->doMatchingAll();
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
