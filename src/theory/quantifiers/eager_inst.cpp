/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager instantiation.
 */

#include "theory/quantifiers/eager_inst.h"

#include <algorithm>
#include <map>
#include <unordered_set>

#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/eager/eager_trigger.h"
#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/uf/equality_engine_iterator.h"

// #define MULTI_TRIGGER_NEW

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EagerInst::EagerInst(Env& env,
                     QuantifiersState& qs,
                     QuantifiersInferenceManager& qim,
                     QuantifiersRegistry& qr,
                     TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_termDb(context()),
      d_hasPendingMerge(false),
      d_nextTriggerId(0)
{
}

EagerInst::~EagerInst() {}

void EagerInst::presolve() {}

bool EagerInst::needsCheck(Theory::Effort e)
{
  if (TraceIsOn("eager-inst-debug"))
  {
    Trace("eager-inst-debug") << "EagerInst::needsCheck(" << e << ") => "
                              << hasPendingWork() << std::endl;
  }
  return e == Theory::EFFORT_STANDARD && hasPendingWork();
}

void EagerInst::check(Theory::Effort e, QEffort quant_e)
{
  if (e != Theory::EFFORT_STANDARD || quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  beginCallDebug();
  FirstOrderModel* fm = d_treg.getModel();
  if (TraceIsOn("eager-inst"))
  {
    Trace("eager-inst") << "EagerInst::check, effort = " << e
                        << ", #dirtyOps = " << d_dirtyOps.size()
                        << ", #dirtyQuants = " << d_dirtyQuants.size()
                        << ", #dirtyTriggers = " << d_dirtyTriggers.size()
                        << ", pendingMerge = " << d_hasPendingMerge
                        << std::endl;
    std::map<Node, bool> dirtyQuants = d_dirtyQuants;
    for (const std::pair<const Node, bool>& dq : d_dirtyTriggerQuants)
    {
      dirtyQuants[dq.first] = true;
    }
    for (const std::pair<const Node, bool>& dq : dirtyQuants)
    {
      std::map<Node, QuantInfo>::const_iterator it = d_qinfo.find(dq.first);
      if (it == d_qinfo.end())
      {
        continue;
      }
      size_t ngt = 0;
      for (const Node& op : it->second.d_watchedOps)
      {
        ngt += d_termDb.getNumGroundTerms(op);
      }
      Trace("eager-inst") << "  dirty quant " << dq.first
                          << ", triggers=" << it->second.d_triggers.size()
                          << ", watchedOps=" << it->second.d_watchedOps.size()
                          << ", groundTerms=" << ngt << std::endl;
    }
  }
  std::map<Node, bool> dirtyQuants = d_dirtyQuants;
  for (const std::pair<const Node, bool>& dq : d_dirtyTriggerQuants)
  {
    dirtyQuants[dq.first] = true;
  }
  for (const std::pair<const Node, bool>& dq : dirtyQuants)
  {
    Node q = dq.first;
    bool allDirty = d_dirtyQuants.find(q) != d_dirtyQuants.end();
    if (!d_qreg.hasOwnership(q, this) || !fm->isQuantifierAsserted(q)
        || !fm->isQuantifierActive(q))
    {
      continue;
    }
    std::map<Node, QuantInfo>::iterator it = d_qinfo.find(q);
    if (it == d_qinfo.end())
    {
      continue;
    }
    for (TriggerInfo& ti : it->second.d_triggers)
    {
      if (!allDirty && d_dirtyTriggers.find(ti.d_id) == d_dirtyTriggers.end())
      {
        continue;
      }
      uint64_t addedLemmas = 0;
      eager::addInstantiations(d_env,
                               d_qstate,
                               d_qim,
                               d_treg,
                               *getTermDatabase(),
                               d_termDb,
                               q,
                               ti,
                               addedLemmas);
      if (d_qstate.isInConflict())
      {
        break;
      }
    }
    if (d_qstate.isInConflict())
    {
      break;
    }
  }
  clearPending();
  endCallDebug();
}

void EagerInst::reset_round(Theory::Effort e)
{
  if (e != Theory::EFFORT_STANDARD)
  {
    return;
  }
}

void EagerInst::preRegisterQuantifier(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  registerWatchInfo(q);
}

void EagerInst::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  if (TraceIsOn("eager-inst-debug"))
  {
    Trace("eager-inst-debug")
        << "EagerInst::ppNotifyAssertions, #assertions = " << assertions.size()
        << ", watchedOps = " << d_opWatchList.size() << std::endl;
  }
}

void EagerInst::assertNode(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  std::map<Node, QuantInfo>::const_iterator it = d_qinfo.find(q);
  if (it == d_qinfo.end())
  {
    return;
  }
  for (const TriggerInfo& ti : it->second.d_triggers)
  {
    if (isTriggerActive(ti.d_id))
    {
      markTriggerDirty(ti.d_id);
    }
  }
}

void EagerInst::checkOwnership(CVC5_UNUSED Node q)
{
  // TODO: maybe take full ownership if the quantified formula has a trivial
  // trigger which we are complete for?
}

std::string EagerInst::identify() const { return "eager-inst"; }

bool EagerInst::needsNotifyNewClass() const { return true; }

bool EagerInst::needsNotifyMergeTerms() const { return false; }

bool EagerInst::needsNotifyAssertedTerms() const { return true; }

bool EagerInst::needsNotifyMerges() const { return true; }

void EagerInst::notifyAssertedTerm(TNode t) { indexTerms(t); }

void EagerInst::eqNotifyMerge(TNode t1, TNode t2)
{
  if (d_mergeOpWatchList.empty() && d_mergeGroundWatchList.empty()
      && d_mergeParentOpWatchList.empty())
  {
    return;
  }
  bool marked = false;
  if (!d_mergeOpWatchList.empty() || !d_mergeGroundWatchList.empty()
      || !d_mergeParentOpWatchList.empty())
  {
    Node rep = getRepresentative(t1);
    eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
    std::unordered_set<TNode> visited;
    std::vector<TNode> visit;
    if (!rep.isNull() && ee->hasTerm(rep))
    {
      eq::EqClassIterator eqc_i(rep, ee);
      while (!eqc_i.isFinished())
      {
        visit.push_back(*eqc_i);
        ++eqc_i;
      }
    }
    else
    {
      visit.push_back(t1);
      visit.push_back(t2);
    }
    while (!visit.empty())
    {
      TNode cur = visit.back();
      visit.pop_back();
      if (!visited.insert(cur).second)
      {
        continue;
      }
      Node op = getTermDatabase()->getMatchOperator(cur);
      if (!op.isNull())
      {
        std::map<Node, std::vector<uint64_t>>::const_iterator ito =
            d_mergeOpWatchList.find(op);
        if (ito != d_mergeOpWatchList.end())
        {
          for (uint64_t tr : ito->second)
          {
            if (isTriggerActive(tr))
            {
              markTriggerDirty(tr);
              marked = true;
            }
          }
        }
      }
      std::map<Node, std::vector<uint64_t>>::const_iterator itg =
          d_mergeGroundWatchList.find(cur);
      if (itg != d_mergeGroundWatchList.end())
      {
        for (uint64_t tr : itg->second)
        {
          if (isTriggerActive(tr))
          {
            markTriggerDirty(tr);
            marked = true;
          }
        }
      }
      const eager::NodeList* parents = d_termDb.getParentOperators(cur);
      if (parents != nullptr)
      {
        for (const Node& pop : parents->d_list)
        {
          std::map<Node, std::vector<uint64_t>>::const_iterator itmp =
              d_mergeParentOpWatchList.find(pop);
          if (itmp == d_mergeParentOpWatchList.end())
          {
            continue;
          }
          for (uint64_t tr : itmp->second)
          {
            if (isTriggerActive(tr))
            {
              markTriggerDirty(tr);
              marked = true;
            }
          }
        }
      }
      if (!cur.isClosure())
      {
        visit.insert(visit.end(), cur.begin(), cur.end());
      }
    }
  }
  d_hasPendingMerge = d_hasPendingMerge || marked;
}

void EagerInst::registerWatchInfo(Node q)
{
  if (q.getNumChildren() != 3)
  {
    return;
  }
  inst::PatternTermSelector pts(options(), q, options::TriggerSelMode::ALL);
  Node pats = d_qreg.substituteBoundVariablesToInstConstants(q[2], q);
  bool changed = false;
  for (const Node& pat : pats)
  {
    if (pat.getKind() != Kind::INST_PATTERN)
    {
      continue;
    }
    std::vector<Node> nodes;
    for (const Node& p : pat)
    {
      if (std::find(nodes.begin(), nodes.end(), p) != nodes.end())
      {
        continue;
      }
      Node pu = pts.getIsUsableTrigger(p, q);
      if (pu.isNull())
      {
        nodes.clear();
        break;
      }
      nodes.push_back(pu);
    }
    if (!nodes.empty())
    {
      changed = registerTriggerInfo(q, nodes) || changed;
    }
  }
  if (TraceIsOn("eager-inst-debug") && changed)
  {
    std::map<Node, QuantInfo>::const_iterator it = d_qinfo.find(q);
    Assert(it != d_qinfo.end());
    Trace("eager-inst-debug")
        << "Registered eager-inst watch info for " << q
        << ", triggers = " << it->second.d_triggers.size()
        << ", watchedOps = " << it->second.d_watchedOps << std::endl;
  }
}

bool EagerInst::registerTriggerInfo(Node q, const std::vector<Node>& pats)
{
  if (pats.empty())
  {
    return false;
  }
  TriggerInfo ti;
  std::map<Node, size_t> varUseCount;
  for (const Node& pat : pats)
  {
    PatternInfo pi;
    if (!eager::getPatternInfo(*getTermDatabase(), q, pat, pi))
    {
      return false;
    }
    ti.d_patterns.push_back(pi);
    pushBackUnique(ti.d_watchedOps, pi.d_op);
    for (const Node& v : pi.d_vars)
    {
      pushBackUnique(ti.d_vars, v);
      varUseCount[v]++;
    }
    for (const Node& op : pi.d_mergeOps)
    {
      pushBackUnique(ti.d_mergeOps, op);
    }
    for (const Node& gt : pi.d_groundTerms)
    {
      pushBackUnique(ti.d_groundTerms, gt);
    }
    ti.d_needsAnyMerge = ti.d_needsAnyMerge || pi.d_hasRepeatedVar;
  }
  if (ti.d_vars.size() != d_qreg.getNumInstantiationConstants(q))
  {
    return false;
  }
  for (const std::pair<const Node, size_t>& v : varUseCount)
  {
    if (v.second > 1)
    {
      ti.d_needsAnyMerge = true;
      break;
    }
  }
  std::vector<Node> extNodes;
  for (const Node& pat : pats)
  {
    extNodes.push_back(d_qreg.substituteInstConstantsToBoundVariables(pat, q));
  }
  ti.d_pfArg = nodeManager()->mkNode(Kind::SEXPR, extNodes);
  QuantInfo& qi = d_qinfo[q];
  for (const TriggerInfo& qe : qi.d_triggers)
  {
    if (qe.d_pfArg == ti.d_pfArg)
    {
      return false;
    }
  }
  ti.d_id = d_nextTriggerId++;
  d_triggerOwner[ti.d_id] = q;
  d_triggerOps[ti.d_id] = ti.d_watchedOps;
  for (const Node& op : ti.d_mergeOps)
  {
    pushBackUniqueTrigger(d_mergeOpWatchList[op], ti.d_id);
  }
  for (const Node& gt : ti.d_groundTerms)
  {
    pushBackUniqueTrigger(d_mergeGroundWatchList[gt], ti.d_id);
  }
  if (ti.d_needsAnyMerge)
  {
    for (const Node& op : ti.d_watchedOps)
    {
      pushBackUniqueTrigger(d_mergeParentOpWatchList[op], ti.d_id);
    }
  }
  qi.d_triggers.push_back(ti);
  for (const Node& op : ti.d_watchedOps)
  {
    pushBackUnique(qi.d_watchedOps, op);
    pushBackUnique(d_opWatchList[op], q);
    pushBackUniqueTrigger(d_opTriggerWatchList[op], ti.d_id);
  }
  if (isTriggerActive(ti.d_id))
  {
    Trace("eager-inst-debug")
        << "EagerInst: trigger active on registration: " << ti.d_pfArg
        << std::endl;
    markTriggerDirty(ti.d_id);
  }
  return true;
}

void EagerInst::indexTerms(TNode t)
{
  Trace("eager-inst-debug") << "EagerInst::indexTerms " << t << std::endl;
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  visit.push_back(t);
  while (!visit.empty())
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (cur.isClosure() || !visited.insert(cur).second)
    {
      continue;
    }
    Node op = getTermDatabase()->getMatchOperator(cur);
    if (!d_termDb.addTerm(cur, op))
    {
      continue;
    }
    Trace("eager-inst-debug")
        << "  indexed " << cur << ", op=" << op << std::endl;
    if (!op.isNull())
    {
      indexParentOperators(cur);
      if (d_opWatchList.find(op) != d_opWatchList.end())
      {
        Trace("eager-inst-debug") << "  dirty op " << op << std::endl;
        markOperatorDirty(op);
      }
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  }
}

void EagerInst::indexParentOperators(TNode t)
{
  Node op = getTermDatabase()->getMatchOperator(t);
  if (op.isNull())
  {
    return;
  }
  std::unordered_set<TNode> visited;
  std::vector<TNode> visit;
  visit.insert(visit.end(), t.begin(), t.end());
  while (!visit.empty())
  {
    TNode cur = visit.back();
    visit.pop_back();
    if (!visited.insert(cur).second)
    {
      continue;
    }
    d_termDb.addParentOperator(cur, op);
    if (!cur.isClosure())
    {
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  }
}

void EagerInst::pushBackUnique(std::vector<Node>& nodes, Node n)
{
  if (std::find(nodes.begin(), nodes.end(), n) == nodes.end())
  {
    nodes.push_back(n);
  }
}

bool EagerInst::isTriggerActive(uint64_t tr) const
{
  std::map<uint64_t, std::vector<Node>>::const_iterator it =
      d_triggerOps.find(tr);
  if (it == d_triggerOps.end())
  {
    return false;
  }
  for (const Node& op : it->second)
  {
    if (d_termDb.getNumGroundTerms(op) == 0)
    {
      return false;
    }
  }
  return true;
}

void EagerInst::markOperatorDirty(Node op)
{
  d_dirtyOps[op] = true;
  std::map<Node, std::vector<uint64_t>>::const_iterator it =
      d_opTriggerWatchList.find(op);
  if (it == d_opTriggerWatchList.end())
  {
    return;
  }
  for (uint64_t tr : it->second)
  {
    if (isTriggerActive(tr))
    {
      markTriggerDirty(tr);
    }
  }
}

void EagerInst::markTriggerDirty(uint64_t tr)
{
  d_dirtyTriggers[tr] = true;
  std::map<uint64_t, Node>::const_iterator it = d_triggerOwner.find(tr);
  if (it != d_triggerOwner.end())
  {
    d_dirtyTriggerQuants[it->second] = true;
  }
}

bool EagerInst::hasPendingWork() const
{
  return d_hasPendingMerge || !d_dirtyOps.empty() || !d_dirtyQuants.empty()
         || !d_dirtyTriggers.empty();
}

void EagerInst::clearPending()
{
  d_dirtyOps.clear();
  d_dirtyQuants.clear();
  d_dirtyTriggerQuants.clear();
  d_dirtyTriggers.clear();
  d_hasPendingMerge = false;
}

void EagerInst::pushBackUniqueTrigger(std::vector<uint64_t>& triggers,
                                      uint64_t tr)
{
  if (std::find(triggers.begin(), triggers.end(), tr) == triggers.end())
  {
    triggers.push_back(tr);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
