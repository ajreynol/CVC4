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

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/ematching/trigger.h"
#include "theory/quantifiers/ematching/trigger_database.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_util.h"

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
      d_trdb(new inst::TriggerDatabase(env, qs, qim, qr, tr)),
      d_hasPendingMerge(false)
{
}

EagerInst::~EagerInst() {}

void EagerInst::presolve() { clearPending(); }

bool EagerInst::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_FULL && hasPendingWork();
}

void EagerInst::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
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
                        << ", pendingMerge = " << d_hasPendingMerge
                        << std::endl;
    for (const std::pair<const Node, bool>& dq : d_dirtyQuants)
    {
      std::map<Node, QuantInfo>::const_iterator it = d_qinfo.find(dq.first);
      if (it == d_qinfo.end())
      {
        continue;
      }
      size_t ngt = 0;
      for (const Node& op : it->second.d_watchedOps)
      {
        ngt += getTermDatabase()->getNumGroundTerms(op);
      }
      Trace("eager-inst") << "  dirty quant " << dq.first << ", triggers="
                          << it->second.d_triggers.size()
                          << ", watchedOps=" << it->second.d_watchedOps.size()
                          << ", groundTerms=" << ngt << std::endl;
    }
  }
  for (const std::pair<const Node, bool>& dq : d_dirtyQuants)
  {
    Node q = dq.first;
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
      if (ti.d_trigger == nullptr)
      {
        continue;
      }
      ti.d_trigger->reset(Node::null());
      ti.d_trigger->addInstantiations();
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
  if (e < Theory::EFFORT_FULL)
  {
    return;
  }
  for (std::pair<const Node, QuantInfo>& qi : d_qinfo)
  {
    for (TriggerInfo& ti : qi.second.d_triggers)
    {
      if (ti.d_trigger != nullptr)
      {
        ti.d_trigger->resetInstantiationRound();
      }
    }
  }
  if (!d_hasPendingMerge)
  {
    return;
  }
  // A merge can potentially change the viability of every stored trigger. We
  // conservatively mark all watched quantifiers dirty and let later matching
  // code decide what to revisit.
  for (const std::pair<const Node, QuantInfo>& qi : d_qinfo)
  {
    markQuantifierDirty(qi.first);
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
  if (d_qinfo.find(q) != d_qinfo.end())
  {
    markQuantifierDirty(q);
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

bool EagerInst::needsNotifyAssertedTerms() const { return false; }

bool EagerInst::needsNotifyMerges() const { return true; }

void EagerInst::notifyAssertedTerm(TNode t)
{
  Node op = getTermDatabase()->getMatchOperator(t);
  if (op.isNull())
  {
    return;
  }
  if (d_opWatchList.find(op) != d_opWatchList.end())
  {
    markOperatorDirty(op);
  }
}

void EagerInst::eqNotifyMerge(CVC5_UNUSED TNode t1, CVC5_UNUSED TNode t2)
{
  if (d_opWatchList.empty())
  {
    return;
  }
  // Any equality merge may enable new matches through congruence or ancestor
  // terms, so we conservatively remember that a merge happened. Later work can
  // refine this to operator- or path-based filtering.
  d_hasPendingMerge = true;
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
    Trace("eager-inst-debug") << "Registered eager-inst watch info for " << q
                              << ", triggers = " << it->second.d_triggers.size()
                              << ", watchedOps = " << it->second.d_watchedOps
                              << std::endl;
  }
}

bool EagerInst::registerTriggerInfo(Node q, const std::vector<Node>& pats)
{
  if (pats.empty())
  {
    return false;
  }
  TriggerInfo ti;
  for (const Node& pat : pats)
  {
    PatternInfo pi;
    if (!getPatternInfo(q, pat, pi))
    {
      return false;
    }
    ti.d_patterns.push_back(pi);
    pushBackUnique(ti.d_watchedOps, pi.d_op);
    for (const Node& v : pi.d_vars)
    {
      pushBackUnique(ti.d_vars, v);
    }
  }
  if (ti.d_vars.size() != d_qreg.getNumInstantiationConstants(q))
  {
    return false;
  }
  ti.d_trigger = d_trdb->mkTrigger(
      q,
      pats,
      true,
      inst::TriggerDatabase::TR_GET_OLD,
      0,
      true,
      InferenceId::QUANTIFIERS_INST_EAGER_INST);
  if (ti.d_trigger == nullptr)
  {
    return false;
  }
  QuantInfo& qi = d_qinfo[q];
  for (const TriggerInfo& qe : qi.d_triggers)
  {
    if (qe.d_trigger == ti.d_trigger)
    {
      return false;
    }
  }
  qi.d_triggers.push_back(ti);
  for (const Node& op : ti.d_watchedOps)
  {
    pushBackUnique(qi.d_watchedOps, op);
    pushBackUnique(d_opWatchList[op], q);
  }
  return true;
}

bool EagerInst::getPatternInfo(Node q, Node pat, PatternInfo& pinfo) const
{
  if (!TermUtil::hasInstConstAttr(pat))
  {
    return false;
  }
  pinfo.d_pattern = pat;
  pinfo.d_op = getTermDatabase()->getMatchOperator(pat);
  if (pinfo.d_op.isNull())
  {
    return false;
  }
  TermUtil::computeInstConstContainsForQuant(q, pat, pinfo.d_vars);
  std::map<Node, size_t> counts;
  std::vector<Node> visit;
  visit.push_back(pat);
  while (!visit.empty())
  {
    Node cur = visit.back();
    visit.pop_back();
    if (cur.getKind() == Kind::INST_CONSTANT
        && TermUtil::getInstConstAttr(cur) == q)
    {
      counts[cur]++;
      if (counts[cur] > 1)
      {
        pinfo.d_hasRepeatedVar = true;
      }
      continue;
    }
    if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      visit.push_back(cur.getOperator());
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  }
  return !pinfo.d_vars.empty();
}

void EagerInst::pushBackUnique(std::vector<Node>& nodes, Node n)
{
  if (std::find(nodes.begin(), nodes.end(), n) == nodes.end())
  {
    nodes.push_back(n);
  }
}

void EagerInst::markOperatorDirty(Node op)
{
  d_dirtyOps[op] = true;
  std::map<Node, std::vector<Node>>::const_iterator it = d_opWatchList.find(op);
  if (it == d_opWatchList.end())
  {
    return;
  }
  for (const Node& q : it->second)
  {
    markQuantifierDirty(q);
  }
}

void EagerInst::markQuantifierDirty(Node q) { d_dirtyQuants[q] = true; }

bool EagerInst::hasPendingWork() const
{
  return d_hasPendingMerge || !d_dirtyOps.empty() || !d_dirtyQuants.empty();
}

void EagerInst::clearPending()
{
  d_dirtyOps.clear();
  d_dirtyQuants.clear();
  d_hasPendingMerge = false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
