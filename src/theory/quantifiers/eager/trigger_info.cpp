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

#include "theory/quantifiers/eager/trigger_info.h"

#include "expr/node_algorithm.h"
#include "expr/subs.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/eager/quant_info.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_database_eager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

std::ostream& operator<<(std::ostream& out, TriggerStatus s)
{
  switch (s)
  {
    case TriggerStatus::NONE: out << "NONE"; break;
    case TriggerStatus::INACTIVE: out << "INACTIVE"; break;
    case TriggerStatus::WAIT: out << "WAIT"; break;
    case TriggerStatus::ACTIVE: out << "ACTIVE"; break;
  }
  return out;
}

TriggerInfo::TriggerInfo(TermDbEager& tde)
    : d_tde(tde),
      d_arity(0),
      d_root{nullptr, nullptr},
      d_status(tde.getSatContext(), TriggerStatus::INACTIVE),
      d_hasActivated(false)
{
}

void TriggerInfo::watch(QuantInfo* qi, const std::vector<Node>& vlist)
{
  if (d_ieval == nullptr)
  {
    const Options& opts = d_tde.getEnv().getOptions();
    ieval::TermEvaluatorMode tev = opts.quantifiers.eagerInstProp
                                       ? ieval::TermEvaluatorMode::PROP
                                       : ieval::TermEvaluatorMode::CONFLICT;
    // initialize the evaluator if not already done so
    d_ieval.reset(new ieval::InstEvaluator(d_tde.getEnv(),
                                           d_tde.getState(),
                                           d_tde.getTermDb(),
                                           tev,
                                           false,
                                           false,
                                           false,
                                           true));
  }
  else
  {
    // otherwise, ensure we are reset
    d_ieval->resetAll(false);
  }
  Node q = qi->getQuant();
  Assert(q.getKind() == Kind::FORALL);
  Assert(vlist.size() == q[0].getNumChildren());
  Subs s;
  for (size_t i = 0, nvars = vlist.size(); i < nvars; i++)
  {
    s.add(q[0][i], vlist[i]);
  }
  // rename quantified formula based on the variable list
  Node qs = s.apply(q);
  // this should probably always hold, or else we have a duplicate trigger
  // for the same quantified formula.
  if (d_quantMap.find(qs) == d_quantMap.end())
  {
    d_ieval->watch(qs);
  }
  // update it to most recent?
  d_quantMap[qs] = q;
  d_quantRMap[q] = qs;
  // a quantified formula may be signed up to watch the same term from
  // different vars, e.g. P(v1,v2) for forall xy. P(x,y) V P(y,x) V Q(x,y).
  if (std::find(d_qinfos.begin(), d_qinfos.end(), qi) == d_qinfos.end())
  {
    d_qinfos.emplace_back(qi);
  }
  Trace("eager-inst-debug2")
      << "Add quant " << q << " to " << d_pattern << std::endl;
}

void TriggerInfo::initialize(const Node& t, const std::vector<Node>& mts)
{
  d_pattern = t;
  d_op = d_tde.getTermDb().getMatchOperator(t);
  d_arity = t.getNumChildren();
  for (size_t i = 0; i < 2; i++)
  {
    bool bindOrder = (i == 0);
    PatTermInfo* pi = getPatTermInfo(t, bindOrder);
    std::unordered_set<Node> fvs;
    pi->initialize(this, t, fvs, bindOrder, true);
    d_root[i] = pi;
    if (i == 0)
    {
      // if we are a multi-trigger, initialize the additional patterns now
      for (const Node& m : mts)
      {
        // we use bindOrder = true, since we will be matching all
        pi = getPatTermInfo(m, bindOrder);
        pi->initialize(this, m, fvs, true, true);
        d_mroots.emplace_back(pi);
      }
      if (pi->d_oargs.empty() && pi->d_gpargs.empty())
      {
        // if simple trigger, the binding order doesn't make a difference
        d_root[1] = pi;
        break;
      }
    }
  }
}

bool TriggerInfo::doMatching(TNode t)
{
  Stats& stats = d_tde.getStats();
  ++(stats.d_matches);
  Trace("eager-inst-matching")
      << "doMatching " << d_pattern << " " << t << std::endl;
  Assert(d_ieval != nullptr);
  Assert(t.getNumChildren() == d_pattern.getNumChildren());
  Assert(t.getOperator() == d_pattern.getOperator());
  if (!resetMatching())
  {
    Trace("eager-inst-matching-debug") << "...failed reset" << std::endl;
    return false;
  }
  if (!d_root[1]->doMatching(d_ieval.get(), t))
  {
    Trace("eager-inst-matching-debug") << "...failed matching" << std::endl;
    return false;
  }
  // add instantiation(s)
  bool isConflict = false;
  std::vector<Node> qinsts = d_ieval->getActiveQuants(isConflict);
  Trace("eager-inst-matching-debug")
      << "...success, #quant=" << qinsts.size() << ", conflict=" << isConflict
      << std::endl;
  if (qinsts.empty())
  {
    return false;
  }
  ++(stats.d_matchesSuccess);
  if (isConflict)
  {
    ++(stats.d_matchesSuccessConflict);
  }
  std::map<Node, Node>::iterator itq;
  for (const Node& q : qinsts)
  {
    std::vector<Node> inst = d_ieval->getInstantiationFor(q);
    processInstantiation(q, inst, isConflict);
  }
  return isConflict;
}

bool TriggerInfo::doMatchingAll()
{
  Stats& stats = d_tde.getStats();
  ++(stats.d_matchesAll);
  ++(stats.d_matches);
  Trace("eager-inst-matching") << "doMatchingAll " << d_pattern << std::endl;
  Assert(d_ieval != nullptr);
  if (!resetMatching())
  {
    Trace("eager-inst-matching-debug")
        << "...doMatchingAll failed reset" << std::endl;
    return false;
  }
  FunInfo* finfo = d_tde.getFunInfo(d_op);
  QuantifiersState& qs = d_tde.getState();
  CDTNodeTrieIterator itt(d_tde.getCdtAlloc(), qs, finfo->getTrie(), d_arity);
  PatTermInfo* root = d_root[0];
  // found an instantiation, we will sanitize it based on the actual term,
  // to ensure the match post-instantiation is syntactic.
  while (root->doMatchingAll(d_ieval.get(), itt))
  {
    bool isConflict = false;
    std::vector<Node> qinsts = d_ieval->getActiveQuants(isConflict);
    if (qinsts.empty())
    {
      Assert(false);
      Trace("eager-inst-matching-debug")
          << "...doMatchingAll no quants" << std::endl;
    }
    else
    {
      ++(stats.d_matchesSuccess);
      if (isConflict)
      {
        ++(stats.d_matchesSuccessConflict);
      }
      Trace("eager-inst-matching-debug")
          << "...doMatchingAll success, #quant=" << qinsts.size()
          << ", conflict=" << isConflict << std::endl;
      // compute the backwards map
      TNode data = itt.getCurrentData();
      Assert(data.getNumChildren() == d_pattern.getNumChildren());
      std::map<Node, Node> varToTerm;
      std::vector<size_t>& vargs = root->d_vargs;
      for (size_t v : vargs)
      {
        Assert(v < d_pattern.getNumChildren());
        varToTerm[d_pattern[v]] = data[v];
      }
      std::map<Node, Node>::iterator it;
      for (const Node& qi : qinsts)
      {
        std::vector<Node> inst;
        for (const Node& v : qi[0])
        {
          it = varToTerm.find(v);
          if (it != varToTerm.end())
          {
            inst.emplace_back(it->second);
          }
          else
          {
            inst.emplace_back(d_ieval->get(v));
          }
        }
        processInstantiation(qi, inst, isConflict);
      }
      if (isConflict)
      {
        Trace("eager-inst-matching-debug")
            << "...doMatchingAll conflict" << std::endl;
        return true;
      }
    }
    // pop the leaf and match again
    itt.pop();
  }
  Trace("eager-inst-matching-debug")
      << "...doMatchingAll finished" << std::endl;
  return false;
}

PatTermInfo* TriggerInfo::getPatTermInfo(TNode p, bool bindOrder)
{
  std::map<TNode, PatTermInfo>& pi = d_pinfo[bindOrder ? 1 : 0];
  std::map<TNode, PatTermInfo>::iterator it = pi.find(p);
  if (it == pi.end())
  {
    pi.emplace(p, d_tde);
    it = pi.find(p);
  }
  return &it->second;
}

bool TriggerInfo::resetMatching()
{
  Trace("eager-inst-debug") << "Reset matching" << std::endl;
  // reset the assignment completely
  d_ieval->resetAll(false);
  // now, ensure we don't watch quantified formulas that are no longer asserted
  bool success = false;
  for (QuantInfo* qi : d_qinfos)
  {
    Node q = qi->getQuant();
    Assert(d_quantRMap.find(q) != d_quantRMap.end())
        << "Unknown quant " << q << " for " << d_pattern << std::endl;
    bool isActive = qi->isAsserted();
    d_ieval->setActive(d_quantRMap[q], isActive);
    Trace("eager-inst-debug")
        << "setActive " << q << " : " << isActive << std::endl;
    success = success || isActive;
  }
  Assert(success == d_ieval->isFeasible());
  // success if at least one is asserted
  return success;
}

bool TriggerInfo::notifyTerm(TNode t, bool isAsserted)
{
  // Do the matching against term t, only if it is marked as asserted.
  // This may be notified when
  // (1) t is a new eqc and eagerInstWhenAsserted is false.
  // (2) t appears as a (subterm of a) term in a merge and eagerInstWhenAsserted
  // is true.
  if (d_status.get() == TriggerStatus::ACTIVE && isAsserted)
  {
    return doMatching(t);
  }
  return false;
}

void TriggerInfo::setStatus(TriggerStatus s)
{
  d_status = s;
  Trace("eager-inst-status")
      << "Set status " << d_pattern << " to " << s << std::endl;
  if (s == TriggerStatus::ACTIVE && !d_hasActivated)
  {
    d_hasActivated = true;
    ++(d_tde.getStats().d_ntriggersActivated);
  }
}

void TriggerInfo::processInstantiation(const Node& q,
                                       std::vector<Node>& inst,
                                       bool isConflict)
{
  Node ent = d_ieval->getEntailedValue(q[1]);
  Trace("eager-inst-ent") << "For " << q << " " << inst << std::endl;
  Trace("eager-inst-ent") << "...entailed term is " << ent << std::endl;
  std::map<Node, Node>::iterator itq = d_quantMap.find(q);
  Assert(itq != d_quantMap.end());
  d_tde.addInstantiation(itq->second, inst, ent, isConflict);
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
