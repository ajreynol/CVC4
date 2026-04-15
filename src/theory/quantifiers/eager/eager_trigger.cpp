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
 * Eager instantiation trigger utilities.
 */

#include "theory/quantifiers/eager/eager_trigger.h"

#include <algorithm>
#include <vector>

#include "theory/quantifiers/inst_match.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

namespace {

void pushBackUnique(std::vector<Node>& nodes, Node n)
{
  if (std::find(nodes.begin(), nodes.end(), n) == nodes.end())
  {
    nodes.push_back(n);
  }
}

bool isPotentialGroundMatch(QuantifiersState& qstate, TNode a, TNode b)
{
  if (a == b || qstate.areEqual(a, b))
  {
    return true;
  }
  if (a.getType() != b.getType() || a.getType().isBoolean()
      || a.getType().isFunction() || (a.isConst() && b.isConst())
      || qstate.areDisequal(a, b))
  {
    return false;
  }
  Trace("eager-inst-debug")
      << "EagerInst: potential ground match " << a << " ~ " << b << std::endl;
  return true;
}

bool matchPattern(Node q,
                  TermDb& tdb,
                  QuantifiersState& qstate,
                  const TermDatabase& termDb,
                  TNode pat,
                  TNode t,
                  InstMatch& m,
                  std::vector<size_t>& assigned)
{
  if (pat.getKind() == Kind::INST_CONSTANT
      && TermUtil::getInstConstAttr(pat) == q)
  {
    size_t vn = pat.getAttribute(InstVarNumAttribute());
    bool wasSet = !m.get(vn).isNull();
    if (!m.set(vn, t))
    {
      return false;
    }
    if (!wasSet)
    {
      assigned.push_back(vn);
    }
    return !qstate.isInConflict();
  }
  if (!TermUtil::hasInstConstAttr(pat))
  {
    return isPotentialGroundMatch(qstate, pat, t);
  }
  Node pop = tdb.getMatchOperator(pat);
  if (!pop.isNull() && tdb.getMatchOperator(t) != pop)
  {
    const NodeList* gts = termDb.getGroundTerms(pop);
    if (gts == nullptr)
    {
      return false;
    }
    for (const Node& gt : gts->d_list)
    {
      if (!isPotentialGroundMatch(qstate, gt, t))
      {
        continue;
      }
      size_t startAssigned = assigned.size();
      if (matchPattern(q, tdb, qstate, termDb, pat, gt, m, assigned))
      {
        return true;
      }
      while (assigned.size() > startAssigned)
      {
        size_t i = assigned.back();
        assigned.pop_back();
        m.reset(i);
      }
    }
    return false;
  }
  if (pat.getKind() != t.getKind()
      || pat.getNumChildren() != t.getNumChildren())
  {
    return false;
  }
  if (pat.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    if (t.getMetaKind() != kind::metakind::PARAMETERIZED
        || pat.getOperator() != t.getOperator())
    {
      return false;
    }
  }
  else if (t.getMetaKind() == kind::metakind::PARAMETERIZED)
  {
    return false;
  }
  for (size_t i = 0, nchild = pat.getNumChildren(); i < nchild; i++)
  {
    if (!matchPattern(q, tdb, qstate, termDb, pat[i], t[i], m, assigned))
    {
      return false;
    }
  }
  return true;
}

void addInstantiations(QuantifiersState& qstate,
                       QuantifiersInferenceManager& qim,
                       TermDb& tdb,
                       const TermDatabase& termDb,
                       Node q,
                       const TriggerInfo& ti,
                       size_t pindex,
                       InstMatch& m,
                       std::vector<size_t>& assigned,
                       uint64_t& addedLemmas)
{
  if (pindex == ti.d_patterns.size())
  {
    if (!m.isComplete())
    {
      return;
    }
    std::vector<Node> terms(m.get().begin(), m.get().end());
    if (qim.getInstantiate()->addInstantiation(
            q, terms, InferenceId::QUANTIFIERS_INST_EAGER_INST, ti.d_pfArg))
    {
      addedLemmas++;
    }
    return;
  }
  const PatternInfo& pi = ti.d_patterns[pindex];
  const NodeList* gts = termDb.getGroundTerms(pi.d_op);
  if (gts == nullptr)
  {
    return;
  }
  for (const Node& gt : gts->d_list)
  {
    size_t startAssigned = assigned.size();
    if (matchPattern(q, tdb, qstate, termDb, pi.d_pattern, gt, m, assigned))
    {
      addInstantiations(qstate,
                        qim,
                        tdb,
                        termDb,
                        q,
                        ti,
                        pindex + 1,
                        m,
                        assigned,
                        addedLemmas);
    }
    while (assigned.size() > startAssigned)
    {
      size_t i = assigned.back();
      assigned.pop_back();
      m.reset(i);
    }
    if (qstate.isInConflict())
    {
      break;
    }
  }
}

}  // namespace

bool getPatternInfo(TermDb& tdb, Node q, Node pat, PatternInfo& pinfo)
{
  if (!TermUtil::hasInstConstAttr(pat))
  {
    return false;
  }
  pinfo.d_pattern = pat;
  pinfo.d_op = tdb.getMatchOperator(pat);
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
    if (cur != pat)
    {
      Node op = tdb.getMatchOperator(cur);
      if (!op.isNull())
      {
        pushBackUnique(pinfo.d_mergeOps, op);
      }
      std::vector<Node> gvars;
      TermUtil::computeInstConstContainsForQuant(q, cur, gvars);
      if (gvars.empty() && !cur.getType().isFunction())
      {
        pushBackUnique(pinfo.d_groundTerms, cur);
      }
    }
    if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
    {
      visit.push_back(cur.getOperator());
    }
    visit.insert(visit.end(), cur.begin(), cur.end());
  }
  return !pinfo.d_vars.empty();
}

void addInstantiations(Env& env,
                       QuantifiersState& qstate,
                       QuantifiersInferenceManager& qim,
                       TermRegistry& treg,
                       TermDb& tdb,
                       const TermDatabase& termDb,
                       Node q,
                       const TriggerInfo& ti,
                       uint64_t& addedLemmas)
{
  InstMatch m(env, qstate, treg, q);
  m.setEvaluatorMode(ieval::TermEvaluatorMode::NO_ENTAIL);
  std::vector<size_t> assigned;
  addInstantiations(
      qstate, qim, tdb, termDb, q, ti, 0, m, assigned, addedLemmas);
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
