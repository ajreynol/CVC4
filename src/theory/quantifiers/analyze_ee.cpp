/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevant domain class.
 */

#include "theory/quantifiers/analyze_ee.h"

#include "theory/quantifiers/quantifiers_state.h"
#include "theory/uf/equality_engine.h"
#include "theory/quantifiers/term_registry.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

AnalyzeEqualityEngine::AnalyzeEqualityEngine(Env& env,
                QuantifiersState& qs,
                QuantifiersRegistry& qr,
                TermRegistry& tr) : QuantifiersUtil(env), d_qs(qs), d_qreg(qr), d_treg(tr) {}
AnalyzeEqualityEngine::~AnalyzeEqualityEngine() {}

bool AnalyzeEqualityEngine::reset(Theory::Effort e)
{
  if (e!=Theory::Effort::EFFORT_FULL && e!=Theory::Effort::EFFORT_LAST_CALL)
  {
    return true;
  }
  std::vector<Node> allTerms;
  TermDb* tdb = d_treg.getTermDatabase();
  size_t addEqc = 0;
  size_t changeEqc = 0;
  size_t unchangeEqc = 0;
  std::unordered_set<Node> unchangedEqc;
  size_t remEqc = 0;
  Trace("analyze-ee") << "Analyze equality engine" << std::endl;
  std::unordered_set<Node> esNew;
  eq::EqualityEngine* ee = d_qs.getEqualityEngine();
  eq::EqClassesIterator eqcs2_i = eq::EqClassesIterator(ee);
  while (!eqcs2_i.isFinished())
  {
    Node eqc = (*eqcs2_i);
    ++eqcs2_i;
    std::vector<Node> etermsNew;
    eq::EqClassIterator eqc2_i = eq::EqClassIterator(eqc, ee);
    while (!eqc2_i.isFinished())
    {
      Node n = (*eqc2_i);
      ++eqc2_i;
      if (!tdb->hasTermCurrent(n))
      {
        continue;
      }
      etermsNew.emplace_back(n);
      allTerms.push_back(n);
    }
    if (etermsNew.empty())
    {
      // no relevant terms
      continue;
    }
    esNew.insert(eqc);
    EqcInfo& ei = d_einfo[eqc];
    bool wasNew = false;
    if (ei.d_terms.empty())
    {
      Trace("analyze-ee-debug") << "  New eqc: " << eqc << std::endl;
      wasNew = true;
    }
    bool changed = false;
    if (!wasNew)
    {
      std::sort(etermsNew.begin(), etermsNew.end());
      for (size_t i=0; i<2; i++)
      {
        std::vector<Node>& v1 = i==0 ? ei.d_terms : etermsNew;
        std::vector<Node>& v2 = i==1 ? ei.d_terms : etermsNew;
        std::vector<Node> diff;
        std::set_difference(v1.begin(), v1.end(), v2.begin(), v2.end(),
            std::inserter(diff, diff.begin()));
        if (!diff.empty())
        {
          Trace("analyze-ee-debug") << "  Diff (" << (i==0 ? "remove) " : "add) ") << eqc << ": " << diff << std::endl;
          changed = true;
        }
      }
    }
    ei.d_terms = etermsNew;
    if (wasNew)
    {
      addEqc++;
    }
    else if (changed)
    {
      changeEqc++;
    }
    else
    {
      unchangeEqc++;
      unchangedEqc.insert(eqc);
    }
  }
  for (const Node& eqc : d_es)
  {
    if (esNew.find(eqc)==esNew.end())
    {
      Trace("analyze-ee-debug") << "  Delete eqc: " << eqc << std::endl;
      d_einfo.erase(eqc);
      remEqc++;
    }
  }
  Trace("analyze-ee") << "Add/unchange/change/rem eqc: " << addEqc << "/" << unchangeEqc << "/" << changeEqc << "/" << remEqc << std::endl;
  d_es = esNew;
  size_t unchangedTerms = 0;
  size_t changedTerms = 0;
  for (const Node& n : allTerms)
  {
    if (tdb->getMatchOperator(n).isNull())
    {
      continue;
    }
    bool changed = false;
    for (const Node& nc : n)
    {
      if (!ee->hasTerm(nc))
      {
        continue;
      }
      Node r = ee->getRepresentative(nc);
      if (unchangedEqc.find(r)==unchangedEqc.end())
      {
        changed = true;
        break;
      }
    }
    if (changed)
    {
      changedTerms++;
    }
    else
    {
      unchangedTerms++;
    }
  }
  Trace("analyze-ee") << "Unchanged/changed terms: " << unchangedTerms << "/" << changedTerms << std::endl;
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
