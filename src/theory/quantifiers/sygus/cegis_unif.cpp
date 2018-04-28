/*********************                                                        */
/*! \file cegis_unif.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Haniel Barbosa
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2018 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief implementation of class for cegis with unification techniques
 **/

#include "theory/quantifiers/sygus/cegis_unif.h"

#include "theory/quantifiers/sygus/ce_guided_conjecture.h"
#include "theory/quantifiers/sygus/sygus_unif_rl.h"
#include "theory/quantifiers/sygus/term_database_sygus.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

CegisUnif::CegisUnif(QuantifiersEngine* qe, CegConjecture* p)
    : SygusModule(qe, p)
{
  d_tds = d_qe->getTermDatabaseSygus();
}

CegisUnif::~CegisUnif() {}
bool CegisUnif::initialize(Node n,
                           const std::vector<Node>& candidates,
                           std::vector<Node>& lemmas)
{
  Trace("cegis-unif") << "Initialize CegisUnif : " << n << std::endl;
  Assert(candidates.size() > 0);
  if (candidates.size() > 1)
  {
    return false;
  }
  d_candidate = candidates[0];
  Trace("cegis-unif") << "Initialize unif utility for " << d_candidate
                      << "...\n";
  d_sygus_unif.initialize(d_qe, d_candidate, d_enums, lemmas);
  Assert(!d_enums.empty());
  Trace("cegis-unif") << "Initialize " << d_enums.size() << " enumerators for "
                      << d_candidate << "...\n";
  /* initialize the enumerators */
  for (const Node& e : d_enums)
  {
    d_tds->registerEnumerator(e, d_candidate, d_parent, true);
    Node g = d_tds->getActiveGuardForEnumerator(e);
    d_enum_to_active_guard[e] = g;
  }
  return true;
}

void CegisUnif::getTermList(const std::vector<Node>& candidates,
                            std::vector<Node>& terms)
{
  Assert(candidates.size() == 1);
  Valuation& valuation = d_qe->getValuation();
  for (const Node& e : d_enums)
  {
    Assert(d_enum_to_active_guard.find(e) != d_enum_to_active_guard.end());
    Node g = d_enum_to_active_guard[e];
    /* Get whether the active guard for this enumerator is if so, then there may
       exist more values for it, and hence we add it to terms. */
    Node gstatus = valuation.getSatValue(g);
    if (!gstatus.isNull() && gstatus.getConst<bool>())
    {
      terms.push_back(e);
    }
  }
}

bool CegisUnif::constructCandidates(const std::vector<Node>& enums,
                                    const std::vector<Node>& enum_values,
                                    const std::vector<Node>& candidates,
                                    std::vector<Node>& candidate_values,
                                    std::vector<Node>& lems)
{
  Assert(enums.size() == enum_values.size());
  if (enums.empty())
  {
    return false;
  }
  unsigned min_term_size = 0;
  std::vector<unsigned> enum_consider;
  Trace("cegis-unif-enum") << "Register new enumerated values :\n";
  for (unsigned i = 0, size = enums.size(); i < size; ++i)
  {
    Trace("cegis-unif-enum") << "  " << enums[i] << " -> " << enum_values[i]
                             << std::endl;
    unsigned sz = d_tds->getSygusTermSize(enum_values[i]);
    if (i == 0 || sz < min_term_size)
    {
      enum_consider.clear();
      min_term_size = sz;
      enum_consider.push_back(i);
    }
    else if (sz == min_term_size)
    {
      enum_consider.push_back(i);
    }
  }
  /* only consider the enumerators that are at minimum size (for fairness) */
  Trace("cegis-unif-enum") << "...register " << enum_consider.size() << " / "
                           << enums.size() << std::endl;
  NodeManager* nm = NodeManager::currentNM();
  for (unsigned i = 0, ecsize = enum_consider.size(); i < ecsize; ++i)
  {
    unsigned j = enum_consider[i];
    Node e = enums[j];
    Node v = enum_values[j];
    std::vector<Node> enum_lems;
    d_sygus_unif.notifyEnumeration(e, v, enum_lems);
    /* the lemmas must be guarded by the active guard of the enumerator */
    Assert(d_enum_to_active_guard.find(e) != d_enum_to_active_guard.end());
    Node g = d_enum_to_active_guard[e];
    for (unsigned j = 0, size = enum_lems.size(); j < size; ++j)
    {
      enum_lems[j] = nm->mkNode(OR, g.negate(), enum_lems[j]);
    }
    lems.insert(lems.end(), enum_lems.begin(), enum_lems.end());
  }
  /* build candidate solution */
  Assert(candidates.size() == 1);
  Node vc = d_sygus_unif.constructSolution();
  if (vc.isNull())
  {
    return false;
  }
  candidate_values.push_back(vc);
  return true;
}

Node CegisUnif::purifyLemma(Node n,
                            bool ensureConst,
                            std::vector<Node>& model_guards,
                            BoolNodePairMap& cache)
{
  Trace("cegis-unif-purify") << "PurifyLemma : " << n << "\n";
  BoolNodePairMap::const_iterator it = cache.find(BoolNodePair(ensureConst, n));
  if (it != cache.end())
  {
    Trace("cegis-unif-purify") << "... already visited " << n << "\n";
    return it->second;
  }
  /* Recurse */
  unsigned size = n.getNumChildren();
  Kind k = n.getKind();
  bool fapp = k == APPLY_UF && size > 0 && n[0] == d_candidate;
  bool childChanged = false;
  std::vector<Node> children;
  for (unsigned i = 0; i < size; ++i)
  {
    if (i == 0 && fapp)
    {
      children.push_back(n[0]);
      continue;
    }
    Node child = purifyLemma(n[i], ensureConst || fapp, model_guards, cache);
    children.push_back(child);
    childChanged = childChanged || child != n[i];
  }
  Node nb;
  if (childChanged)
  {
    if (n.hasOperator())
    {
      children.insert(children.begin(), n.getOperator());
    }
    nb = NodeManager::currentNM()->mkNode(k, children);
    Trace("cegis-unif-purify") << "PurifyLemma : transformed " << n << " into "
                               << nb << "\n";
  }
  else
  {
    nb = n;
  }
  /* get model value of non-top level applications of d_candidate */
  if (ensureConst && fapp)
  {
    Node nv = d_parent->getModelValue(nb);
    Trace("cegis-unif-purify") << "PurifyLemma : model value for " << nb
                               << " is " << nv << "\n";
    /* test if different, then update model_guards */
    if (nv != nb)
    {
      Trace("cegis-unif-purify") << "PurifyLemma : adding model eq\n";
      model_guards.push_back(
          NodeManager::currentNM()->mkNode(EQUAL, nv, nb).negate());
      nb = nv;
    }
  }
  nb = Rewriter::rewrite(nb);
  /* every non-top level application of function-to-synthesize must be reduced
     to a concrete constant */
  Assert(!ensureConst || nb.isConst());
  Trace("cegis-unif-purify") << "... caching [" << n << "] = " << nb << "\n";
  cache[BoolNodePair(ensureConst, n)] = nb;
  return nb;
}

void CegisUnif::registerRefinementLemma(const std::vector<Node>& vars,
                                        Node lem,
                                        std::vector<Node>& lems)
{
  Node plem;
  std::vector<Node> model_guards;
  BoolNodePairMap cache;
  Trace("cegis-unif") << "Registering lemma at CegisUnif : " << lem << "\n";
  /* Make the purified lemma which will guide the unification utility. */
  plem = purifyLemma(lem, false, model_guards, cache);
  if (!model_guards.empty())
  {
    model_guards.push_back(plem);
    plem = NodeManager::currentNM()->mkNode(OR, model_guards);
  }
  plem = Rewriter::rewrite(plem);
  Trace("cegis-unif") << "Purified lemma : " << plem << "\n";
  d_refinement_lemmas.push_back(plem);
  /* Notify lemma to unification utility */
  d_sygus_unif.addRefLemma(plem);
  /* Make the refinement lemma and add it to lems. This lemma is guarded by the
     parent's guard, which has the semantics "this conjecture has a solution",
     hence this lemma states: if the parent conjecture has a solution, it
     satisfies the specification for the given concrete point. */
  /* Store lemma for external modules */
  lems.push_back(
      NodeManager::currentNM()->mkNode(OR, d_parent->getGuard().negate(), lem));
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
