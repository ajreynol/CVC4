/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Andres Noetzli
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Conflict-based conjecture generation
 */

#include "theory/quantifiers/conflict_conjecture_generator.h"

#include "expr/node_algorithm.h"
#include "expr/subs.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/first_order_model.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/term_pools.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_tuple_enumerator.h"
#include "util/random.h"

using namespace cvc5::internal::kind;
using namespace cvc5::context;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

ConflictConjectureGenerator::ConflictConjectureGenerator(
    Env& env,
    QuantifiersState& qs,
    QuantifiersInferenceManager& qim,
    QuantifiersRegistry& qr,
    TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_funDefEvaluator(env),
      d_conjGen(userContext()),
      d_conjGenIndex(userContext()),
      d_conjGenCache(userContext())
{
  d_false = nodeManager()->mkConst(false);
}

void ConflictConjectureGenerator::presolve() {}

bool ConflictConjectureGenerator::needsCheck(Theory::Effort e)
{
  return e >= Theory::EFFORT_LAST_CALL;
}

void ConflictConjectureGenerator::reset_round(Theory::Effort e) {}

void ConflictConjectureGenerator::registerQuantifier(Node q) {}

void ConflictConjectureGenerator::checkOwnership(Node q) {}

QuantifiersModule::QEffort ConflictConjectureGenerator::needsModel(
    Theory::Effort e)
{
  return QEFFORT_STANDARD;
}

void ConflictConjectureGenerator::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  Trace("ccgen") << "ConflictConjectureGenerator: check" << std::endl;
  // update the function definitions
  d_funDefEvaluator.clear();
  quantifiers::FirstOrderModel* model = d_treg.getModel();
  Trace("ccgen-debug") << "Refresh function definitions..." << std::endl;
  std::unordered_set<Node> qsyms;
  std::unordered_set<TNode> qvisited;
  for (size_t i = 0; i < model->getNumAssertedQuantifiers(); i++)
  {
    Node phi = model->getAssertedQuantifier(i);
    Trace("ccgen-debug") << "- quant : " << phi << std::endl;
    if (d_qreg.getQuantAttributes().isFunDef(phi))
    {
      Trace("ccgen-debug") << "  fun def: " << phi << std::endl;
      d_funDefEvaluator.assertDefinition(phi);
    }
    // record symbols
    expr::getSymbols(phi, qsyms, qvisited);
  }
  d_ee = d_qstate.getEqualityEngine();
  d_eqcGen.clear();
  d_eqcGenRec.clear();
  std::vector<Node> candDeq;
  eq::EqClassIterator eqc = eq::EqClassIterator(d_false, d_ee);
  while (!eqc.isFinished())
  {
    Node n = *eqc;
    if (n.getKind() == Kind::EQUAL)
    {
      candDeq.push_back(n);
    }
    ++eqc;
  }

  Trace("ccgen") << "...found " << candDeq.size() << " candidate disequalities"
                 << std::endl;
  for (const Node& eq : candDeq)
  {
    Trace("ccgen-debug") << "- disequality: " << eq << std::endl;
    std::unordered_set<Node> syms;
    expr::getSymbols(eq, syms);
    Subs ss;
    for (const Node& s : syms)
    {
      if (!s.getType().isFirstClass())
      {
        continue;
      }
      // if the symbol appears in a quantified formula, do not trust its model
      // value. HACK: Also always take model values for skolems.
      if (qsyms.find(s) == qsyms.end() || s.getKind() == Kind::SKOLEM)
      {
        Node sm = model->getValue(s);
        Trace("ccgen-debug") << "  - " << s << " = " << sm << std::endl;
        ss.add(s, sm);
      }
    }
    Node eqm = rewrite(ss.apply(eq));
    Trace("ccgen-debug") << "  ...concretizes to " << eqm << std::endl;
    if (eqm == d_false)
    {
      Trace("ccgen-debug") << "...filter " << eq << std::endl;
      continue;
    }
    Trace("ccgen-debug") << "...keep " << eq << std::endl;
    checkDisequality(eq);
  }

  // candidate conjectures
  NodeManager* nm = nodeManager();
  while (d_conjGenIndex.get() < d_conjGen.size())
  {
    Node lem = d_conjGen[d_conjGenIndex.get()];
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(lem, fvs);
    std::vector<Node> bvs(fvs.begin(), fvs.end());
    if (!bvs.empty())
    {
      lem =
          nm->mkNode(Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, bvs), lem);
    }
    lem = nm->mkNode(Kind::OR, lem.negate(), lem);
    Trace("ccgen-lemma") << "ConflictConjectureGenerator: send lemma " << lem << std::endl;
    d_qim.addPendingLemma(lem,
                          InferenceId::QUANTIFIERS_CONFLICT_CONJ_GEN_SPLIT);
    d_conjGenIndex = d_conjGenIndex.get() + 1;
  }
  Trace("ccgen") << "ConflictConjectureGenerator: end check" << std::endl;
}

std::string ConflictConjectureGenerator::identify() const
{
  return "conflict-conjecture-gen";
}

void ConflictConjectureGenerator::checkDisequality(const Node& eq)
{
  Trace("ccgen") << "checkDisequality " << eq << std::endl;
  std::vector<Node> vars;
  for (size_t i = 0; i < 2; i++)
  {
    Node r = d_ee->getRepresentative(eq[i]);
    Node v = getOrMkVarForEqc(r);
    vars.push_back(v);
    getGeneralizations(v);
  }
  // see if any generalization of the right hand
  std::vector<Node>& genRhs = d_eqcGenRec[vars[1]];

  Trace("ccgen") << "- look at " << genRhs.size()
                 << " recursive generalizations of RHS" << std::endl;
  for (const Node& g : genRhs)
  {
    const std::vector<Node>& gfvs = d_genToFv[g];
    Trace("ccgen-debug") << "  - " << g << std::endl;
    State s = gfvs.empty() ? State::SUBSET : State::UNKNOWN;
    findCompatible(g, gfvs, vars[0], &d_gtrie, s, 0);
  }
}

Node ConflictConjectureGenerator::getOrMkVarForEqc(const Node& e)
{
  Assert(d_ee->getRepresentative(e) == e);
  std::map<Node, Node>::iterator it = d_bv.find(e);
  if (it != d_bv.end())
  {
    return it->second;
  }
  Node v = NodeManager::mkBoundVar(e.getType());
  d_bv[e] = v;
  d_bvToEqc[v] = e;
  return v;
}
const std::vector<Node>& ConflictConjectureGenerator::getGenForEqc(
    const Node& e)
{
  std::map<Node, std::vector<Node>>::iterator it = d_eqcGen.find(e);
  if (it != d_eqcGen.end())
  {
    return it->second;
  }
  TermDb* tdb = getTermDatabase();
  NodeManager* nm = nodeManager();
  std::vector<Node>& cg = d_eqcGen[e];
  Assert(d_ee->hasTerm(e));
  Assert(d_ee->getRepresentative(e) == e);
  eq::EqClassIterator eqc = eq::EqClassIterator(e, d_ee);
  while (!eqc.isFinished())
  {
    Node n = *eqc;
    ++eqc;
    if (n.getKind() == Kind::APPLY_UF || n.getKind() == Kind::APPLY_CONSTRUCTOR)
    {
      if (n.getNumChildren() == 0)
      {
        cg.emplace_back(n);
        continue;
      }
      // minor optimization: if the term is inactive (e.g. congruent to another
      // term), skip.
      if (!tdb->isTermActive(n))
      {
        continue;
      }
      Node op = n.getOperator();
      std::vector<Node> children;
      children.push_back(op);
      for (const Node& nc : n)
      {
        Assert(d_ee->hasTerm(nc));
        Node r = d_ee->getRepresentative(nc);
        Node v = getOrMkVarForEqc(r);
        children.push_back(v);
      }
      Node gen = nm->mkNode(n.getKind(), children);
      cg.emplace_back(gen);
    }
  }
  return cg;
}

void ConflictConjectureGenerator::getGeneralizations(const Node& v)
{
  Assert(v.getKind() == Kind::BOUND_VARIABLE);
  if (d_eqcGenRec.find(v) != d_eqcGenRec.end())
  {
    return;
  }
  d_eqcGenRec[v].emplace_back(v);
  // base case: own free variable
  addGeneralizationTerm(v, v, 0, {v});
  size_t reps = 15;
  Trace("ccgen-debug") << "Get " << reps << " runs for generalizations of " << v
                 << std::endl;
  for (size_t i = 0; i < reps; i++)
  {
    getGeneralizationsInternal(v);
  }
}

void ConflictConjectureGenerator::getGeneralizationsInternal(const Node& v)
{
  size_t depth = 5;
  Node cur = v;
  // the current free variables of cur
  std::vector<Node> fvs;
  std::vector<Node>& grecs = d_eqcGenRec[v];
  fvs.push_back(v);
  Subs subs;
  size_t rindex = Random::getRandom().pick(0, fvs.size() - 1);
  for (size_t i = 0; i < depth; i++)
  {
    Node vc = fvs[rindex];
    Trace("ccgen-debug") << "process " << vc << std::endl;
    Assert(d_bvToEqc.find(vc) != d_bvToEqc.end());
    const std::vector<Node>& gens = getGenForEqc(d_bvToEqc[vc]);
    if (gens.empty())
    {
      rindex = rindex+1==fvs.size() ? 0 : rindex+1;
      Trace("ccgen-debug") << "...no generalizations" << std::endl;
      // nothing to generalize
      continue;
    }
    size_t gindex = Random::getRandom().pick(0, gens.size() - 1);
    Node g = gens[gindex];
    Node gs = subs.apply(g);
    if (expr::hasSubterm(gs, v))
    {
      Trace("ccgen-debug") << "...cyclic to " << gs << std::endl;
      rindex = Random::getRandom().pick(0, fvs.size() - 1);
      // cyclic, skip
      continue;
    }
    Trace("ccgen-debug") << "...expand to " << gs << std::endl;
    std::vector<Node> newVars;
    if (g.getNumChildren() > 0)
    {
      bool isDag = false;
      for (const Node& gv : g)
      {
        if (subs.contains(gv))
        {
          // already handled
          isDag = true;
        }
        else if (std::find(fvs.begin(), fvs.end(), gv) == fvs.end())
        {
          newVars.push_back(gv);
        }
        else
        {
          // already in progress of being handled
          isDag = true;
        }
      }
      if (isDag)
      {
        rindex = Random::getRandom().pick(0, fvs.size() - 1);
        continue;
      }
    }
    fvs.erase(fvs.begin() + rindex);
    for (const Node& gv : newVars)
    {
      auto it = std::lower_bound(fvs.begin(), fvs.end(), gv);
      fvs.insert(it, gv);
    }
    Trace("ccgen-debug") << "...free variables now " << fvs << std::endl;
    Subs stmp;
    stmp.add(vc, gs);
    cur = stmp.apply(cur);
    stmp.applyToRange(subs);
    subs.add(vc, gs);
    // cur is now a candidate term
    addGeneralizationTerm(cur, v, i, fvs);
    grecs.emplace_back(cur);
    if (fvs.empty())
    {
      break;
    }
    // new index
    rindex = Random::getRandom().pick(0, fvs.size() - 1);
  }
}

void ConflictConjectureGenerator::addGeneralizationTerm(
    const Node& g, const Node& v, size_t depth, const std::vector<Node>& fvs)
{
  if (d_genToFv.find(g) != d_genToFv.end())
  {
    return;
  }
  Trace("ccgen-terms") << "* Generalization term [" << v << "]: " << g << std::endl;
  Trace("ccgen-debug") << "- free variables are " << fvs << std::endl;
  d_genToFv[g] = fvs;
  GenTrie* gt = &d_gtrie;
  for (const Node& fv : fvs)
  {
    gt = &gt->d_children[fv];
  }
  gt->d_gens.emplace_back(g, v);
}

void ConflictConjectureGenerator::GenTrie::clear()
{
  d_children.clear();
  d_gens.clear();
}

void ConflictConjectureGenerator::findCompatible(
    const Node& g,
    const std::vector<Node>& fvs,
    const Node& vlhs,
    GenTrie* gt,
    ConflictConjectureGenerator::State state,
    size_t fvindex)
{
  if (state != State::SUBSET || fvindex == fvs.size())
  {
    for (const std::pair<Node, Node>& cg : gt->d_gens)
    {
      if (cg.second == vlhs)
      {
        if (state == State::SUBSET)
        {
          candidateConjecture(cg.first, g);
        }
        else
        {
          candidateConjecture(g, cg.first);
        }
      }
      else
      {
        Trace("ccgen-debug")
            << "- found term " << cg.first << " but not for lhs " << vlhs
            << " vs " << cg.second << std::endl;
      }
    }
  }
  Trace("ccgen-debug") << "  findCompatible " << fvindex << "/" << fvs.size()
                       << " state = " << static_cast<int>(state) << std::endl;
  Assert(state != State::UNKNOWN || fvindex < fvs.size());
  for (std::pair<const Node, GenTrie>& cg : gt->d_children)
  {
    if (fvindex < fvs.size() && cg.first == fvs[fvindex])
    {
      Assert(state != State::SUPERSET);
      State newState = fvindex + 1 == fvs.size() ? State::SUBSET : state;
      findCompatible(g, fvs, vlhs, &cg.second, newState, fvindex + 1);
    }
    else if (std::find(fvs.begin() + fvindex, fvs.end(), cg.first) != fvs.end())
    {
      // we skipped a variable
      if (state != State::SUBSET)
      {
        findCompatible(g, fvs, vlhs, &cg.second, State::SUPERSET, fvindex);
      }
    }
    else if (state != State::SUPERSET)
    {
      findCompatible(g, fvs, vlhs, &cg.second, State::SUBSET, fvindex);
    }
  }
}

class EMatchFrame
{
 public:
  EMatchFrame() {}
  EMatchFrame(TermDb* tdb, eq::EqualityEngine* ee, const Node& m, const Node& r)
      : d_toMatch(m), d_index(0)
  {
    Assert(ee->hasTerm(r) && ee->getRepresentative(r) == r && r.isConst());
    Node op = m.getOperator();
    std::map<size_t, Node> groundArgs;
    for (size_t i = 0, nargs = m.getNumChildren(); i < nargs; i++)
    {
      if (m[i].getKind() == Kind::BOUND_VARIABLE)
      {
        d_varArgs.push_back(i);
      }
      else if (!expr::hasBoundVar(m[i]))
      {
        Assert(ee->hasTerm(m[i]));
        groundArgs[i] = ee->getRepresentative(m[i]);
      }
      else
      {
        d_recArgs.push_back(i);
      }
    }
    // get the candidates
    eq::EqClassIterator eqc = eq::EqClassIterator(r, ee);
    while (!eqc.isFinished())
    {
      Node n = *eqc;
      ++eqc;
      // must match
      if (!n.hasOperator() || n.getOperator() != m.getOperator()
          || !tdb->isTermActive(n))
      {
        continue;
      }
      Assert(n.getNumChildren() == m.getNumChildren());
      // prune ground disequal
      bool success = true;
      for (std::pair<const size_t, Node>& g : groundArgs)
      {
        Assert(g.first < n.getNumChildren());
        Assert(ee->hasTerm(n[g.first]));
        Node gr = ee->getRepresentative(n[g.first]);
        if (gr != g.second)
        {
          success = false;
          break;
        }
      }
      if (success)
      {
        d_matches.push_back(n);
      }
    }
  }
  Node d_toMatch;
  std::vector<Node> d_matches;
  std::vector<size_t> d_recArgs;
  std::vector<size_t> d_varArgs;
  std::unordered_set<size_t> d_varArgsBound;
  size_t d_index;
  bool push(TermDb* tdb,
            eq::EqualityEngine* ee,
            Subs& match,
            std::vector<std::shared_ptr<EMatchFrame>>& emf)
  {
    Trace("cconj-em-debug") << "push " << std::endl;
    if (isFinished())
    {
      Trace("cconj-em-debug") << "...already finished" << std::endl;
      return false;
    }
    Node nextMatch = d_matches[d_index];
    d_index++;
    Assert(nextMatch.getNumChildren() == d_toMatch.getNumChildren());
    std::vector<Node> groundRec;
    for (size_t i : d_recArgs)
    {
      Assert(i < nextMatch.getNumChildren());
      Assert(ee->hasTerm(nextMatch[i]));
      Node r = ee->getRepresentative(nextMatch[i]);
      if (!r.isConst())
      {
        // non-constant
        Trace("cconj-em-debug") << "...non-const" << std::endl;
        return false;
      }
      groundRec.emplace_back(r);
    }
    Trace("cconj-em-debug") << "look at var args" << std::endl;
    // match the current vars
    for (size_t i : d_varArgs)
    {
      const Node& v = d_toMatch[i];
      Assert(v.getKind() == Kind::BOUND_VARIABLE);
      Node cur = match.getSubs(v);
      if (cur.isNull())
      {
        d_varArgsBound.insert(i);
        match.add(v, nextMatch[i]);
        continue;
      }
      Assert(ee->hasTerm(nextMatch[i]));
      if (!ee->areEqual(nextMatch[i], cur))
      {
        // failed a bound argument argument
        pop(match);
        Trace("cconj-em-debug") << "...bound conflict" << std::endl;
        return false;
      }
    }
    Trace("cconj-em-debug") << "push" << std::endl;
    Assert(groundRec.size() == d_recArgs.size());
    for (size_t i = 0, ngr = groundRec.size(); i < ngr; i++)
    {
      emf.emplace_back(std::make_shared<EMatchFrame>(
          tdb, ee, d_toMatch[d_recArgs[i]], groundRec[i]));
    }
    Trace("cconj-em-debug") << "...return success" << std::endl;
    return true;
  }
  void pop(Subs& match)
  {
    for (size_t i : d_varArgsBound)
    {
      match.erase(d_toMatch[i]);
    }
    d_varArgsBound.clear();
  }
  bool isFinished() const { return d_index == d_matches.size(); }
};

void ConflictConjectureGenerator::candidateConjecture(const Node& a,
                                                      const Node& b)
{
  if (a.isVar() && expr::hasSubterm(b,a))
  {
    // corner case of the form x = t[x], flip sides
    candidateConjecture(b,a);
    return;
  }
  Trace("cconj-filter") << "Candidate conjecture : " << a << " == " << b << "?"
                        << std::endl;
  Trace("cconj-filter") << "Try filter based on E-matching" << std::endl;
  if (filterEmatching(a, b))
  {
    Trace("cconj-filter") << "...filtered based on E-matching" << std::endl;
    return;
  }

  // filter based on cache
  Node lem = a.eqNode(b);
  // canonize it, which catches duplicates modulo alpha equivalence
  Node clem = d_tc.getCanonicalTerm(lem);
  if (d_conjGenCache.find(clem) != d_conjGenCache.end())
  {
    Trace("cconj-filter") << "...already in cache" << std::endl;
    return;
  }
  d_conjGenCache.insert(clem);
  Trace("cconj") << "*** Conjecture : " << a << " == " << b << std::endl;
  d_conjGen.emplace_back(lem);
}

bool ConflictConjectureGenerator::filterEmatching(const Node& a, const Node& b)
{
  if (!a.hasOperator())
  {
    // we don't expect this to happen, but in case it does we given an
    // assertion failure
    Assert(false);
    return false;
  }
  // TODO: cache E-matching for a, for checking a = b1 and a = b2
  Node op = a.getOperator();
  TermDb* tdb = getTermDatabase();
  EntailmentCheck* ec = d_treg.getEntailmentCheck();
  std::vector<Node> reps;
  eq::EqClassesIterator eqcs = eq::EqClassesIterator(d_ee);
  while (!eqcs.isFinished())
  {
    Node r = (*eqcs);
    ++eqcs;
    if (r.isConst() && r.getType() == a.getType())
    {
      reps.push_back(r);
    }
  }
  size_t confirmed = 0;
  size_t tested = 0;
  for (const Node& r : reps)
  {
    Trace("cconj-filter-debug") << "- look in " << r << std::endl;
    Subs match;
    // filter based on E-matching and test
    std::vector<std::shared_ptr<EMatchFrame>> emf;
    emf.emplace_back(std::make_shared<EMatchFrame>(tdb, d_ee, a, r));
    size_t eindex = 1;
    do
    {
      Assert(0 < eindex);
      Trace("cconj-filter-debug")
          << "match at " << eindex << ", " << emf.size() << std::endl;
      Assert(eindex <= emf.size() + 1);
      if (eindex == emf.size() + 1)
      {
        Trace("cconj-filter-debug")
            << "Matches " << match.toString() << std::endl;
        // should have a complete match, process the right hand side
        Node bs = match.apply(b);
        Node bse = ec->getEntailedTerm(bs);
        Trace("cconj-filter-debug")
            << "...left hand side entailed " << bse << std::endl;
        if (!bse.isNull())
        {
          Node rr = d_ee->getRepresentative(bse);
          if (d_ee->areDisequal(r, rr, false))
          {
            Trace("cconj-filter") << "...disequal, filtered based on "
                                  << match.toString() << std::endl;
            Trace("cconj-filter") << "lhs: " << r << std::endl;
            Trace("cconj-filter")
                << "rhs: " << d_ee->getRepresentative(bse) << std::endl;
            return true;
          }
          tested++;
          confirmed = confirmed + (r == rr ? 1 : 0);
        }
      }
      else if (emf[eindex - 1]->push(tdb, d_ee, match, emf))
      {
        eindex++;
        continue;
      }
      else
      {
        emf[eindex - 1]->pop(match);
      }
      eindex--;
      emf.resize(eindex);
      if (!emf.empty())
      {
        emf[eindex - 1]->pop(match);
      }
    } while (!emf.empty());
  }
  if (tested == 0)
  {
    // no tests, reject?
    return true;
  }
  Trace("cconj-filter") << "...success, not filtered, tested=" << tested
                        << ", confirmed=" << confirmed << std::endl;
  return false;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
