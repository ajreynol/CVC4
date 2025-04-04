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
    : QuantifiersModule(env, qs, qim, qr, tr)
{
  d_false = nodeManager()->mkConst(false);
}

void ConflictConjectureGenerator::presolve() {}

bool ConflictConjectureGenerator::needsCheck(Theory::Effort e)
{
  return d_qstate.getInstWhenNeedsCheck(e);
}

void ConflictConjectureGenerator::reset_round(Theory::Effort e) {}

void ConflictConjectureGenerator::registerQuantifier(Node q) {}

void ConflictConjectureGenerator::checkOwnership(Node q) {}

void ConflictConjectureGenerator::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  d_ee = d_qstate.getEqualityEngine();
  Trace("ccgen") << "ConflictConjectureGenerator: check" << std::endl;
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
    Trace("ccgen") << "Get generalizations of " << eq << std::endl;
    checkDisequality(eq);
  }
}

std::string ConflictConjectureGenerator::identify() const
{
  return "conflict-conjecture-gen";
}

void ConflictConjectureGenerator::checkDisequality(const Node& eq)
{
  for (size_t i = 0; i < 2; i++)
  {
    Node r = d_ee->getRepresentative(eq[i]);
    Node v = getOrMkVarForEqc(r);
    getGeneralizations(v);
  }
  // see if any generalization of the right hand
  std::vector<Node>& genRhs = d_eqcGenRec[eq[1]];
  for (const Node& g : genRhs)
  {
    const std::vector<Node>& gfvs = d_genToFv[g];
    findCompatible(g, gfvs, eq[0], &d_gtrie, State::UNKNOWN, 0);
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
      std::vector<Node> children;
      children.push_back(n.getOperator());
      for (const Node& nc : n)
      {
        Assert(d_ee->hasTerm(nc));
        Node r = d_ee->getRepresentative(nc);
        Node v = getOrMkVarForEqc(r);
        children.push_back(v);
      }
      Node gen = nm->mkNode(Kind::APPLY_UF, children);
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
  addGeneralizationTerm(v, v, 0, {});
  size_t reps = 3;
  for (size_t i = 0; i < reps; i++)
  {
    getGeneralizationsInternal(v);
  }
}

void ConflictConjectureGenerator::getGeneralizationsInternal(const Node& v)
{
  size_t depth = 5;
  Trace("ccgen") << "Get generalizations of " << v << std::endl;
  Node cur = v;
  // the current free variables of cur
  std::vector<Node> fvs;
  std::vector<Node>& grecs = d_eqcGenRec[v];
  fvs.push_back(v);
  Subs subs;
  for (size_t i = 0; i < depth; i++)
  {
    size_t rindex = Random::getRandom().pick(0, fvs.size() - 1);
    Node vc = fvs[rindex];
    Trace("ccgen-debug") << "process " << vc << std::endl;
    Assert(d_bvToEqc.find(vc) != d_bvToEqc.end());
    const std::vector<Node>& gens = getGenForEqc(d_bvToEqc[vc]);
    if (gens.empty())
    {
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
      // cyclic, skip
      continue;
    }
    Trace("ccgen-debug") << "...expand to " << gs << std::endl;
    fvs.erase(fvs.begin() + rindex);
    if (g.getNumChildren() > 0)
    {
      // TODO: sorted add
      for (const Node& gv : g)
      {
        if (!subs.contains(gv))
        {
          fvs.push_back(gv);
        }
      }
      std::sort(fvs.begin(), fvs.end());
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
  }
}

void ConflictConjectureGenerator::addGeneralizationTerm(
    const Node& g, const Node& v, size_t depth, const std::vector<Node>& fvs)
{
  if (d_genToFv.find(g) != d_genToFv.end())
  {
    return;
  }
  Trace("ccgen") << "* Generalization term [" << v << "]: " << g << std::endl;
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
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
