/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager instantiation via E-matching on new terms.
 */

#include "theory/quantifiers/eager_inst.h"

#include "expr/node_algorithm.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_inference_manager.h"
#include "theory/quantifiers/quantifiers_registry.h"
#include "theory/uf/equality_engine.h"
#include "util/resource_manager.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EagerInstantiation::EagerInstantiation(Env& env,
                                       QuantifiersState& qs,
                                       QuantifiersInferenceManager& qim,
                                       QuantifiersRegistry& qr,
                                       TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_activeQuants(context()),
      d_newTerms(context()),
      d_procSigs(context()),
      d_procIdx(context(), 0),
      d_procTime(statisticsRegistry().registerTimer(
          "theory::quantifiers::eagerInst::processTime")),
      d_addInstTime(statisticsRegistry().registerTimer(
          "theory::quantifiers::eagerInst::addInstTime")),
      d_statTerms(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numTermsProcessed")),
      d_statMatches(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numMatches")),
      d_statInst(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numInstantiations"))
{
}

EagerInstantiation::~EagerInstantiation() {}

bool EagerInstantiation::needsCheck(Theory::Effort e)
{
  // We process new terms at standard effort via a direct call to
  // processNewTerms from the quantifiers engine. We only require a check at
  // full effort if there are still unprocessed terms, e.g. if the previous
  // standard effort check was interrupted by a conflict.
  return e == Theory::EFFORT_FULL && d_procIdx.get() < d_newTerms.size();
}

void EagerInstantiation::check(CVC5_UNUSED Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_CONFLICT)
  {
    return;
  }
  processNewTerms();
}

void EagerInstantiation::registerQuantifier(Node q)
{
  if (q.getNumChildren() != 3)
  {
    return;
  }
  // We process quantified formulas that are unowned, or owned by the lazy
  // instantiation engine, which takes ownership of quantified formulas with
  // user patterns when --user-pat=strict. Eager and lazy E-matching are
  // complementary strategies over the same triggers.
  QuantifiersModule* owner = d_qreg.getOwner(q);
  if (owner != nullptr && owner != this && owner != d_instEngine)
  {
    Trace("eager-inst-reject")
        << "Eager inst: reject (owner=" << owner->identify() << ") " << q
        << std::endl;
    return;
  }
  // collect the variables of q
  std::unordered_set<Node> qvars(q[0].begin(), q[0].end());
  for (const Node& ipl : q[2])
  {
    // only consider single triggers; multi-triggers are handled by the
    // lazy instantiation engine
    if (ipl.getKind() != Kind::INST_PATTERN || ipl.getNumChildren() != 1)
    {
      continue;
    }
    Node pat = ipl[0];
    // only consider applications of uninterpreted functions
    if (pat.getKind() != Kind::APPLY_UF)
    {
      Trace("eager-inst-reject")
          << "Eager inst: reject pattern kind " << pat.getKind() << " : "
          << pat << std::endl;
      continue;
    }
    // the pattern must contain all variables of q
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(pat, fvs);
    if (fvs.size() != qvars.size())
    {
      Trace("eager-inst-reject")
          << "Eager inst: reject pattern (covers " << fvs.size() << "/"
          << qvars.size() << " vars) : " << pat << std::endl;
      continue;
    }
    bool covers = true;
    for (const Node& v : qvars)
    {
      if (fvs.find(v) == fvs.end())
      {
        covers = false;
        break;
      }
    }
    if (!covers)
    {
      continue;
    }
    Node op = pat.getOperator();
    d_opTriggers[op].emplace_back(q, pat);
    Trace("eager-inst") << "Eager trigger for " << q << " : " << pat
                        << std::endl;
  }
}

void EagerInstantiation::assertNode(Node q)
{
  d_activeQuants.insert(q);
}

void EagerInstantiation::eqNotifyNewClass(TNode t)
{
  // We only consider applications of uninterpreted functions, which is the
  // only kind of pattern head we currently handle. Note we must not do any
  // matching here, since the equality engine may be mid-operation; we only
  // enqueue the term.
  if (t.getKind() == Kind::APPLY_UF)
  {
    d_newTerms.push_back(t);
  }
}

void EagerInstantiation::processNewTerms()
{
  size_t endIdx = d_newTerms.size();
  if (d_procIdx.get() >= endIdx)
  {
    return;
  }
  if (d_qstate.isInConflict() || !d_qstate.getEqualityEngine()->consistent())
  {
    return;
  }
  Trace("eager-inst-debug") << "Eager inst: process new terms ["
                            << d_procIdx.get() << ", " << endIdx << ")"
                            << std::endl;
  CodeTimer codeTimer(d_procTime);
  while (d_procIdx.get() < endIdx)
  {
    TNode t = d_newTerms[d_procIdx.get()];
    d_procIdx = d_procIdx.get() + 1;
    resourceManager()->spendResource(Resource::QuantifierStep);
    ++d_statTerms;
    processTerm(t);
    if (d_qstate.isInConflict())
    {
      break;
    }
  }
}

void EagerInstantiation::processTerm(TNode t)
{
  Node op = t.getOperator();
  std::map<Node, std::vector<EagerTrigger>>::iterator it =
      d_opTriggers.find(op);
  if (it == d_opTriggers.end())
  {
    return;
  }
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  if (!ee->hasTerm(t))
  {
    // can happen if the term was removed by a backtrack after it was queued
    return;
  }
  // Compute the signature of t, which is its operator applied to the
  // representatives of its arguments. If we already processed a term with
  // the same signature, the matches of t are duplicates of those we have
  // already considered, and we skip it.
  std::vector<Node> sigc;
  sigc.push_back(op);
  for (const Node& tc : t)
  {
    sigc.push_back(ee->getRepresentative(tc));
  }
  Node sig = nodeManager()->mkNode(Kind::SEXPR, sigc);
  if (d_procSigs.contains(sig))
  {
    Trace("eager-inst-debug2") << "Eager inst: skip congruent " << t
                               << std::endl;
    return;
  }
  d_procSigs.insert(sig);
  Instantiate* ie = d_qim.getInstantiate();
  for (const EagerTrigger& tr : it->second)
  {
    const Node& q = tr.d_quant;
    if (!d_activeQuants.contains(q))
    {
      continue;
    }
    const Node& pat = tr.d_pattern;
    Assert(pat.getNumChildren() == t.getNumChildren());
    // match the arguments of the pattern against the arguments of t
    std::vector<std::pair<TNode, TNode>> todo;
    for (size_t i = 0, nchild = pat.getNumChildren(); i < nchild; i++)
    {
      todo.emplace_back(pat[i], t[i]);
    }
    std::map<Node, Node> binding;
    std::vector<std::map<Node, Node>> matches;
    matchRec(0, todo, binding, matches);
    // The instantiations we send, indexed by the tuple of representatives
    // of the terms, so that we send at most one instantiation per
    // equivalence-class tuple.
    std::set<std::vector<Node>> seenInsts;
    std::vector<Node> instSig;
    for (const std::map<Node, Node>& m : matches)
    {
      std::vector<Node> terms;
      instSig.clear();
      bool success = true;
      for (const Node& v : q[0])
      {
        std::map<Node, Node>::const_iterator itm = m.find(v);
        if (itm == m.end())
        {
          // should not happen by trigger registration, but be safe
          success = false;
          break;
        }
        terms.push_back(itm->second);
        instSig.push_back(ee->getRepresentative(itm->second));
      }
      if (!success || !seenInsts.insert(instSig).second)
      {
        continue;
      }
      Trace("eager-inst-debug")
          << "Eager inst: match " << q << " with " << terms << " from term "
          << t << std::endl;
      ++d_statMatches;
      // We disable the entailment check, since it relies on state of TermDb
      // that is only valid during full effort instantiation rounds.
      bool addSuccess;
      {
        CodeTimer instTimer(d_addInstTime);
        addSuccess = ie->addInstantiation(
            q,
            terms,
            InferenceId::QUANTIFIERS_INST_E_MATCHING_EAGER,
            Node::null(),
            false,
            false);
      }
      if (addSuccess)
      {
        ++d_statInst;
        Trace("eager-inst") << "Eager inst: success " << q << " with " << terms
                            << std::endl;
      }
      if (d_qstate.isInConflict())
      {
        return;
      }
    }
  }
}

void EagerInstantiation::matchRec(size_t i,
                                  std::vector<std::pair<TNode, TNode>>& todo,
                                  std::map<Node, Node>& binding,
                                  std::vector<std::map<Node, Node>>& matches)
{
  if (i == todo.size())
  {
    matches.push_back(binding);
    return;
  }
  TNode p = todo[i].first;
  TNode t = todo[i].second;
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  if (p.getKind() == Kind::BOUND_VARIABLE)
  {
    std::map<Node, Node>::iterator itb = binding.find(p);
    if (itb != binding.end())
    {
      // non-linear occurrence, the binding must be equal to t
      if (itb->second == t || ee->areEqual(itb->second, t))
      {
        matchRec(i + 1, todo, binding, matches);
      }
      return;
    }
    binding[p] = t;
    matchRec(i + 1, todo, binding, matches);
    binding.erase(p);
    return;
  }
  if (!expr::hasBoundVar(p))
  {
    // ground subterm, must be equal to t in the current context
    if (ee->hasTerm(p) && ee->areEqual(p, t))
    {
      matchRec(i + 1, todo, binding, matches);
    }
    return;
  }
  if (p.getKind() != Kind::APPLY_UF)
  {
    // unhandled pattern shape (e.g. interpreted symbols over bound
    // variables), this trigger is handled by the lazy engine only
    return;
  }
  // find a term in the equivalence class of t whose operator matches
  Node op = p.getOperator();
  Node r = ee->getRepresentative(t);
  size_t base = todo.size();
  // We consider only one candidate per tuple of argument representatives,
  // since congruent candidates yield the same matches modulo equality.
  std::set<std::vector<TNode>> seenSigs;
  std::vector<TNode> sig;
  eq::EqClassIterator eqc(r, ee);
  while (!eqc.isFinished())
  {
    TNode s = *eqc;
    ++eqc;
    if (s.getKind() != Kind::APPLY_UF || s.getOperator() != op)
    {
      continue;
    }
    Assert(s.getNumChildren() == p.getNumChildren());
    sig.clear();
    for (const TNode& sc : s)
    {
      sig.push_back(ee->getRepresentative(sc));
    }
    if (!seenSigs.insert(sig).second)
    {
      // congruent to a candidate we already tried
      continue;
    }
    for (size_t j = 0, nchild = p.getNumChildren(); j < nchild; j++)
    {
      todo.emplace_back(p[j], s[j]);
    }
    matchRec(i + 1, todo, binding, matches);
    todo.resize(base);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
