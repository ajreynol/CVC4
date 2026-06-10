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
      d_procTime(statisticsRegistry().registerTimer(
          "theory::quantifiers::eagerInst::processTime")),
      d_addInstTime(statisticsRegistry().registerTimer(
          "theory::quantifiers::eagerInst::addInstTime")),
      d_statPairs(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numPairsProcessed")),
      d_statMatches(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numMatches")),
      d_statInst(statisticsRegistry().registerInt(
          "theory::quantifiers::eagerInst::numInstantiations"))
{
}

EagerInstantiation::~EagerInstantiation() {}

bool EagerInstantiation::needsCheck(Theory::Effort e)
{
  if (e != Theory::EFFORT_FULL)
  {
    // We process new terms at standard effort via a direct call to
    // processNewTerms from the quantifiers engine. We only require a check
    // at full effort if there are still unprocessed pairs, e.g. if the
    // previous standard effort check was interrupted by a conflict.
    return false;
  }
  for (const std::pair<const Node, std::vector<std::unique_ptr<EagerTrigger>>>&
           ot : d_opTriggers)
  {
    std::map<Node, std::unique_ptr<OpTermList>>::iterator itt =
        d_opTerms.find(ot.first);
    if (itt == d_opTerms.end())
    {
      continue;
    }
    size_t nuniq = itt->second->d_unique.size();
    // whether promotion may extend the unique list
    bool promotionPending =
        itt->second->d_rawIdx.get() < itt->second->d_list.size();
    for (const std::unique_ptr<EagerTrigger>& tr : ot.second)
    {
      if ((promotionPending || tr->d_procIdx.get() < nuniq)
          && d_activeQuants.contains(tr->d_quant))
      {
        return true;
      }
    }
  }
  return false;
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
      Trace("eager-inst-reject")
          << "Eager inst: reject pattern (different vars) : " << pat
          << std::endl;
      continue;
    }
    Node op = pat.getOperator();
    d_opTriggers[op].emplace_back(
        std::make_unique<EagerTrigger>(context(), q, pat));
    Trace("eager-inst") << "Eager inst: trigger for " << q << " : " << pat
                        << std::endl;
  }
}

void EagerInstantiation::assertNode(Node q)
{
  if (d_activeQuants.contains(q))
  {
    return;
  }
  d_activeQuants.insert(q);
  Trace("eager-inst") << "Eager inst: activate " << q << std::endl;
}

void EagerInstantiation::eqNotifyNewClass(TNode t)
{
  // We only consider applications of uninterpreted functions, which is the
  // only kind of pattern head we currently handle. Note we must not do any
  // matching here, since the equality engine may be mid-operation; we only
  // enqueue the term.
  if (t.getKind() == Kind::APPLY_UF)
  {
    getOpTermList(t.getOperator()).d_list.push_back(t);
  }
}

EagerInstantiation::OpTermList& EagerInstantiation::getOpTermList(
    const Node& op)
{
  std::map<Node, std::unique_ptr<OpTermList>>::iterator it =
      d_opTerms.find(op);
  if (it == d_opTerms.end())
  {
    it = d_opTerms.emplace(op, std::make_unique<OpTermList>(context())).first;
  }
  return *it->second;
}

void EagerInstantiation::promoteTerms(OpTermList& ol)
{
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  size_t i = ol.d_rawIdx.get();
  size_t nterms = ol.d_list.size();
  if (i >= nterms)
  {
    return;
  }
  std::vector<Node> sigc;
  while (i < nterms)
  {
    TNode t = ol.d_list[i];
    i++;
    if (!ee->hasTerm(t))
    {
      // can happen if the term was removed by a backtrack after it was
      // queued
      continue;
    }
    // The signature of t is the tuple of representatives of its arguments
    // (its operator is implied by the list it occurs in). Note that within
    // a SAT context, congruences are never undone, so the promotion
    // decision remains valid for the lifetime of this list entry.
    sigc.clear();
    for (const Node& tc : t)
    {
      sigc.push_back(ee->getRepresentative(tc));
    }
    Node sig = nodeManager()->mkNode(Kind::SEXPR, sigc);
    if (!ol.d_sigs.contains(sig))
    {
      ol.d_sigs.insert(sig);
      ol.d_unique.push_back(t);
    }
    else
    {
      Trace("eager-inst-debug2")
          << "Eager inst: do not promote congruent " << t << std::endl;
    }
  }
  ol.d_rawIdx = i;
}

void EagerInstantiation::processNewTerms()
{
  if (d_qstate.isInConflict() || !d_qstate.getEqualityEngine()->consistent())
  {
    return;
  }
  CodeTimer codeTimer(d_procTime);
  int64_t prevPairs = d_statPairs.get();
  int64_t prevMatches = d_statMatches.get();
  int64_t prevInst = d_statInst.get();
  for (std::pair<const Node, std::vector<std::unique_ptr<EagerTrigger>>>& ot :
       d_opTriggers)
  {
    std::map<Node, std::unique_ptr<OpTermList>>::iterator itt =
        d_opTerms.find(ot.first);
    if (itt == d_opTerms.end())
    {
      continue;
    }
    promoteTerms(*itt->second);
    context::CDList<Node>& terms = itt->second->d_unique;
    size_t nterms = terms.size();
    for (std::unique_ptr<EagerTrigger>& tr : ot.second)
    {
      size_t i = tr->d_procIdx.get();
      if (i >= nterms || !d_activeQuants.contains(tr->d_quant))
      {
        // up to date, or the quantified formula is not (yet) asserted; in
        // the latter case we do not advance the cursor, so that we match
        // against all existing terms if it is asserted later
        continue;
      }
      Trace("eager-inst-debug")
          << "Eager inst: process terms [" << i << ", " << nterms << ") of "
          << ot.first << " for " << tr->d_pattern << std::endl;
      while (i < nterms)
      {
        TNode t = terms[i];
        i++;
        resourceManager()->spendResource(Resource::QuantifierStep);
        ++d_statPairs;
        processTermForTrigger(t, *tr);
        if (d_qstate.isInConflict())
        {
          // stop processing, but remember how far we got
          break;
        }
      }
      tr->d_procIdx = i;
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
  if (TraceIsOn("eager-inst-status"))
  {
    int64_t p = d_statPairs.get() - prevPairs;
    if (p > 0)
    {
      Trace("eager-inst-status")
          << "Eager inst: round processed " << p << " pairs, found "
          << (d_statMatches.get() - prevMatches) << " matches, added "
          << (d_statInst.get() - prevInst) << " instantiations"
          << (d_qstate.isInConflict() ? " (conflict)" : "") << std::endl;
    }
  }
}

void EagerInstantiation::processTermForTrigger(TNode t, const EagerTrigger& tr)
{
  eq::EqualityEngine* ee = d_qstate.getEqualityEngine();
  Assert(ee->hasTerm(t));
  const Node& q = tr.d_quant;
  const Node& pat = tr.d_pattern;
  Assert(pat.getNumChildren() == t.getNumChildren());
  size_t nchild = pat.getNumChildren();
  // Cheap top-level filter before doing any allocation: ground arguments of
  // the pattern must be equal to the corresponding argument of t. This
  // rejects the vast majority of pairs for operators with many triggers
  // that differ in a ground argument (e.g. has_type patterns).
  for (size_t i = 0; i < nchild; i++)
  {
    TNode pc = pat[i];
    if (!expr::hasBoundVar(pc)
        && (!ee->hasTerm(pc) || !ee->areEqual(pc, t[i])))
    {
      return;
    }
  }
  // match the arguments of the pattern against the arguments of t
  std::vector<std::pair<TNode, TNode>> todo;
  for (size_t i = 0; i < nchild; i++)
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
  Instantiate* ie = d_qim.getInstantiate();
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
      addSuccess =
          ie->addInstantiation(q,
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
