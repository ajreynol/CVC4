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

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void EagerWatchList::add(const EagerTrie* et, const Node& t)
{
  d_matchJobs.push_back(std::pair<const EagerTrie*, Node>(et, t));
}

EagerWatchList* EagerWatchInfo::getOrMkList(const Node& r, bool doMk)
{
  context::CDHashMap<Node, std::shared_ptr<EagerWatchList>>::iterator it =
      d_eqWatch.find(r);
  if (it != d_eqWatch.end())
  {
    return it->second.get();
  }
  else if (!doMk)
  {
    return nullptr;
  }
  std::shared_ptr<EagerWatchList> eoi = std::make_shared<EagerWatchList>(d_ctx);
  d_eqWatch.insert(r, eoi);
  return eoi.get();
}

EagerTrie* EagerOpInfo::getCurrentTrie(TermDb* tdb)
{
  if (d_pats.empty())
  {
    return nullptr;
  }
  Assert(!d_triePats.empty());
  size_t tsize = d_pats.size();
  if (d_triePats.size() > d_pats.size())
  {
    // clean up any stale patterns that appear in the trie
    for (size_t i = d_triePats.size() - 1; i >= tsize; i--)
    {
      d_trie.erase(tdb, d_triePats[i]);
    }
    d_triePats.resize(tsize);
  }
  return &d_trie;
}

void EagerOpInfo::addPattern(TermDb* tdb, const Node& pat)
{
  d_trie.add(tdb, pat);
  d_triePats.emplace_back(pat);
  d_pats.emplace_back(pat);
}

EagerInst::EagerInst(Env& env,
                     QuantifiersState& qs,
                     QuantifiersInferenceManager& qim,
                     QuantifiersRegistry& qr,
                     TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_ee(nullptr),
      d_tdb(tr.getTermDatabase()),
      d_instTerms(userContext()),
      d_ownedQuants(context()),
      d_ppQuants(userContext()),
      d_rlvTerms(context()),
      d_fullInstTerms(userContext()),
      d_cdOps(context()),
      d_repWatch(context()),
      d_userPat(context()),
      d_statUserPats(statisticsRegistry().registerInt("EagerInst::userPats")),
      d_statUserPatsCd(
          statisticsRegistry().registerInt("EagerInst::userPatsCd")),
      d_statUserPatsMultiFilter(
          statisticsRegistry().registerInt("EagerInst::userPatsMultiFilter")),
      d_statMatchCall(statisticsRegistry().registerInt("EagerInst::matchCall"))
{
  d_tmpAddedLemmas = 0;
  d_instOutput = isOutputOn(OutputTag::INST_STRATEGY);
}

EagerInst::~EagerInst() {}

void EagerInst::presolve() {}

bool EagerInst::needsCheck(Theory::Effort e)
{
  if (d_instOutput)
  {
    Assert(isOutputOn(OutputTag::INST_STRATEGY));
    if (d_tmpAddedLemmas > 0)
    {
      output(OutputTag::INST_STRATEGY) << "(inst-strategy " << identify();
      output(OutputTag::INST_STRATEGY) << " :inst " << d_tmpAddedLemmas;
      output(OutputTag::INST_STRATEGY) << ")" << std::endl;
      d_tmpAddedLemmas = 0;
    }
  }
  return false;
}

void EagerInst::reset_round(Theory::Effort e) {}

void EagerInst::registerQuantifier(Node q) {}

void EagerInst::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  std::vector<Node> toProcess;
  std::unordered_set<Node> processed;
  for (const Node& n : assertions)
  {
    Kind k = n.getKind();
    if (k == Kind::FORALL)
    {
      toProcess.emplace_back(n);
    }
    else if (k == Kind::AND)
    {
      toProcess.insert(toProcess.end(), n.begin(), n.end());
    }
  }
  size_t i = 0;
  while (i < toProcess.size())
  {
    const Node& a = toProcess[i];
    i++;
    if (processed.find(a) != processed.end())
    {
      continue;
    }
    processed.insert(a);
    Kind k = a.getKind();
    if (k == Kind::FORALL)
    {
      d_ppQuants.insert(a);
      registerQuant(a);
    }
    else if (k == Kind::AND)
    {
      toProcess.insert(toProcess.end(), a.begin(), a.end());
    }
  }
  d_ee = d_qstate.getEqualityEngine();
  Assert(d_ee != nullptr);
}

void EagerInst::assertNode(Node q)
{
  if (!options().quantifiers.eagerInstCd)
  {
    return;
  }
  Assert(q.getKind() == Kind::FORALL);
  if (d_ppQuants.find(q) == d_ppQuants.end())
  {
    registerQuant(q);
  }
}
void EagerInst::registerQuant(const Node& q)
{
  Trace("eager-inst-register") << "Assert " << q << std::endl;
  if (q.getNumChildren() != 3)
  {
    return;
  }
  Node ipl = q[2];
  bool isPp = (d_ppQuants.find(q) != d_ppQuants.end());
  bool owner = isPp;
  bool hasPat = false;
  // TODO: do for any pattern selection?
  for (const Node& pat : ipl)
  {
    if (pat.getKind() == Kind::INST_PATTERN)
    {
      Node pati = d_qreg.substituteBoundVariablesToInstConstants(pat, q);
      std::vector<Node> ppc(pati.begin(), pati.end());
      std::vector<Node> spats;
      for (size_t i = 0, npats = pati.getNumChildren(); i < npats; i++)
      {
        Node pc = pati[i];
        if (pc.getKind() == Kind::APPLY_UF
            && d_qreg.hasAllInstantiationConstants(pc, q))
        {
          if (ppc.size() == 1)
          {
            spats.push_back(pc);
          }
          else
          {
            Node tmp = ppc[0];
            ppc[0] = ppc[i];
            ppc[i] = tmp;
            Node pp = nodeManager()->mkNode(Kind::INST_PATTERN, ppc);
            spats.push_back(pp);
          }
        }
      }
      if (spats.empty())
      {
        owner = false;
        Trace("eager-inst-warn")
            << "Cannot handle user pattern " << pat << std::endl;
      }
      for (const Node& spat : spats)
      {
        hasPat = true;
        // TODO: statically analyze if this would lead to matching loops
        Trace("eager-inst-register") << "Single pat: " << spat << std::endl;
        Node op;
        if (spat.getKind() == Kind::INST_PATTERN)
        {
          op = spat[0].getOperator();
          ++d_statUserPatsMultiFilter;
        }
        else
        {
          op = spat.getOperator();
        }
        EagerOpInfo* eoi = getOrMkOpInfo(op, true);
        eoi->addPattern(d_tdb, spat);
        if (!isPp)
        {
          d_cdOps.insert(op);
          ++d_statUserPatsCd;
        }
        else
        {
          ++d_statUserPats;
        }
        if (owner)
        {
          for (const Node& spc : spat)
          {
            if (spc.getKind() != Kind::INST_CONSTANT)
            {
              owner = false;
              break;
            }
          }
        }
      }
    }
  }
  // can maybe assign owner if only a trivial trigger and the quantified formula
  // is top level.
  if (hasPat && owner)
  {
    QAttributes qa;
    QuantAttributes::computeQuantAttributes(q, qa);
    if (qa.isStandard())
    {
      Trace("eager-inst-register") << "...owned" << std::endl;
      d_ownedQuants.insert(q);
    }
  }
}

void EagerInst::checkOwnership(Node q)
{
  if (d_ownedQuants.find(q) != d_ownedQuants.end())
  {
    d_qreg.setOwner(q, this, 2);
  }
}

void EagerInst::check(Theory::Effort e, QEffort quant_e) {}

std::string EagerInst::identify() const { return "eager-inst"; }

void EagerInst::notifyAssertedTerm(TNode t)
{
  if (t.getKind() != Kind::APPLY_UF)
  {
    return;
  }
  Node op = t.getOperator();
  d_rlvTerms.insert(t);
  if (d_fullInstTerms.find(t) != d_fullInstTerms.end())
  {
    if (d_cdOps.find(op) == d_cdOps.end())
    {
      return;
    }
  }
  // NOTE: in some cases a macro definition for this term may come after it is
  // registered, we don't bother handling this.
  EagerOpInfo* eoi = getOrMkOpInfo(op, false);
  if (eoi == nullptr)
  {
    d_fullInstTerms.insert(t);
    return;
  }
  Trace("eager-inst-debug")
      << "Asserted term " << t << " with user patterns" << std::endl;
  EagerTrie* et = eoi->getCurrentTrie(d_tdb);
  if (et == nullptr)
  {
    // no current active patterns
    return;
  }
  // if master equality engine is inconsistent, we are in conflict
  Assert(d_ee != nullptr);
  if (!d_ee->consistent())
  {
    return;
  }
  ++d_statMatchCall;
  size_t prevLemmas = d_tmpAddedLemmas;
  std::vector<Node> inst;
  EagerTermIterator eti(t);
  std::map<const EagerTrie*, std::pair<Node, Node>> failExp;
  doMatchingTrieInternal(et, eti, inst, failExp);
  if (failExp.empty())
  {
    // this term is never matchable again (unless against cd-dependent user ops)
    d_fullInstTerms.insert(t);
  }
  if (d_tmpAddedLemmas > prevLemmas)
  {
    d_qim.doPending();
  }
}

void EagerInst::doMatchingTrieInternal(
    const EagerTrie* et,
    EagerTermIterator& eti,
    std::vector<Node>& inst,
    std::map<const EagerTrie*, std::pair<Node, Node>>& failExp)
{
  if (eti.needsBacktrack())
  {
    // continue matching
    if (!eti.d_stack.empty())
    {
      Assert(et->d_pats.empty());
      // save state
      Node pt = eti.d_term;
      size_t pi = eti.d_index;
      std::pair<Node, size_t> p = eti.d_stack.back();
      // pop
      eti.pop();
      doMatchingTrieInternal(et, eti, inst, failExp);
      // restore state
      eti.d_term = pt;
      eti.d_index = pi;
      eti.d_stack.emplace_back(p);
    }
    else
    {
      // instantiate with all patterns stored on this leaf
      const std::vector<Node>& pats = et->d_pats;
      Instantiate* ie = d_qim.getInstantiate();
      std::vector<Node> instSub;
      const Node& n = eti.getOriginal();
      for (const Node& pat : pats)
      {
        std::pair<Node, Node> key(n, pat);
        if (d_instTerms.find(key) != d_instTerms.end())
        {
          continue;
        }
        Node q = TermUtil::getInstConstAttr(pat);
        Assert(!q.isNull());
        // must resize
        std::vector<Node> instq(inst.begin(),
                                inst.begin() + q[0].getNumChildren());
        if (pat.getKind() == Kind::INST_PATTERN)
        {
          std::vector<Node> ics = d_qreg.getInstantiationConstants(q);
          bool filtered = false;
          for (size_t j = 1, npats = pat.getNumChildren(); j < npats; j++)
          {
            Node pcs = pat[j].substitute(
                ics.begin(), ics.end(), instq.begin(), instq.end());
            if (d_rlvTerms.find(pcs) == d_rlvTerms.end())
            {
              filtered = true;
              break;
            }
          }
          if (filtered)
          {
            continue;
          }
        }
        if (ie->addInstantiation(
                q, instq, InferenceId::QUANTIFIERS_INST_EAGER_E_MATCHING))
        {
          d_tmpAddedLemmas++;
          d_instTerms.insert(key);
        }
        else
        {
          // dummy mark that the failure was due to entailed pattern
          failExp[et] = d_nullPair;
        }
      }
    }
    return;
  }
  Assert(et->d_pats.empty());
  const Node& tc = eti.getCurrent();
  eti.incrementChild();
  for (const std::pair<const uint64_t, EagerTrie>& c : et->d_varChildren)
  {
    uint64_t vnum = c.first;
    // not necessary?
    if (vnum >= inst.size())
    {
      inst.resize(vnum + 1);
    }
    if (!inst[vnum].isNull() && !d_qstate.areEqual(inst[vnum], tc))
    {
      addToFailExp(&c.second, failExp, inst[vnum], tc);
      continue;
    }
    // not necessary??
    Node prev = inst[vnum];
    inst[vnum] = tc;
    doMatchingTrieInternal(&c.second, eti, inst, failExp);
    inst[vnum] = prev;
  }
  for (const std::pair<const Node, EagerTrie>& c : et->d_groundChildren)
  {
    if (!d_qstate.areEqual(c.first, tc))
    {
      addToFailExp(&c.second, failExp, c.first, tc);
      continue;
    }
    doMatchingTrieInternal(&c.second, eti, inst, failExp);
  }
  eti.decrementChild();
  const std::map<Node, EagerTrie>& etng = et->d_ngroundChildren;
  if (etng.empty())
  {
    return;
  }
  // save state
  Node pt = eti.d_term;
  size_t pi = eti.d_index;
  Node op = d_tdb->getMatchOperator(tc);
  if (op.isNull())
  {
    // don't bother if we are in simple mode
    if (options().quantifiers.eagerInstSimple)
    {
      return;
    }
    /*
    std::map<Node, std::vector<Node>> terms;
    // extract terms per operator
    Assert(d_ee->hasTerm(t[i]));
    TNode r = d_ee->getRepresentative(t[i]);
    eq::EqClassIterator eqc_i = eq::EqClassIterator(r, d_ee);
    while (!eqc_i.isFinished())
    {
      Node fapp = (*eqc_i);
      Node fop = d_tdb->getMatchOperator(fapp);
      if (etng.find(fop) != etng.end())
      {
        terms[fop].emplace_back(fapp);
      }
      ++eqc_i;
    }
    if (!terms.empty())
    {
      ets.emplace_back(t, i + 1);
      std::map<Node, EagerTrie>::const_iterator itc;
      for (const std::pair<const Node, std::vector<Node>>& tp : terms)
      {
        itc = etng.find(tp.first);
        Assert(itc != etng.end());
        const EagerTrie* etc = &itc->second;
        for (const Node& tt : tp.second)
        {
          doMatchingTrieInternal(etc, n, tt, 0, inst, ets, failExp);
        }
      }
      ets.pop_back();
    }
    */
  }
  else
  {
    std::map<Node, EagerTrie>::const_iterator it = etng.find(op);
    if (it != etng.end())
    {
      // push
      eti.push();
      doMatchingTrieInternal(&it->second, eti, inst, failExp);
      eti.d_stack.pop_back();
    }
  }
  // revert state
  eti.d_term = pt;
  eti.d_index = pi;
}

void EagerInst::addToFailExp(
    const EagerTrie* et,
    std::map<const EagerTrie*, std::pair<Node, Node>>& failExp,
    const Node& a,
    const Node& b)
{
  if (!a.isConst() || !b.isConst())
  {
    failExp[et] = std::pair<Node, Node>(a, b);
  }
}

EagerOpInfo* EagerInst::getOrMkOpInfo(const Node& op, bool doMk)
{
  context::CDHashMap<Node, std::shared_ptr<EagerOpInfo>>::iterator it =
      d_userPat.find(op);
  if (it != d_userPat.end())
  {
    return it->second.get();
  }
  else if (!doMk)
  {
    return nullptr;
  }
  std::shared_ptr<EagerOpInfo> eoi = std::make_shared<EagerOpInfo>(context());
  d_userPat.insert(op, eoi);
  return eoi.get();
}

EagerWatchInfo* EagerInst::getOrMkWatchInfo(const Node& r, bool doMk)
{
  context::CDHashMap<Node, std::shared_ptr<EagerWatchInfo>>::iterator it =
      d_repWatch.find(r);
  if (it != d_repWatch.end())
  {
    return it->second.get();
  }
  else if (!doMk)
  {
    return nullptr;
  }
  std::shared_ptr<EagerWatchInfo> ewi =
      std::make_shared<EagerWatchInfo>(context());
  d_repWatch.insert(r, ewi);
  return ewi.get();
}

void EagerInst::addWatches(
    const Node& t, std::map<const EagerTrie*, std::pair<Node, Node>>& failExp)
{
  if (options().quantifiers.eagerInstWatchMode
      == options::EagerInstWatchMode::NONE)
  {
    return;
  }
  for (std::pair<const EagerTrie* const, std::pair<Node, Node>>& f : failExp)
  {
    addWatch(f.first, t, f.second.first, f.second.second);
  }
}

void EagerInst::addWatch(const EagerTrie* pat,
                         const Node& t,
                         const Node& a,
                         const Node& b)
{
  TNode ar = d_qstate.getRepresentative(a);
  TNode br = d_qstate.getRepresentative(b);
  if (br.isConst())
  {
    TNode tmp = ar;
    ar = br;
    br = tmp;
  }
  Trace("eager-inst-watch") << "Fail to match: " << t << " because " << ar
                            << " <> " << br << std::endl;
  EagerWatchInfo* ew = getOrMkWatchInfo(ar, true);
  EagerWatchList* ewl = ew->getOrMkList(br, true);
  ewl->d_matchJobs.push_back(std::pair<const EagerTrie*, Node>(pat, t));
}

void EagerInst::eqNotifyMerge(TNode t1, TNode t2)
{
  Assert(d_qstate.getRepresentative(t2) == t1);
  Trace("eager-inst-debug2")
      << "eqNotifyMerge " << t1 << " " << t2 << std::endl;
  EagerWatchInfo* ewi[2];
  std::map<Node, std::map<const EagerTrie*, std::pair<Node, Node>>> nextFails;
  bool addedInst = false;
  // look at the watch info of both equivalence classes
  for (size_t i = 0; i < 2; i++)
  {
    ewi[i] = getOrMkWatchInfo(t1, false);
    if (ewi[i] == nullptr)
    {
      continue;
    }
    Trace("eager-inst-debug2")
        << "...check watched terms of " << t1 << std::endl;
    context::CDHashMap<Node, std::shared_ptr<EagerWatchList>>& w =
        ewi[i]->d_eqWatch;
    for (context::CDHashMap<Node, std::shared_ptr<EagerWatchList>>::iterator
             itw = w.begin();
         itw != w.end();
         ++itw)
    {
      EagerWatchList* ewl = itw->second.get();
      if (!ewl->d_valid.get())
      {
        // this list was already processed by a previous merge
        continue;
      }
      if (!d_qstate.areEqual(itw->first, t2))
      {
        // if unprocessed, carry over
        if (i == 1)
        {
          // make the other if not generated, t2 was swapped from t1
          if (ewi[0] == nullptr)
          {
            ewi[0] = getOrMkWatchInfo(t2, true);
          }
          // update the representative as you go
          TNode rep = d_qstate.getRepresentative(itw->first);
          context::CDList<std::pair<const EagerTrie*, Node>>& wmj =
              ewl->d_matchJobs;
          EagerWatchList* ewlo = ewi[0]->getOrMkList(rep, true);
          context::CDList<std::pair<const EagerTrie*, Node>>& wmjo =
              ewlo->d_matchJobs;
          for (const std::pair<const EagerTrie*, Node>& p : wmj)
          {
            wmjo.push_back(p);
          }
        }
        continue;
      }
      // otherwise, we have a list of matching jobs that where waiting for this merge,
      // process them now.
      context::CDList<std::pair<const EagerTrie*, Node>>& wmj =
          ewl->d_matchJobs;
      for (const std::pair<const EagerTrie*, Node>& j : wmj)
      {
        Trace("eager-inst-watch")
            << "Since " << t1 << " and " << t2 << " merged, retry " << j.first
            << " and " << j.second << std::endl;
        // TODO: resume
      }
      // no longer valid
      ewl->d_valid = false;
    }
    if (i == 0)
    {
      // now swap
      TNode tmp = t1;
      t1 = t2;
      t2 = tmp;
    }
  }
  // do pending lemmas if added
  if (addedInst)
  {
    d_qim.doPending();
  }
  // add new watching
  for (std::pair<const Node, std::map<const EagerTrie*, std::pair<Node, Node>>>&
           nf : nextFails)
  {
    addWatches(nf.first, nf.second);
  }
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
