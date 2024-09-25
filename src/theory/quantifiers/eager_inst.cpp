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
      d_ee(nullptr),
      d_tdb(tr.getTermDatabase()),
      d_instTerms(userContext()),
      d_ownedQuants(context()),
      d_patRegister(userContext()),
      d_filteringSingleTriggers(userContext()),
      // d_etrie(context()),
      d_ppQuants(userContext()),
      d_fullInstTerms(userContext()),
      d_cdOps(context()),
      d_repWatch(context()),
      d_opInfo(context()),
      d_patInfo(context()),
      d_gdb(env, qs, tr.getTermDatabase()),
      d_statUserPats(statisticsRegistry().registerInt("EagerInst::userPats")),
      d_statUserPatsCd(
          statisticsRegistry().registerInt("EagerInst::userPatsCd")),
      d_statSinglePat(
          statisticsRegistry().registerInt("EagerInst::patternSingle")),
      d_statFilteringSinglePat(statisticsRegistry().registerInt(
          "EagerInst::patternFilteringSingle")),
      d_statMultiPat(
          statisticsRegistry().registerInt("EagerInst::patternMulti")),
      d_statWatchCount(
          statisticsRegistry().registerInt("EagerInst::watchCount")),
      d_statWatchMtCount(
          statisticsRegistry().registerInt("EagerInst::watchMtCount")),
      d_statMatchCall(statisticsRegistry().registerInt("EagerInst::matchCall")),
      d_statResumeMergeMatchCall(statisticsRegistry().registerInt(
          "EagerInst::matchResumeOnMergeCall")),
      d_statCdPatMatchCall(
          statisticsRegistry().registerInt("EagerInst::matchCdPatCall")),
      d_statMtJoinCount(
          statisticsRegistry().registerInt("EagerInst::mtJoinCount"))
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
    size_t prevLemmas = d_tmpAddedLemmas;
    registerQuant(q);
    if (d_tmpAddedLemmas > prevLemmas)
    {
      d_qim.doPending();
    }
  }
}
void EagerInst::registerQuant(const Node& q)
{
  Trace("eager-inst-register") << "Assert " << q << std::endl;
  if (q.getNumChildren() != 3)
  {
    Trace("eager-inst-warn")
        << "Unhandled quantified formula (no patterns) " << q << std::endl;
    return;
  }
  Node ipl = q[2];
  bool isPp = (d_ppQuants.find(q) != d_ppQuants.end());
  bool owner = isPp;
  bool hasPat = false;
  // ensure we have enough in the instantiation vector
  size_t nvars = q[0].getNumChildren();
  if (d_inst.size() < nvars)
  {
    d_inst.resize(nvars);
  }
  // TODO: do for any pattern selection?
  for (const Node& pat : ipl)
  {
    if (pat.getKind() != Kind::INST_PATTERN)
    {
      continue;
    }
    Node upat = getPatternFor(pat, q);
    if (upat.isNull())
    {
      owner = false;
      continue;
    }
    // TODO: statically analyze if this would lead to matching loops
    bool success = true;
    for (size_t i = 0, npats = upat.getNumChildren(); i < npats; i++)
    {
      TNode pc = upat[i];
      TNode op = d_tdb->getMatchOperator(pc);
      EagerOpInfo* eoi = getOrMkOpInfo(op, true);
      CDEagerTrie* cet = eoi->getPatternTrie();
      EagerTrie* et = cet->addPattern(d_tdb, pc);
      // can happen if not a usable trigger
      if (et == nullptr)
      {
        Trace("eager-inst-warn") << "Unhandled pattern: " << pc << std::endl;
        owner = false;
        d_patRegister[std::pair<Node, Node>(pat, q)] = d_null;
        // TODO: cleanup successful patterns????
        // for (size_t j=0; j<i; j++)
        success = false;
        break;
      }
      hasPat = true;
      if (isPp)
      {
        // not context-dependent, continue
        continue;
      }
      // otherwise, we revisit matching with all existing terms
      d_cdOps.insert(op);
      if (options().quantifiers.eagerInstCdWatch)
      {
        // match the current terms
        EagerTrie* root = cet->getCurrent(d_tdb);
        Assert(root != nullptr);
        if (eoi != nullptr)
        {
          const context::CDHashSet<Node>& gts = eoi->getGroundTerms(d_qstate);
          Trace("eager-inst-match-event")
              << "Since " << pat << " was added, revisit match with "
              << gts.size() << " terms" << std::endl;
          for (const Node& t : gts)
          {
            std::pair<Node, Node> key(t, pc);
            if (d_instTerms.find(key) != d_instTerms.end())
            {
              continue;
            }
            EagerTermIterator etip(pc);
            EagerTermIterator eti(t);
            ++d_statCdPatMatchCall;
            EagerFailExp failExp;
            doMatchingPath(root, eti, etip, failExp);
            addWatches(failExp);
          }
        }
      }
    }
    if (success)
    {
      hasPat = true;
      if (!isPp)
      {
        ++d_statUserPatsCd;
      }
      else
      {
        ++d_statUserPats;
      }
    }
    if (owner)
    {
      for (const Node& p : upat)
      {
        for (const Node& spc : p)
        {
          if (spc.getKind() != Kind::INST_CONSTANT)
          {
            owner = false;
            break;
          }
        }
        if (!owner)
        {
          break;
        }
      }
    }
  }
  if (!hasPat)
  {
    Trace("eager-inst-warn")
        << "Unhandled quantified formula " << q << std::endl;
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
  Trace("eager-inst-notify") << "notify: asserted term " << t << std::endl;
  Node op = t.getOperator();
  EagerOpInfo* eoi = getOrMkOpInfo(op, true);
  if (!eoi->addGroundTerm(d_qstate, t))
  {
    return;
  }
  if (d_fullInstTerms.find(t) != d_fullInstTerms.end())
  {
    if (d_cdOps.find(op) == d_cdOps.end())
    {
      return;
    }
  }
  Trace("eager-inst-debug")
      << "Asserted term " << t << " with user patterns" << std::endl;
  EagerTrie* root = eoi->getPatternTrie()->getCurrent(d_tdb);
  if (root == nullptr)
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
  EagerTermIterator eti(t);
  EagerFailExp failExp;
  Trace("eager-inst-match")
      << "Complete matching (upon asserted) for " << t << std::endl;
  doMatching(root, eti, failExp);
  Trace("eager-inst-match") << "...finished" << std::endl;

  if (failExp.empty())
  {
    // optimization: this term is never matchable again (unless against
    // cd-dependent user ops)
    d_fullInstTerms.insert(t);
  }
  else
  {
    addWatches(failExp);
  }
  if (d_tmpAddedLemmas > prevLemmas)
  {
    d_qim.doPending();
  }
}

void EagerInst::doMatching(const EagerTrie* et,
                           EagerTermIterator& eti,
                           EagerFailExp& failExp)
{
  if (eti.needsBacktrack())
  {
    // continue matching
    if (eti.canPop())
    {
      // save state
      std::pair<TNode, size_t> p = eti.d_stack.back();
      // pop
      eti.pop();
      doMatching(et, eti, failExp);
      // restore state
      eti.d_stack.emplace_back(p);
    }
    else
    {
      processInstantiation(et, eti, failExp);
    }
    return;
  }
  const Node& tc = eti.getCurrent();
  Trace("eager-inst-match-debug") << "  Complete matching: " << tc << std::endl;
  eti.incrementChild();
  // try all variable children
  for (const std::pair<const uint64_t, EagerTrie>& c : et->d_varChildren)
  {
    uint64_t vnum = c.first;
    Assert(vnum < d_inst.size());
    if (!d_inst[vnum].isNull() && !d_qstate.areEqual(d_inst[vnum], tc))
    {
      addToFailExp(&c.second, eti.getOriginal(), failExp, d_inst[vnum], tc);
      continue;
    }
    Node prev = d_inst[vnum];
    d_inst[vnum] = tc;
    doMatching(&c.second, eti, failExp);
    // clean up, since global
    d_inst[vnum] = prev;
  }
  for (const std::pair<const Node, EagerTrie>& c : et->d_groundChildren)
  {
    if (!d_qstate.areEqual(c.first, tc))
    {
      addToFailExp(&c.second, eti.getOriginal(), failExp, c.first, tc);
      continue;
    }
    doMatching(&c.second, eti, failExp);
  }
  eti.decrementChild();
  const std::map<Node, EagerTrie>& etng = et->d_ngroundChildren;
  if (etng.empty())
  {
    return;
  }
  Node op = d_tdb->getMatchOperator(tc);
  if (op.isNull())
  {
    // don't bother if we are in simple mode
    if (options().quantifiers.eagerInstSimple)
    {
      return;
    }
    std::map<Node, std::vector<Node>> terms;
    // extract terms per operator
    Assert(d_ee->hasTerm(tc));
    TNode r = d_ee->getRepresentative(tc);
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
      std::map<Node, EagerTrie>::const_iterator itc;
      eti.incrementChild();
      for (const std::pair<const Node, std::vector<Node>>& tp : terms)
      {
        itc = etng.find(tp.first);
        Assert(itc != etng.end());
        const EagerTrie* etc = &itc->second;
        for (const Node& tt : tp.second)
        {
          eti.push(tt);
          doMatching(etc, eti, failExp);
          eti.pop();
        }
      }
      eti.decrementChild();
    }
  }
  else
  {
    std::map<Node, EagerTrie>::const_iterator it = etng.find(op);
    if (it != etng.end())
    {
      // push
      eti.incrementChild();
      eti.push(tc);
      doMatching(&it->second, eti, failExp);
      eti.pop();
      eti.decrementChild();
    }
  }
}

void EagerInst::processInstantiation(const EagerTrie* et,
                                     EagerTermIterator& eti,
                                     EagerFailExp& failExp)
{
  const std::vector<Node>& pats = et->d_pats;
  TNode n = eti.getOriginal();
  for (const Node& pat : pats)
  {
    EagerPatternInfo* epi = getOrMkPatternInfo(pat, false);
    if (epi == nullptr)
    {
      // single trigger, ready for instantiation
      doInstantiation(pat, n, failExp);
      continue;
    }
    // for each multi-trigger this is a part of
    const std::vector<std::pair<Node, size_t>>& mctx = epi->getMultiCtx();
    EagerWatchSet failWatch;
    for (const std::pair<Node, size_t>& m : mctx)
    {
      processMultiTriggerInstantiation(m.first, m.second, n, failWatch);
    }
    for (std::pair<const TNode, std::unordered_set<TNode>>& fw : failWatch)
    {
      std::map<TNode, std::vector<std::pair<const EagerTrie*, TNode>>>& wmj =
          failExp[fw.first];
      for (TNode fwb : fw.second)
      {
        ++d_statWatchMtCount;
        wmj[fwb].emplace_back(et, n);
      }
    }
  }
}

void EagerInst::processMultiTriggerInstantiation(const Node& pat,
                                                 size_t index,
                                                 const Node& n,
                                                 EagerWatchSet& failWatch)
{
  ++d_statMtJoinCount;
  Trace("eager-inst-mt") << "Multi-trigger instantiation trigger by matching "
                         << n << " with " << pat << "[" << index << "]"
                         << std::endl;
  Assert(d_multiPatInfo.find(pat) != d_multiPatInfo.end());
  EagerMultiPatternInfo& empi = d_multiPatInfo[pat];
  std::vector<EagerPatternInfo*>& pvec = empi.d_epis;
  Assert(index < pvec.size());
  EagerPatternInfo* epi = pvec[index];
  EagerGroundTrie* egt = epi->getPartialMatches();
  const Node& q = epi->getQuantFormula();
  size_t qvars = q[0].getNumChildren();
  // check if redundant (by congruence)
  const EagerGroundTrie* egtc = egt->contains(d_qstate, d_inst, qvars);
  if (egtc != nullptr)
  {
    if (egtc->getData() != n)
    {
      Trace("eager-inst-mt") << "...congruent" << std::endl;
      // added congruent term, we are done
      return;
    }
    // otherwise already added, we process again below
    Trace("eager-inst-mt") << "...already added" << std::endl;
  }
  else
  {
    // otherwise, we add now
    egt->add(d_qstate, d_gdb.getAlloc(), d_inst, n, qvars);
    Trace("eager-inst-mt") << "...newly added" << std::endl;
  }
  // now, go back to other patterns
  EagerGtMVector pats;
  for (EagerPatternInfo* epic : pvec)
  {
    pats.emplace_back(std::vector<EagerGroundTrie*>{epic->getPartialMatches()});
  }
  Trace("eager-inst-mt") << "Do multi-trigger instantiations" << std::endl;
  processMultiTriggerInstantiations(q, pat, 0, index, pats, failWatch);
  Trace("eager-inst-mt") << "...finished" << std::endl;
}

void EagerInst::processMultiTriggerInstantiations(const Node& q,
                                                  const Node& pat,
                                                  size_t varIndex,
                                                  size_t basePatIndex,
                                                  EagerGtMVector& pats,
                                                  EagerWatchSet& failWatch)
{
  // invariant: each index of pats should be non-empty
  if (varIndex == q[0].getNumChildren())
  {
    // instantiate now, d_inst should be complete
    if (!doInstantiation(q, pat, d_null))
    {
      // TODO: ?
    }
    return;
  }
  size_t npats = pats.size();
  context::CDHashMap<Node, EagerGroundTrie*>::iterator it;
  EagerGtMVector nextPats;
  nextPats.resize(pats.size());
  // immediately populate the next pat vector for the base pattern, which
  // should be size one.
  std::vector<EagerGroundTrie*>& basep = pats[basePatIndex];
  Assert(basep.size() == 1);
  it = basep[0]->d_cmap.find(d_inst[varIndex]);
  Assert(it != basep[0]->d_cmap.end());
  nextPats[basePatIndex].emplace_back(it->second);
  // if the variable was set by the base pattern, we direct the continuing
  if (!d_inst[varIndex].isNull())
  {
    Trace("eager-inst-mt") << "* join #" << varIndex << " " << d_inst[varIndex]
                           << std::endl;
    TNode r = d_qstate.getRepresentative(d_inst[varIndex]);
    std::map<size_t, std::unordered_set<TNode>> watchFails;
    size_t minWatchIndex = 0;
    size_t minWatchSize = 0;
    bool allNonEmpty = true;
    for (size_t i = 0; i < npats; i++)
    {
      if (i == basePatIndex)
      {
        // don't process the base pattern index here
        continue;
      }
      std::vector<EagerGroundTrie*>& nps = nextPats[i];
      std::vector<EagerGroundTrie*>& p = pats[i];
      Assert(!p.empty());
      Trace("eager-inst-mt") << "Check " << p.size() << " paths for pattern ["
                             << i << "]..." << std::endl;
      // get the trie(s) we are traversing for this pattern
      std::unordered_set<TNode>& wf = watchFails[i];
      for (EagerGroundTrie* egt : p)
      {
        context::CDHashMap<Node, EagerGroundTrie*>& cmap = egt->d_cmap;
        if (cmap.empty())
        {
          // There are no matches for this pattern. This can only occur
          // at varIndex 0. Here, everything fails, nothing to watch for (we
          // are waiting to get the first match for this component pattern).
          Assert(varIndex == 0);
          Trace("eager-inst-mt")
              << "...failed (empty) #" << i << " " << pat[i] << std::endl;
          return;
        }
        it = cmap.begin();
        // if a wildcard, just continue with the child
        if (it->first.isNull())
        {
          nps.emplace_back(it->second);
          continue;
        }
        Trace("eager-inst-mt-debug")
            << "...has children " << cmap.size() << std::endl;
        // otherwise, continue with all that are equal
        for (it = cmap.begin(); it != cmap.end(); ++it)
        {
          Assert(!it->first.isNull());
          TNode rr = d_qstate.getRepresentative(it->first);
          Trace("eager-inst-mt-debug") << "Check " << it->first << std::endl;
          if (rr == r)
          {
            nps.emplace_back(it->second);
          }
          else if (!rr.isConst() || !r.isConst())
          {
            Trace("eager-inst-mt-debug")
                << "not equal: " << it->first << " " << r << std::endl;
            // those that are not equal are a potential watch
            wf.insert(rr);
          }
        }
      }
      // if nps is empty, we cannot continue
      if (nps.empty())
      {
        Trace("eager-inst-mt")
            << "...failed #" << i << " " << pat[i] << std::endl;
        allNonEmpty = false;
        // we continue to continue, since we want to find a minimal watch set?
      }
      size_t wfsize = wf.size();
      if (i == 0 || wfsize < minWatchSize)
      {
        minWatchIndex = i;
        minWatchSize = wfsize;
      }
    }
    // set up watches for the minimal failure
    std::unordered_set<TNode>& mwf = watchFails[minWatchIndex];
    for (TNode rr : mwf)
    {
      addToWatchSet(failWatch, r, rr);
    }
    // if all non-empty, we can continue
    if (allNonEmpty)
    {
      processMultiTriggerInstantiations(
          q, pat, varIndex + 1, basePatIndex, nextPats, failWatch);
    }
    return;
  }
  // if null, we consider all possibilities of what to set d_inst[varIndex] to.

  Trace("eager-inst-mt") << "* look for values #" << varIndex << std::endl;
  // Mapping representatives to the vector we would pass to pats on the next
  // call to this method.
  std::map<TNode, EagerGtMVector> nextPatRep;
  std::map<TNode, EagerGtMVector>::iterator itn;
  // an "actual" term per rep
  std::map<TNode, TNode> repUse;
  std::pair<std::map<TNode, EagerGtMVector>::iterator, bool> iret;
  bool firstTime = true;
  for (size_t i = 0; i < npats; i++)
  {
    if (i == basePatIndex)
    {
      // don't process the base pattern index here
      continue;
    }
    // for each trie we are processing for this pattern
    std::vector<EagerGroundTrie*>& p = pats[i];
    for (EagerGroundTrie* egt : p)
    {
      context::CDHashMap<Node, EagerGroundTrie*>& cmap = egt->d_cmap;
      if (cmap.empty())
      {
        // Similar to above.
        // There are no matches for this pattern. This can only occur
        // at varIndex 0. Here, everything fails, nothing to watch for (we
        // are waiting to get the first match for this component pattern).
        Assert(varIndex == 0);
        Trace("eager-inst-mt")
            << "...failed (empty) #" << i << " " << pat[i] << std::endl;
        return;
      }
      it = cmap.begin();
      if (it->first.isNull())
      {
        // if a wildcard, we will including it always
        std::vector<EagerGroundTrie*>& nps = nextPats[i];
        nps.emplace_back(it->second);
        break;
      }
      for (it = cmap.begin(); it != cmap.end(); ++it)
      {
        Assert(!it->first.isNull());
        TNode rr = d_qstate.getRepresentative(it->first);
        if (firstTime)
        {
          // if first time, we populate nextPatRep
          iret = nextPatRep.insert(
              std::pair<TNode, EagerGtMVector>(rr, EagerGtMVector()));
          if (iret.second)
          {
            iret.first->second.resize(npats);
            repUse[rr] = it->first;
          }
          iret.first->second[i].emplace_back(it->second);
          continue;
        }
        // if not first time, combine with a previous
        itn = nextPatRep.find(rr);
        if (itn != nextPatRep.end())
        {
          itn->second[i].emplace_back(it->second);
        }
      }
    }
    firstTime = false;
  }
  // now go back and try possibilities
  for (std::pair<const TNode, EagerGtMVector>& npr : nextPatRep)
  {
    Trace("eager-inst-mt") << "  * rep : " << npr.first << std::endl;
    EagerGtMVector& evec = npr.second;
    bool allNonEmpty = true;
    // fist check that all simultanesouly match
    for (size_t i = 0; i < npats; i++)
    {
      std::vector<EagerGroundTrie*>& vec = evec[i];
      if (vec.empty())
      {
        // maybe a wildcard
        std::vector<EagerGroundTrie*>& wcvec = nextPats[i];
        if (wcvec.empty())
        {
          Trace("eager-inst-mt")
              << "...failed #" << i << " " << pat[i] << std::endl;
          allNonEmpty = false;
          break;
        }
        // add wildcards (and base) to vec
        vec.insert(vec.end(), wcvec.begin(), wcvec.end());
      }
    }
    // if all non-empty, this this value
    if (allNonEmpty)
    {
      Assert(repUse.find(npr.first) != repUse.end());
      d_inst[varIndex] = repUse[npr.first];
      processMultiTriggerInstantiations(
          q, pat, varIndex + 1, basePatIndex, evec, failWatch);
    }
    // note that we don't need to set up watches here.
  }
  // cleanup
  d_inst[varIndex] = d_null;
}

bool EagerInst::doInstantiation(const Node& pat, TNode n, EagerFailExp& failExp)
{
  Trace("eager-inst-inst") << "Instantiate based on " << pat << std::endl;
  Node q = TermUtil::getInstConstAttr(pat);
  Assert(!q.isNull());
  Assert(q[0].getNumChildren() >= d_inst.size());
  if (!doInstantiation(q, pat, n))
  {
    // dummy mark that the failure was due to entailed pattern
    failExp[d_null][d_null].emplace_back();
    return false;
  }
  return true;
}

bool EagerInst::doInstantiation(const Node& q, const Node& pat, const Node& n)
{
  Assert(!q.isNull());
  Assert(q[0].getNumChildren() >= d_inst.size());
  std::pair<Node, Node> key(n, pat);
  if (!n.isNull())
  {
    if (d_instTerms.find(key) != d_instTerms.end())
    {
      // already instantiated
      return true;
    }
  }
  // TODO: context dependent instantiation
  // must resize now
  std::vector<Node> instq(d_inst.begin(),
                          d_inst.begin() + q[0].getNumChildren());
  Trace("eager-inst-inst") << "Instantiation :  " << instq << std::endl;
  Instantiate* ie = d_qim.getInstantiate();
  if (ie->addInstantiation(
          q, instq, InferenceId::QUANTIFIERS_INST_EAGER_E_MATCHING))
  {
    d_tmpAddedLemmas++;
    if (!n.isNull())
    {
      d_instTerms.insert(key);
    }
    return true;
  }
  return false;
}

void EagerInst::resumeMatching(const EagerTrie* pat,
                               EagerTermIterator& eti,
                               const EagerTrie* tgt,
                               EagerTermIterator& etip,
                               EagerFailExp& failExp)
{
  // TODO: make non-recursive
  if (pat == tgt)
  {
    // we have now fully resumed the match, now go to main matching procedure
    Trace("eager-inst-match") << "Complete matching (upon resume) for "
                              << eti.getOriginal() << std::endl;
    doMatching(pat, eti, failExp);
    Trace("eager-inst-match") << "...finished" << std::endl;
    return;
  }
  // The following traverses a single path of the eager trie
  // to resume matching at tgt. This is guided by an example
  // pattern that was stored at tgt and is being traversed with etip.
  // We assume that all steps of the matching succeed below.
  if (eti.needsBacktrack())
  {
    Assert(eti.canPop());
    eti.pop();
    etip.pop();
    resumeMatching(pat, eti, tgt, etip, failExp);
    return;
  }
  const Node& tc = eti.getCurrent();
  const Node& pc = etip.getCurrent();
  eti.incrementChild();
  etip.incrementChild();
  if (pc.getKind() == Kind::INST_CONSTANT)
  {
    const std::map<uint64_t, EagerTrie>& pv = pat->d_varChildren;
    uint64_t vnum = TermUtil::getInstVarNum(pc);
    Assert(vnum < d_inst.size());
    Node prev = d_inst[vnum];
    d_inst[vnum] = tc;
    std::map<uint64_t, EagerTrie>::const_iterator it = pv.find(vnum);
    Assert(it != pv.end());
    resumeMatching(&it->second, eti, tgt, etip, failExp);
    // clean up, since global
    d_inst[vnum] = prev;
  }
  else if (!TermUtil::hasInstConstAttr(pc))
  {
    const std::map<Node, EagerTrie>& pg = pat->d_groundChildren;
    std::map<Node, EagerTrie>::const_iterator it = pg.find(pc);
    Assert(it != pg.end());
    resumeMatching(&it->second, eti, tgt, etip, failExp);
  }
  else
  {
    eti.push(tc);
    etip.push(pc);
    const Node& op = d_tdb->getMatchOperator(pc);
    const std::map<Node, EagerTrie>& png = pat->d_ngroundChildren;
    std::map<Node, EagerTrie>::const_iterator it = png.find(op);
    Assert(it != png.end());
    resumeMatching(&it->second, eti, tgt, etip, failExp);
  }
}
void EagerInst::doMatchingPath(const EagerTrie* et,
                               EagerTermIterator& eti,
                               EagerTermIterator& etip,
                               EagerFailExp& failExp)
{
  // TODO: make non-recursive
  if (eti.needsBacktrack())
  {
    if (eti.canPop())
    {
      // pop
      eti.pop();
      etip.pop();
      doMatchingPath(et, eti, etip, failExp);
      // don't need to restore state
    }
    else
    {
      // instantiate with all patterns stored on this leaf
      TNode n = eti.getOriginal();
      const std::vector<Node>& pats = et->d_pats;
      for (const Node& pat : pats)
      {
        doInstantiation(pat, n, failExp);
      }
    }
    return;
  }
  const Node& tc = eti.getCurrent();
  const Node& pc = etip.getCurrent();
  Trace("eager-inst-match-debug")
      << "  Path matching: " << tc << " " << pc << std::endl;
  Assert(tc.getType() == pc.getType());
  eti.incrementChild();
  etip.incrementChild();
  if (pc.getKind() == Kind::INST_CONSTANT)
  {
    uint64_t vnum = TermUtil::getInstVarNum(pc);
    const std::map<uint64_t, EagerTrie>& pv = et->d_varChildren;
    std::map<uint64_t, EagerTrie>::const_iterator it = pv.find(vnum);
    Assert(it != pv.end());
    Assert(vnum < d_inst.size());
    if (!d_inst[vnum].isNull() && !d_qstate.areEqual(d_inst[vnum], tc))
    {
      addToFailExp(&it->second, eti.getOriginal(), failExp, d_inst[vnum], tc);
      return;
    }
    Node prev = d_inst[vnum];
    d_inst[vnum] = tc;
    doMatchingPath(&it->second, eti, etip, failExp);
    // clean up, since global
    d_inst[vnum] = prev;
  }
  else if (!TermUtil::hasInstConstAttr(pc))
  {
    const std::map<Node, EagerTrie>& pg = et->d_groundChildren;
    std::map<Node, EagerTrie>::const_iterator it = pg.find(pc);
    Assert(it != pg.end());
    if (!d_qstate.areEqual(pc, tc))
    {
      addToFailExp(&it->second, eti.getOriginal(), failExp, pc, tc);
      return;
    }
    doMatchingPath(&it->second, eti, etip, failExp);
  }
  else
  {
    const Node& op = d_tdb->getMatchOperator(pc);
    if (d_tdb->getMatchOperator(tc) != op)
    {
      return;
    }
    eti.push(tc);
    etip.push(pc);
    const std::map<Node, EagerTrie>& png = et->d_ngroundChildren;
    std::map<Node, EagerTrie>::const_iterator it = png.find(op);
    Assert(it != png.end());
    doMatchingPath(&it->second, eti, etip, failExp);
  }
}

void EagerInst::addToFailExp(const EagerTrie* et,
                             TNode t,
                             EagerFailExp& failExp,
                             const Node& a,
                             const Node& b)
{
  TNode ar = d_qstate.getRepresentative(a);
  TNode br = d_qstate.getRepresentative(b);
  if (ar.isConst())
  {
    if (br.isConst())
    {
      return;
    }
  }
  else if (br.isConst() || br < ar)
  {
    failExp[br][ar].emplace_back(et, t);
    return;
  }
  failExp[ar][br].emplace_back(et, t);
}

void EagerInst::addToWatchSet(EagerWatchSet& ews, TNode a, TNode b)
{
  TNode ar = d_qstate.getRepresentative(a);
  TNode br = d_qstate.getRepresentative(b);
  if (ar.isConst())
  {
    if (br.isConst())
    {
      return;
    }
  }
  else if (br.isConst() || br < ar)
  {
    ews[br].insert(ar);
    return;
  }
  ews[ar].insert(br);
}

EagerOpInfo* EagerInst::getOrMkOpInfo(const Node& op, bool doMk)
{
  context::CDHashMap<Node, std::shared_ptr<EagerOpInfo>>::iterator it =
      d_opInfo.find(op);
  if (it != d_opInfo.end())
  {
    return it->second.get();
  }
  else if (!doMk)
  {
    return nullptr;
  }
  EagerGroundDb* gdbu = nullptr;
  if (options().quantifiers.eagerInstGroundCongruence)
  {
    gdbu = &d_gdb;
  }
  std::shared_ptr<EagerOpInfo> eoi =
      std::make_shared<EagerOpInfo>(context(), op, gdbu);
  d_opInfo.insert(op, eoi);
  return eoi.get();
}

EagerRepInfo* EagerInst::getOrMkRepInfo(const Node& r, bool doMk)
{
  context::CDHashMap<Node, std::shared_ptr<EagerRepInfo>>::iterator it =
      d_repWatch.find(r);
  if (it != d_repWatch.end())
  {
    return it->second.get();
  }
  else if (!doMk)
  {
    return nullptr;
  }
  std::shared_ptr<EagerRepInfo> ewi = std::make_shared<EagerRepInfo>(context());
  d_repWatch.insert(r, ewi);
  return ewi.get();
}

EagerPatternInfo* EagerInst::getOrMkPatternInfo(const Node& pat, bool doMk)
{
  context::CDHashMap<Node, std::shared_ptr<EagerPatternInfo>>::iterator it =
      d_patInfo.find(pat);
  if (it != d_patInfo.end())
  {
    return it->second.get();
  }
  else if (!doMk)
  {
    return nullptr;
  }
  const Node& q = TermUtil::getInstConstAttr(pat);
  std::shared_ptr<EagerPatternInfo> epi =
      std::make_shared<EagerPatternInfo>(context(), q);
  d_patInfo.insert(pat, epi);
  return epi.get();
}

EagerTrie* EagerInst::getCurrentTrie(const Node& op)
{
  EagerOpInfo* eoi = getOrMkOpInfo(op, false);
  if (eoi == nullptr)
  {
    return nullptr;
  }
  CDEagerTrie* cet = eoi->getPatternTrie();
  return cet->getCurrent(d_tdb);
}

void EagerInst::addWatches(EagerFailExp& failExp)
{
  if (options().quantifiers.eagerInstWatchMode
      == options::EagerInstWatchMode::NONE)
  {
    return;
  }
  d_statWatchCount += failExp.size();
  for (const std::pair<
           const TNode,
           std::map<TNode, std::vector<std::pair<const EagerTrie*, TNode>>>>&
           f : failExp)
  {
    // if a dummy mark
    if (f.first.isNull())
    {
      continue;
    }
    EagerRepInfo* ew = getOrMkRepInfo(f.first, true);
    for (const std::pair<const TNode,
                         std::vector<std::pair<const EagerTrie*, TNode>>>& ff :
         f.second)
    {
      EagerWatchList* ewl = ew->getOrMkList(ff.first, true);
      for (const std::pair<const EagerTrie*, TNode>& fmj : ff.second)
      {
        Trace("eager-inst-watch")
            << "-- watch merge " << f.first << " " << ff.first
            << " to resume matching with " << fmj.second << std::endl;
        ewl->d_matchJobs.emplace_back(fmj);
      }
    }
  }
}

void EagerInst::eqNotifyMerge(TNode t1, TNode t2)
{
  Assert(d_qstate.getRepresentative(t2) == t1);
  Trace("eager-inst-debug2")
      << "eqNotifyMerge " << t1 << " " << t2 << std::endl;
  Trace("eager-inst-notify")
      << "notify: merge " << t1 << " " << t2 << std::endl;
  EagerRepInfo* ewi[2];
  EagerFailExp nextFails;
  bool addedInst = false;
  std::map<const EagerTrie*, std::unordered_set<TNode>> processed;
  std::pair<std::unordered_set<TNode>::iterator, bool> iret;
  // look at the watch info of both equivalence classes
  for (size_t i = 0; i < 2; i++)
  {
    ewi[i] = getOrMkRepInfo(t1, false);
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
            ewi[0] = getOrMkRepInfo(t2, true);
          }
          // update the representative as you go
          TNode rep = d_qstate.getRepresentative(itw->first);
          context::CDList<std::pair<const EagerTrie*, TNode>>& wmj =
              ewl->d_matchJobs;
          EagerWatchList* ewlo = ewi[0]->getOrMkList(rep, true);
          context::CDList<std::pair<const EagerTrie*, TNode>>& wmjo =
              ewlo->d_matchJobs;
          for (const std::pair<const EagerTrie*, TNode>& p : wmj)
          {
            wmjo.push_back(p);
          }
        }
        continue;
      }
      // otherwise, we have a list of matching jobs that where waiting for this
      // merge, process them now.
      context::CDList<std::pair<const EagerTrie*, TNode>>& wmj =
          ewl->d_matchJobs;
      for (const std::pair<const EagerTrie*, TNode>& j : wmj)
      {
        // don't process duplicates
        std::unordered_set<TNode>& p = processed[j.first];
        iret = p.insert(j.second);
        if (!iret.second)
        {
          continue;
        }
        Assert(!j.first->d_pats.empty());
        const Node& pat = j.first->d_pats[0];
        Assert(!pat.isNull());
        TNode patOp = d_tdb->getMatchOperator(pat);
        Assert(!patOp.isNull());
        EagerTrie* root = getCurrentTrie(patOp);
        if (root == nullptr)
        {
          continue;
        }
        TNode t = j.second;
        Trace("eager-inst-match-event")
            << "Since " << t1 << " and " << t2 << " merged, retry " << j.first
            << " and " << j.second << ", resume pattern is " << pat
            << std::endl;
        EagerTermIterator etip(pat);
        EagerTermIterator eti(t);
        ++d_statResumeMergeMatchCall;
        Trace("eager-inst-match") << "Resume match (upon merge) for "
                                  << eti.getOriginal() << std::endl;
        resumeMatching(root, eti, j.first, etip, nextFails);
        Trace("eager-inst-match") << "...finished" << std::endl;
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
  addWatches(nextFails);
}

Node EagerInst::getPatternFor(const Node& pat, const Node& q)
{
  Assert(pat.getKind() == Kind::INST_PATTERN);
  std::pair<Node, Node> key(pat, q);
  NodePairMap::iterator it = d_patRegister.find(key);
  if (it != d_patRegister.end())
  {
    return it->second;
  }
  Node pati = d_qreg.substituteBoundVariablesToInstConstants(pat, q);
  Trace("eager-inst-register") << "Register pattern: " << pati << std::endl;
  size_t npats = pati.getNumChildren();
  Node upat = pati;
  if (npats > 1)
  {
    // TODO: more heuristics, e.g. most constrained trigger
    bool isFiltering = false;
    for (size_t i = 0; i < npats; i++)
    {
      if (!d_qreg.hasAllInstantiationConstants(pati[i], q))
      {
        continue;
      }
      // TODO: eliminate this heuristic
      if (i != 0)
      {
        // reorder to process single trigger first
        std::vector<Node> ppc(pati.begin(), pati.end());
        Node tmp = ppc[0];
        ppc[0] = ppc[i];
        ppc[i] = tmp;
        upat = nodeManager()->mkNode(Kind::INST_PATTERN, ppc);
      }
      d_filteringSingleTriggers.insert(upat);
      Trace("eager-inst-register")
          << "Filtering single trigger: " << upat << std::endl;
      isFiltering = true;
      break;
    }
    if (isFiltering)
    {
      ++d_statFilteringSinglePat;
    }
    else
    {
      ++d_statMultiPat;
    }
    // set the multi-pattern contexts
    EagerMultiPatternInfo& empi = d_multiPatInfo[pati];
    Assert(empi.d_epis.empty());
    for (size_t i = 0; i < npats; i++)
    {
      EagerPatternInfo* epi = getOrMkPatternInfo(pati[i], true);
      epi->addMultiTriggerContext(pati, i);
      empi.d_epis.emplace_back(epi);
    }
  }
  else
  {
    ++d_statSinglePat;
  }
  d_patRegister.insert(key, upat);
  return upat;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
