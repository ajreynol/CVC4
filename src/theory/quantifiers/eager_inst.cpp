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

void EagerWatchList::add(const EagerTrie* et, const std::vector<Node>& t)
{
  d_matchJobs.push_back(std::pair<const EagerTrie*, std::vector<Node>>(et, t));
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

EagerOpInfo::EagerOpInfo(context::Context* c,
                         const Node& op,
                         EagerGroundDb* gdb)
    : d_galloc(nullptr),
      d_gtrie(nullptr),
      d_rlvTerms(c),
      d_rlvTermsWaiting(c),
      d_active(c, false),
      d_ewl(c)
{
  if (gdb != nullptr)
  {
    d_galloc = gdb->getAlloc();
    d_gtrie = gdb->getTrie(op);
  }
}

bool EagerOpInfo::addGroundTerm(QuantifiersState& qs, const Node& n)
{
  if (d_gtrie == nullptr)
  {
    d_rlvTerms.insert(n);
    return true;
  }
  if (!d_active.get())
  {
    // index now
    return addGroundTermInternal(qs, n);
  }
  d_rlvTermsWaiting.insert(n);
  return false;
}

bool EagerOpInfo::addGroundTermInternal(QuantifiersState& qs, const Node& n)
{
  Assert(d_gtrie != nullptr);
  if (d_gtrie->add(qs, d_galloc, n))
  {
    d_rlvTerms.insert(n);
    return true;
  }
  return false;
}

void EagerOpInfo::setActive(QuantifiersState& qs)
{
  Assert(!d_active.get());
  for (const Node& nw : d_rlvTermsWaiting)
  {
    addGroundTerm(qs, nw);
  }
}

bool EagerOpInfo::isRelevant(QuantifiersState& qs,
                             const std::vector<Node>& args) const
{
  Assert(d_gtrie != nullptr);
  return d_gtrie->contains(qs, args);
}

CDEagerTrie::CDEagerTrie(context::Context* c) : d_pats(c) {}

EagerTrie* CDEagerTrie::addPattern(TermDb* tdb, const Node& pat)
{
  Trace("eager-inst-pattern") << "add pat: " << pat << std::endl;
  makeCurrent(tdb);
  d_pats.push_back(pat);
  d_triePats.emplace_back(pat);
  return d_trie.add(tdb, pat);
}

EagerTrie* CDEagerTrie::getCurrent(TermDb* tdb)
{
  makeCurrent(tdb);
  return &d_trie;
}

void CDEagerTrie::makeCurrent(TermDb* tdb)
{
  size_t i = d_triePats.size();
  size_t tsize = d_pats.size();
  // clean up any stale patterns that appear in the trie
  while (i > tsize)
  {
    i--;
    Node pat = d_triePats[i];
    Trace("eager-inst-pattern") << "remove pat: " << pat << std::endl;
    d_trie.erase(tdb, pat);
  }
  d_triePats.resize(tsize);
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
      d_patRegister(userContext()),
      d_filteringSingleTriggers(userContext()),
      d_etrie(context()),
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
      d_statMatchCall(statisticsRegistry().registerInt("EagerInst::matchCall")),
      d_statMatchContinueCall(
          statisticsRegistry().registerInt("EagerInst::matchContinueCall")),
      d_statWatchCount(
          statisticsRegistry().registerInt("EagerInst::watchCount")),
      d_statResumeMergeMatchCall(statisticsRegistry().registerInt(
          "EagerInst::matchResumeOnMergeCall")),
      d_statResumeAssertMatchCall(statisticsRegistry().registerInt(
          "EagerInst::matchResumeOnAssertCall")),
      d_statCdPatMatchCall(
          statisticsRegistry().registerInt("EagerInst::matchCdPatCall"))
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
    EagerTrie* et = d_etrie.addPattern(d_tdb, upat);
    // can happen if not a usable trigger
    if (et == nullptr)
    {
      Trace("eager-inst-warn") << "Unhandled pattern: " << upat << std::endl;
      owner = false;
      d_patRegister[std::pair<Node, Node>(pat, q)] = d_null;
      continue;
    }
    hasPat = true;
    if (!isPp)
    {
      Node op = d_tdb->getMatchOperator(upat[0]);
      d_cdOps.insert(op);
      ++d_statUserPatsCd;
      if (options().quantifiers.eagerInstCdWatch)
      {
        // match the current terms
        EagerTrie* root = d_etrie.getCurrent(d_tdb);
        Assert(root != nullptr);
        EagerOpInfo* eoi = getOrMkOpInfo(op, false);
        if (eoi != nullptr)
        {
          const context::CDHashSet<Node>& gts = eoi->getGroundTerms();
          Trace("eager-inst-match-event")
              << "Since " << upat << " was added, revisit match with "
              << gts.size() << " terms" << std::endl;
          for (const Node& t : gts)
          {
            std::pair<Node, Node> key(t, upat);
            if (d_instTerms.find(key) != d_instTerms.end())
            {
              continue;
            }
            EagerTermIterator etip(upat);
            std::vector<Node> ts{t};
            EagerTermIterator eti(ts);
            ++d_statCdPatMatchCall;
            EagerFailExp failExp;
            doMatchingPath(root, eti, etip, failExp);
            addWatches(failExp);
          }
        }
      }
    }
    else
    {
      ++d_statUserPats;
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
  EagerTrie* root = d_etrie.getCurrent(d_tdb);
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
  std::vector<Node> ts{t};
  EagerTermIterator eti(ts);
  EagerFailExp failExp;
  Trace("eager-inst-match")
      << "Complete matching (upon asserted) for " << t << std::endl;
  doMatching(root, eti, failExp);
  Trace("eager-inst-match") << "...finished" << std::endl;

  // Also see if this triggers progress on any partially completed
  // multi-triggers
  EagerWatchList& ewl = eoi->getEagerWatchList();
  context::CDList<std::pair<const EagerTrie*, std::vector<Node>>>& wmj =
      ewl.d_matchJobs;
  for (const std::pair<const EagerTrie*, std::vector<Node>>& j : wmj)
  {
    std::vector<Node> tsr = j.second;
    tsr.push_back(t);
    Assert(!j.first->d_pats.empty());
    const Node& pat = j.first->d_pats[0];
    Assert(!pat.isNull());
    Trace("eager-inst-match-event")
        << "Since " << t << " was added, resume " << j.first << " and " << tsr
        << ", resume pattern is " << pat << std::endl;
    EagerTermIterator etipr(pat);
    EagerTermIterator etir(tsr);
    ++d_statResumeAssertMatchCall;
    Trace("eager-inst-match") << "Resume match (upon new term) for "
                              << etir.getOriginal() << std::endl;
    resumeMatching(root, etir, j.first, etipr, failExp);
    Trace("eager-inst-match") << "...finished" << std::endl;
  }

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
      std::pair<std::vector<Node>, size_t> p = eti.d_stack.back();
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
    // not necessary?
    if (vnum >= d_inst.size())
    {
      d_inst.resize(vnum + 1);
    }
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
  const std::vector<Node>& n = eti.getOriginal();
#if 0
  for (const Node& pat : pats)
  {
    EagerPatternInfo* epi = getOrMkPatternInfo(pat, false);
    if (epi==nullptr)
    {
      // single trigger, ready for instantiation
      doInstantiation(pat, n, failExp);
      continue;
    }
    Assert (n.size()==1); // FIXME: will go away
    // for each multi-trigger this is a part of
    const std::vector<std::pair<Node, size_t>>& mctx = epi->getMultiCtx();
    for (const std::pair<Node, size_t>& m : mctx)
    {
      processMultiTriggerInstantiation(epi, m.first, m.second, n[0], failExp);
    }
  }
#endif
  const std::map<Node, EagerTrie>& etng = et->d_ngroundChildren;
  bool needsGeneralMatching = false;
  Trace("ajr-temp") << "Matched " << eti.getOriginal() << std::endl;
  Trace("ajr-temp") << "Patterns " << pats << std::endl;
  // instantiate with all patterns stored on this leaf
  for (const Node& pat : pats)
  {
    if (pat.getNumChildren() == n.size())
    {
      doInstantiation(pat, n, failExp);
      continue;
    }
    else if (n.size() == 1)
    {
      if (d_filteringSingleTriggers.find(pat)
          != d_filteringSingleTriggers.end())
      {
        // if relevant suffix, we are done
        if (isRelevantSuffix(pat, n))
        {
          Trace("ajr-temp") << "...success inst fst" << std::endl;
          doInstantiation(pat, n, failExp);
          continue;
        }
        Trace("ajr-temp") << "...fail inst" << std::endl;
      }
    }
    // TODO: only continue with true multi-triggers
    needsGeneralMatching = true;
  }
  if (needsGeneralMatching)
  {
    Trace("ajr-temp") << "Needs gen matching " << eti.getOriginal()
                      << std::endl;
    // also process potential multi triggers
    for (const std::pair<const Node, EagerTrie>& ng : etng)
    {
      EagerOpInfo* eoi = getOrMkOpInfo(ng.first, true);
      const EagerTrie* etn = &ng.second;
      const context::CDHashSet<Node>& gts = eoi->getGroundTerms();
      Trace("eager-inst-match-debug")
          << "Prefix multi-trigger matched for " << n
          << ", continue match with " << gts.size() << " " << ng.first
          << " terms" << std::endl;
      for (const Node& t : gts)
      {
        ++d_statMatchContinueCall;
        Trace("eager-inst-match")
            << "Complete matching (upon multi-trigger prefix "
            << eti.getOriginal() << ") for " << t << std::endl;
        eti.pushOriginal(t);
        doMatching(etn, eti, failExp);
        eti.popOriginal();
        Trace("eager-inst-match") << "...finished" << std::endl;
      }
      // also set up an assert watch
      EagerWatchList& ewl = eoi->getEagerWatchList();
      ewl.add(etn, eti.getOriginal());
      Trace("eager-inst-watch") << "-- watch asserted " << ng.first
                                << " terms to resume matching with "
                                << eti.getOriginal() << std::endl;
    }
  }
  else if (!etng.empty())
  {
    Trace("ajr-temp") << "Avoid gen matching " << eti.getOriginal()
                      << std::endl;
  }
}

void EagerInst::processMultiTriggerInstantiation(EagerPatternInfo* epi,
                                                 const Node& pat,
                                                 size_t index,
                                                 const Node& n,
                                                 EagerFailExp& failExp)
{
  EagerGroundTrie* egt = epi->getPartialMatches();
  const Node& q = epi->getQuantFormula();
  size_t qvars = q.getNumChildren();
  // check if redundant (by congruence)
  const EagerGroundTrie* egtc = egt->contains(d_qstate, d_inst, qvars);
  if (egtc != nullptr)
  {
    if (egtc->getData() != n)
    {
      // added congruent term, we are done
      return;
    }
    // otherwise already added, we process again below
  }
  else
  {
    // otherwise, we add now
    egt->add(d_qstate, d_gdb.getAlloc(), d_inst, n, qvars);
  }
}

bool EagerInst::isRelevantSuffix(const Node& pat, const std::vector<Node>& n)
{
  if (n.size() < pat.getNumChildren())
  {
    Node q = TermUtil::getInstConstAttr(pat);
    Assert(!q.isNull());
    Assert(q[0].getNumChildren() >= d_inst.size());
    // must resize
    std::vector<Node> instq(d_inst.begin(),
                            d_inst.begin() + q[0].getNumChildren());
    Trace("eager-inst-inst")
        << "Ensure the instantiation is filtered..." << std::endl;
    const std::vector<Node>& ics = d_qreg.getInstantiationConstants(q);
    for (size_t j = n.size(), npats = pat.getNumChildren(); j < npats; j++)
    {
      Node pcs =
          pat[j].substitute(ics.begin(), ics.end(), instq.begin(), instq.end());
      if (!isRelevantTerm(pcs))
      {
        return false;
      }
    }
  }
  return true;
}

bool EagerInst::doInstantiation(const Node& pat,
                                const std::vector<Node>& n,
                                EagerFailExp& failExp)
{
  Assert(!n.empty());
  Trace("eager-inst-inst") << "Instantiate based on " << pat << std::endl;
  std::pair<Node, Node> key(n[0], pat);
  if (n.size() == 1)
  {
    if (d_instTerms.find(key) != d_instTerms.end())
    {
      return false;
    }
  }
  Instantiate* ie = d_qim.getInstantiate();
  Node q = TermUtil::getInstConstAttr(pat);
  Assert(!q.isNull());
  Assert(q[0].getNumChildren() >= d_inst.size());
  // must resize
  std::vector<Node> instq(d_inst.begin(),
                          d_inst.begin() + q[0].getNumChildren());
  Trace("eager-inst-inst") << "Instantiation :  " << instq << std::endl;
  if (ie->addInstantiation(
          q, instq, InferenceId::QUANTIFIERS_INST_EAGER_E_MATCHING))
  {
    d_tmpAddedLemmas++;
    if (n.size() == 1)
    {
      d_instTerms.insert(key);
    }
    return true;
  }
  // dummy mark that the failure was due to entailed pattern
  failExp[d_null][d_null].emplace_back();
  return false;
}

void EagerInst::resumeMatching(const EagerTrie* pat,
                               EagerTermIterator& eti,
                               const EagerTrie* tgt,
                               EagerTermIterator& etip,
                               EagerFailExp& failExp)
{
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
    if (vnum >= d_inst.size())
    {
      d_inst.resize(vnum + 1);
    }
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
      const std::vector<Node>& n = eti.getOriginal();
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
    if (vnum >= d_inst.size())
    {
      d_inst.resize(vnum + 1);
    }
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
                             const std::vector<Node>& ts,
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
  else if (br.isConst())
  {
    failExp[br][ar].emplace_back(et, ts);
    return;
  }
  failExp[ar][br].emplace_back(et, ts);
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

void EagerInst::addWatches(EagerFailExp& failExp)
{
  if (options().quantifiers.eagerInstWatchMode
      == options::EagerInstWatchMode::NONE)
  {
    return;
  }
  for (const std::pair<const Node,
                       std::map<Node,
                                std::vector<std::pair<const EagerTrie*,
                                                      std::vector<Node>>>>>& f :
       failExp)
  {
    // if a dummy mark
    if (f.first.isNull())
    {
      continue;
    }
    EagerWatchInfo* ew = getOrMkWatchInfo(f.first, true);
    for (const std::pair<
             const Node,
             std::vector<std::pair<const EagerTrie*, std::vector<Node>>>>& ff :
         f.second)
    {
      EagerWatchList* ewl = ew->getOrMkList(ff.first, true);
      for (const std::pair<const EagerTrie*, std::vector<Node>>& fmj :
           ff.second)
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
  EagerWatchInfo* ewi[2];
  EagerFailExp nextFails;
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
          context::CDList<std::pair<const EagerTrie*, std::vector<Node>>>& wmj =
              ewl->d_matchJobs;
          EagerWatchList* ewlo = ewi[0]->getOrMkList(rep, true);
          context::CDList<std::pair<const EagerTrie*, std::vector<Node>>>&
              wmjo = ewlo->d_matchJobs;
          for (const std::pair<const EagerTrie*, std::vector<Node>>& p : wmj)
          {
            wmjo.push_back(p);
          }
        }
        continue;
      }
      // otherwise, we have a list of matching jobs that where waiting for this
      // merge, process them now.
      context::CDList<std::pair<const EagerTrie*, std::vector<Node>>>& wmj =
          ewl->d_matchJobs;
      EagerTrie* root = d_etrie.getCurrent(d_tdb);
      for (const std::pair<const EagerTrie*, std::vector<Node>>& j : wmj)
      {
        const std::vector<Node>& t = j.second;
        Assert(!j.first->d_pats.empty());
        const Node& pat = j.first->d_pats[0];
        Assert(!pat.isNull());
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

bool EagerInst::isRelevantTerm(const Node& t)
{
  // Node op = d_tdb->getMatchOperator(t);
  // std::vector<TNode> args(t.begin(), t.end());
  // return isRelevant(op, args);
  Node op = d_tdb->getMatchOperator(t);
  EagerOpInfo* eoi = getOrMkOpInfo(op, false);
  if (eoi == nullptr)
  {
    return false;
  }
  const context::CDHashSet<Node>& gts = eoi->getGroundTerms();
  return gts.find(t) != gts.end();
}

bool EagerInst::isRelevant(const Node& op, const std::vector<Node>& args)
{
  EagerOpInfo* eoi = getOrMkOpInfo(op, false);
  if (eoi == nullptr)
  {
    return false;
  }
  return eoi->isRelevant(d_qstate, args);
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
    for (size_t i = 0; i < npats; i++)
    {
      EagerPatternInfo* epi = getOrMkPatternInfo(pati[i], true);
      epi->addMultiTriggerContext(pati, i);
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
