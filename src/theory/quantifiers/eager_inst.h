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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER_INST_H
#define CVC5__THEORY__QUANTIFIERS__EAGER_INST_H

#include "smt/env_obj.h"
#include "theory/quantifiers/eager/eager_ground_trie.h"
#include "theory/quantifiers/eager/eager_trie.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class EagerWatchList
{
 public:
  EagerWatchList(context::Context* c) : d_valid(c, true), d_matchJobs(c) {}
  void add(const EagerTrie* et, const std::vector<Node>& t);
  context::CDO<bool> d_valid;
  context::CDList<std::pair<const EagerTrie*, std::vector<Node>>> d_matchJobs;
};

class EagerWatchInfo
{
 public:
  EagerWatchInfo(context::Context* c) : d_eqWatch(c), d_ctx(c) {}
  EagerWatchList* getOrMkList(const Node& r, bool doMk);
  /**
   * Mapping from terms in the above list to the term we are waiting the
   * equivalence class to become equal to.
   */
  context::CDHashMap<Node, std::shared_ptr<EagerWatchList>> d_eqWatch;

 private:
  context::Context* d_ctx;
};

class EagerOpInfo
{
 public:
  EagerOpInfo(context::Context* c, const Node& op, EagerGroundDb* gdb);
  /** Add ground term */
  bool addGroundTerm(QuantifiersState& qs, const Node& n);
  /** Get ground terms */
  const context::CDHashSet<Node>& getGroundTerms() const { return d_rlvTerms; }
  /** Set active */
  void setActive(QuantifiersState& qs);
  /**
   * These are the set of partially completed multi-trigger matches that are
   * waiting on new terms for this operator.
   */
  EagerWatchList& getEagerWatchList() { return d_ewl; }
  /** */
  bool isRelevant(QuantifiersState& qs, const std::vector<Node>& args) const;

 private:
  /** Add ground term */
  bool addGroundTermInternal(QuantifiersState& qs, const Node& n);
  /** For ground term indexing */
  EagerGroundTrieAllocator* d_galloc;
  EagerGroundTrie* d_gtrie;
  /** Relevant terms for this in the current context */
  context::CDHashSet<Node> d_rlvTerms;
  /** Relevant terms for this in the current context */
  context::CDHashSet<Node> d_rlvTermsWaiting;
  /** */
  context::CDO<bool> d_active;
  /** */
  EagerWatchList d_ewl;
};

using EagerFailExp = std::map<
    Node,
    std::map<Node,
             std::vector<std::pair<const EagerTrie*, std::vector<Node>>>>>;

class CDEagerTrie
{
 public:
  CDEagerTrie(context::Context* c);
  /** Add pattern */
  EagerTrie* addPattern(TermDb* tdb, const Node& pat);
  /** */
  EagerTrie* getCurrent(TermDb* tdb);

 private:
  void makeCurrent(TermDb* tdb);
  EagerTrie d_trie;
  /** The patterns for this operator in the current context */
  context::CDList<Node> d_pats;
  std::vector<Node> d_triePats;
};

class EagerPatternInfo
{
 public:
  EagerPatternInfo(context::Context* c, const Node& q)
      : d_quant(q), d_pmatches(c)
  {
  }
  void addMultiTriggerContext(const Node& pat, size_t i)
  {
    d_multiCtx.emplace_back(pat, i);
  }
  /** */
  const Node& getQuantFormula() const { return d_quant; }
  const std::vector<std::pair<Node, size_t>>& getMultiCtx() const
  {
    return d_multiCtx;
  }
  EagerGroundTrie* getPartialMatches() { return &d_pmatches; }

 private:
  Node d_quant;
  std::vector<std::pair<Node, size_t>> d_multiCtx;
  EagerGroundTrie d_pmatches;
};

/**
 */
class EagerInst : public QuantifiersModule
{
  using NodeSet = context::CDHashSet<Node>;
  using NodePairHashFunction =
      PairHashFunction<Node, Node, std::hash<Node>, std::hash<Node>>;
  using NodePairSet =
      context::CDHashSet<std::pair<Node, Node>, NodePairHashFunction>;
  using NodePairMap =
      context::CDHashMap<std::pair<Node, Node>, Node, NodePairHashFunction>;

  using NodeMap = context::CDHashMap<Node, Node>;

 public:
  EagerInst(Env& env,
            QuantifiersState& qs,
            QuantifiersInferenceManager& qim,
            QuantifiersRegistry& qr,
            TermRegistry& tr);
  ~EagerInst();
  /** Presolve */
  void presolve() override;
  /** Needs check. */
  bool needsCheck(Theory::Effort e) override;
  /** Reset round. */
  void reset_round(Theory::Effort e) override;
  /** Register quantified formula q */
  void registerQuantifier(Node q) override;
  /** Assert node. */
  void assertNode(Node q) override;
  /** Check ownership for q */
  void checkOwnership(Node q) override;
  /** Check.
   * Adds instantiations for all currently asserted
   * quantified formulas via calls to process(...)
   */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Identify. */
  std::string identify() const override;

  /** Notify asserted term */
  void notifyAssertedTerm(TNode n);

  /* For collecting global terms from all available assertions. */
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;

  void eqNotifyMerge(TNode t1, TNode t2);

 private:
  void registerQuant(const Node& q);
  eq::EqualityEngine* d_ee;
  TermDb* d_tdb;
  Node d_null;
  NodePairSet d_instTerms;
  NodeSet d_ownedQuants;
  NodePairMap d_patRegister;
  NodeSet d_filteringSingleTriggers;
  size_t d_tmpAddedLemmas;
  bool d_instOutput;
  CDEagerTrie d_etrie;
  NodeSet d_ppQuants;
  NodeSet d_fullInstTerms;
  NodeSet d_cdOps;
  context::CDHashMap<Node, std::shared_ptr<EagerWatchInfo>> d_repWatch;
  context::CDHashMap<Node, std::shared_ptr<EagerOpInfo>> d_opInfo;
  context::CDHashMap<Node, std::shared_ptr<EagerPatternInfo>> d_patInfo;

  EagerGroundDb d_gdb;
  /** Number of patterns */
  IntStat d_statUserPats;
  /** Number of cd patterns */
  IntStat d_statUserPatsCd;
  /** Number of single patterns */
  IntStat d_statSinglePat;
  /** Number of single patterns */
  IntStat d_statFilteringSinglePat;
  /** Number of single patterns */
  IntStat d_statMultiPat;
  /** Number of calls to match */
  IntStat d_statMatchCall;
  /** Number of calls to match */
  IntStat d_statMatchContinueCall;
  /** Number of calls to match */
  IntStat d_statWatchCount;
  /** Number of calls to match */
  IntStat d_statResumeMergeMatchCall;
  /** Number of calls to match */
  IntStat d_statResumeAssertMatchCall;
  /** Number of calls to match */
  IntStat d_statCdPatMatchCall;
  /** Static registers for instantiations */
  std::vector<Node> d_inst;
  /** */
  std::pair<Node, Node> d_nullPair;
  EagerWatchInfo* getOrMkWatchInfo(const Node& r, bool doMk);
  EagerOpInfo* getOrMkOpInfo(const Node& op, bool doMk);
  EagerPatternInfo* getOrMkPatternInfo(const Node& pat, bool doMk);
  /**
   * Match ground term iterated on by eti with the entire trie of patterns in
   * pat.
   */
  void doMatching(const EagerTrie* pat,
                  EagerTermIterator& eti,
                  EagerFailExp& failExp);
  void processInstantiation(const EagerTrie* pat,
                            EagerTermIterator& eti,
                            EagerFailExp& failExp);
  /**
   * Called when n matches pat, d_inst is populated with the match.
   */
  void processMultiTriggerInstantiation(EagerPatternInfo* epi,
                                        const Node& pat,
                                        size_t index,
                                        const Node& n,
                                        EagerFailExp& failExp);
  /**
   * Resume matching the ground term iterated on by eti with the entire trie of
   * patterns beneath tgt. We have so far traversed to the path pat guided by
   * the example pattern iterated on by etip.
   */
  void resumeMatching(const EagerTrie* pat,
                      EagerTermIterator& eti,
                      const EagerTrie* tgt,
                      EagerTermIterator& etip,
                      EagerFailExp& failExp);
  void doMatchingPath(const EagerTrie* et,
                      EagerTermIterator& eti,
                      EagerTermIterator& etip,
                      EagerFailExp& failExp);
  /**
   * Assumes d_inst is ready, instantiate with the patterns in et.
   */
  bool doInstantiation(const Node& pat,
                       const std::vector<Node>& n,
                       EagerFailExp& failExp);
  /** */
  bool isRelevantSuffix(const Node& pat, const std::vector<Node>& n);
  void addToFailExp(const EagerTrie* et,
                    const std::vector<Node>& ts,
                    EagerFailExp& failExp,
                    const Node& a,
                    const Node& b);
  void addWatches(EagerFailExp& failExp);
  bool isRelevantTerm(const Node& t);
  bool isRelevant(const Node& op, const std::vector<Node>& args);
  /** */
  Node getPatternFor(const Node& pat, const Node& q);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
