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
#include "theory/quantifiers/eager/eager_utils.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

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
  /** Preregister quantified formula q */
  void preRegisterQuantifier(Node q) override;
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
  void registerQuantInternal(const Node& q);
  eq::EqualityEngine* d_ee;
  TermDb* d_tdb;
  Node d_null;
  NodePairSet d_instTerms;
  NodeSet d_ownedQuants;
  NodePairMap d_patRegister;
  NodeSet d_filteringSingleTriggers;
  size_t d_tmpAddedLemmas;
  bool d_instOutput;
  NodeSet d_ppQuants;
  NodeSet d_fullInstTerms;
  NodeSet d_cdOps;
  context::CDHashMap<Node, std::shared_ptr<EagerRepInfo>> d_repWatch;
  context::CDHashMap<Node, std::shared_ptr<EagerOpInfo>> d_opInfo;
  context::CDHashMap<Node, std::shared_ptr<EagerPatternInfo>> d_patInfo;
  std::map<Node, EagerMultiPatternInfo> d_multiPatInfo;
  /** */
  bool d_quantOnAssert;
  bool d_quantOnPreregister;

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
  IntStat d_statWatchCount;
  /** Number of calls to match */
  IntStat d_statWatchMtCount;
  /** Number of calls to match */
  IntStat d_statMatchCall;
  /** Number of calls to match */
  IntStat d_statResumeMergeMatchCall;
  /** Number of calls to match */
  IntStat d_statCdPatMatchCall;
  /** Number of calls to match */
  IntStat d_statMtJoinCount;
  /** Static registers for instantiations */
  std::vector<TNode> d_inst;
  /** */
  std::pair<Node, Node> d_nullPair;
  EagerRepInfo* getOrMkRepInfo(const Node& r, bool doMk);
  EagerOpInfo* getOrMkOpInfo(const Node& op, bool doMk);
  EagerPatternInfo* getOrMkPatternInfo(const Node& pat, bool doMk);
  EagerTrie* getCurrentTrie(const Node& op);
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
   * Called when n matches pat, d_inst is populated with the partial match.
   *
   * We first see if the partial match is already equal modulo equality to
   * another partial match. If so, we return.
   * Otherwise, if this is the first time seeing n, we add the partial match
   * and proceed to joining with the remaining matches
   */
  void processMultiTriggerInstantiation(const Node& pat,
                                        size_t index,
                                        const Node& n,
                                        EagerWatchSet& failWatch);
  void processMultiTriggerInstantiations(
      const Node& q,
      const Node& pat,
      size_t varIndex,
      size_t basePatIndex,
      std::vector<std::vector<EagerGroundTrie*>>& pats,
      EagerWatchSet& failWatch);

  /**
   * Resume matching the ground term iterated on by eti with the entire trie of
   * patterns beneath tgt. We have so far traversed to the path pat guided by
   * the example pattern iterated on by etip.
   */
  void resumeMatching(const EagerTrie* pat,
                      EagerTermIterator& eti,
                      const EagerTrie* tgt,
                      EagerTermIterator& etip,
                      std::unordered_set<size_t>& bindices);
  void doMatchingPath(const EagerTrie* et,
                      EagerTermIterator& eti,
                      EagerTermIterator& etip,
                      EagerFailExp& failExp);
  /**
   * Assumes d_inst is ready, instantiate with the patterns in et.
   * TODO: remove this variant
   */
  bool doInstantiation(const Node& pat, TNode n, EagerFailExp& failExp);
  /**
   * Assumes d_inst is ready, instantiate q with d_inst.
   * The pattern and term matched (pat and n) are checked and
   * cached if n is non-null (which is the case iff pat is a single trigger).
   * If the instantiation fails, adds to failExp.
   */
  bool doInstantiation(const Node& q, const Node& pat, const Node& n);
  void addEqToWatch(const EagerTrie* et,
                    TNode t,
                    EagerFailExp& failExp,
                    const Node& a,
                    const Node& b);
  void addOpToWatch(const EagerTrie* et,
                    TNode t,
                    EagerFailExp& failExp,
                    const Node& a,
                    const Node& op);
  void addToWatchSet(EagerWatchSet& ews, TNode a, TNode b);
  void addWatches(EagerFailExp& failExp);
  /** */
  Node getPatternFor(const Node& pat, const Node& q);

  /** */
  void resumeWatchList(
      EagerWatchList* ewl,
      std::map<const EagerTrie*, std::unordered_set<TNode>>& processed,
      EagerFailExp& nextFails);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
