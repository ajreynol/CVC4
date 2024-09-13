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
#include "theory/quantifiers/eager/eager_trie.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class EagerWatchList
{
 public:
  EagerWatchList(context::Context* c) : d_valid(c, true), d_matchJobs(c) {}
  void add(const EagerTrie* et, const Node& t);
  context::CDO<bool> d_valid;
  context::CDList<std::pair<const EagerTrie*, Node>> d_matchJobs;
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
  EagerOpInfo(context::Context* c) : d_pats(c) {}
  /** Get trie, possibly with cleaning */
  EagerTrie* getCurrentTrie(TermDb* tdb);
  /** Add pattern */
  void addPattern(TermDb* tdb, const Node& pat);

  // without trie
  context::CDList<Node>& getPatterns() { return d_pats; }
  void addPatternSimple(const Node& pat) { d_pats.push_back(pat); }

 private:
  /** The patterns for this operator in the current context */
  context::CDList<Node> d_pats;
  EagerTrie d_trie;
  std::vector<Node> d_triePats;
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
  NodePairSet d_instTerms;
  NodeSet d_ownedQuants;
  size_t d_tmpAddedLemmas;
  bool d_instOutput;
  NodeSet d_ppQuants;
  NodeSet d_rlvTerms;
  std::map<Node, size_t> d_termNotifyCount;
  NodeSet d_fullInstTerms;
  NodeSet d_cdOps;
  context::CDHashMap<Node, std::shared_ptr<EagerWatchInfo>> d_repWatch;
  context::CDHashMap<Node, std::shared_ptr<EagerOpInfo>> d_userPat;
  /** Number of patterns */
  IntStat d_statUserPats;
  /** Number of cd patterns */
  IntStat d_statUserPatsCd;
  /** Multi filter */
  IntStat d_statUserPatsMultiFilter;
  /** Number of calls to match */
  IntStat d_statMatchCall;
  /** */
  std::pair<Node, Node> d_nullPair;
  EagerWatchInfo* getOrMkWatchInfo(const Node& r, bool doMk);
  EagerOpInfo* getOrMkOpInfo(const Node& op, bool doMk);
  void doMatchingTrieInternal(
      const EagerTrie* pat,
      const Node& n,
      const Node& t,
      size_t i,
      std::vector<Node>& inst,
      std::vector<std::pair<Node, size_t>>& ets,
      std::map<const EagerTrie*, std::pair<Node, Node>>& failExp);
  void addToFailExp(const EagerTrie* et,
                    std::map<const EagerTrie*, std::pair<Node, Node>>& failExp,
                    const Node& a,
                    const Node& b);
  void addWatches(const Node& t,
                  std::map<const EagerTrie*, std::pair<Node, Node>>& failExp);
  /**
   * Node n matching pat is waiting on a being equal to b.
   */
  void addWatch(const EagerTrie* pat,
                const Node& t,
                const Node& a,
                const Node& b);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
