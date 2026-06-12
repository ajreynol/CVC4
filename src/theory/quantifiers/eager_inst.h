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

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER_INST_H
#define CVC5__THEORY__QUANTIFIERS__EAGER_INST_H

#include <map>
#include <memory>
#include <unordered_set>
#include <vector>

#include "context/cdhashset.h"
#include "context/cdlist.h"
#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/quant_module.h"
#include "util/statistics_stats.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

/**
 * EagerInstantiation
 *
 * This module performs E-matching eagerly: it watches new term and merge
 * notifications from the master equality engine and matches them against
 * (user-provided) triggers as soon as possible, that is, at standard effort
 * checks, instead of waiting for a full effort instantiation round. It is
 * intended to run concurrently with the (lazy) InstantiationEngine, which
 * remains the backstop for completeness.
 *
 * In contrast to the lazy E-matching infrastructure (TermDb,
 * InstMatchGenerator, etc.), which re-enumerates candidate terms per
 * instantiation round, this module is incremental: each pair of a ground
 * term and a trigger is considered (at the top level) at most once per
 * SAT context, unless a merge makes new matches possible for the term
 * (see "merge-driven re-matching" below). This is implemented by
 * maintaining, per operator, the (context-dependent) list of ground terms
 * with that operator, and, per trigger, a (context-dependent) cursor into
 * that list. The cursor of a trigger only advances while its quantified
 * formula is asserted, so that a quantified formula that becomes asserted
 * late in the SAT context still matches against all existing terms.
 * Matching of subterms is performed modulo the master equality engine at
 * the time the pair is processed.
 *
 * Merge-driven re-matching: when two equivalence classes merge, matches
 * that were not possible before may become possible, but only for terms
 * that have a direct subterm in the merged class (matching of deeper
 * subterms is modulo the equality engine and hence considers the merged
 * classes when their parent is re-matched). We maintain a (syntactic)
 * parent index, and re-append the parents of all members of a merged
 * class to the respective term lists, so that all triggers re-match them.
 *
 * The current implementation handles single triggers whose pattern is an
 * APPLY_UF application and whose free variables span the variables of the
 * quantified formula. All other triggers (multi-triggers, relational
 * triggers, triggers with interpreted symbols) are left to the lazy
 * instantiation engine.
 *
 * Trace tags:
 * - eager-inst: trigger registration, activation, added instantiations
 * - eager-inst-reject: quantified formulas/patterns this module does not
 *   handle (left to the lazy engine)
 * - eager-inst-status: one line summary per processing round
 * - eager-inst-debug: per (term, trigger) pair processing, found matches
 * - eager-inst-debug2: fine-grained matching details (congruence skips)
 */
class EagerInstantiation : public QuantifiersModule
{
  using NodeSet = context::CDHashSet<Node, std::hash<Node>>;

 public:
  EagerInstantiation(Env& env,
                     QuantifiersState& qs,
                     QuantifiersInferenceManager& qim,
                     QuantifiersRegistry& qr,
                     TermRegistry& tr);
  ~EagerInstantiation();
  /** Needs check at full effort if there are unprocessed pairs. */
  bool needsCheck(Theory::Effort e) override;
  /** Check, processes unprocessed (term, trigger) pairs. */
  void check(Theory::Effort e, QEffort quant_e) override;
  /** Register quantifier, compiles eager triggers for q. */
  void registerQuantifier(Node q) override;
  /** Called when q is asserted, activates the triggers of q. */
  void assertNode(Node q) override;
  /** Identify. */
  std::string identify() const override { return "EagerInstantiation"; }
  /**
   * Set the (lazy) instantiation engine. Quantified formulas owned by the
   * lazy instantiation engine (e.g. those with user patterns when
   * --user-pat=strict) are also handled by this module, since eager and
   * lazy E-matching are complementary strategies over the same triggers.
   */
  void setLazyInstantiationEngine(QuantifiersModule* m) { d_instEngine = m; }
  /**
   * Notification from the master equality engine that term t was added.
   * This method only enqueues t; matching is performed in the next call to
   * processNewTerms, which is called during theory checks. It is safe to
   * call this method while the equality engine is mid-operation.
   */
  void eqNotifyNewClass(TNode t);
  /**
   * Notification from the master equality engine that the classes of t1
   * and t2 were merged. This method only enqueues the pair; re-matching is
   * performed in the next call to processNewTerms. It is safe to call this
   * method while the equality engine is mid-operation.
   */
  void eqNotifyMerge(TNode t1, TNode t2);
  /**
   * Process all unprocessed (term, trigger) pairs, matching terms against
   * the triggers of asserted quantified formulas and sending instantiation
   * lemmas via the inference manager. Lemmas are buffered in the inference
   * manager; the caller is responsible for flushing them (via doPending).
   *
   * This is the main entry point of this module. It is called directly
   * from the quantifiers engine at standard effort (bypassing the full
   * quantifiers check, which resets utilities such as TermDb), and from
   * check(...) at full effort.
   */
  void processNewTerms();

 private:
  /** An eager trigger, a single pattern for a quantified formula. */
  struct EagerTrigger
  {
    EagerTrigger(context::Context* c, const Node& q, const Node& pattern);
    /** The quantified formula */
    Node d_quant;
    /** The pattern, an APPLY_UF application whose free variables are the
     * bound variables of d_quant */
    Node d_pattern;
    /**
     * The index of the next unprocessed term in the unique term list of
     * the operator of d_pattern (SAT context). This only advances while
     * d_quant is asserted.
     */
    context::CDO<size_t> d_procIdx;
    /** The argument positions of d_pattern that are ground */
    std::vector<size_t> d_groundPos;
    //----- per-round cache, valid when d_roundStamp matches the current round
    /** The round this cache was computed at */
    uint64_t d_roundStamp;
    /** Whether all ground arguments of the pattern occur in the equality
     * engine this round; if not, the pattern cannot match */
    bool d_roundActive;
    /** The representatives of the ground arguments, aligned with
     * d_groundPos */
    std::vector<Node> d_groundReps;
  };
  /**
   * The (context-dependent) lists of ground terms for one operator.
   *
   * Terms arrive in d_list (the raw list) via eqNotifyNewClass. During
   * processing, raw terms are promoted (once, tracked by d_rawIdx) to
   * d_unique if no term with the same signature (the representatives of
   * its arguments) has been promoted already, as recorded in d_sigs.
   * Triggers match against d_unique only, since terms that are congruent
   * to an already promoted term produce the same matches modulo equality.
   * This is important since (1) most new terms are introduced by
   * instantiation lemmas, which heavily overlap with existing terms, and
   * (2) each unique term is matched by all triggers with this operator,
   * hence deduplication must happen before the per-trigger loop.
   * The signature of each promoted term is stored in d_uniqueSigs (aligned
   * with d_unique), which enables cheap filtering against the ground
   * arguments of patterns.
   *
   * Terms may additionally be re-appended to d_unique by merge-driven
   * re-matching (with their new signature), in which case they are
   * processed again by all triggers.
   *
   * Note that within a SAT context, merges only coarsen the congruence
   * relation, so terms that are congruent at promotion time remain
   * congruent; backtracking pops all structures consistently.
   */
  class OpTermList
  {
   public:
    OpTermList(context::Context* c)
        : d_list(c), d_unique(c), d_uniqueSigs(c), d_sigs(c), d_rawIdx(c, 0)
    {
    }
    /** The raw list of terms with this operator */
    context::CDList<Node> d_list;
    /** The congruence-deduplicated list of terms */
    context::CDList<Node> d_unique;
    /** The signatures of the terms in d_unique, aligned with d_unique */
    context::CDList<Node> d_uniqueSigs;
    /** The set of signatures of the terms promoted to d_unique */
    NodeSet d_sigs;
    /** The index of the next raw term to consider for promotion */
    context::CDO<size_t> d_rawIdx;
  };
  /** Get (or create) the term lists for operator op. */
  OpTermList& getOpTermList(const Node& op);
  /**
   * Return the signature of term t, the tuple of representatives of its
   * arguments (the operator is implied by the list the term occurs in).
   */
  Node computeSig(TNode t);
  /**
   * Promote all unpromoted raw terms of ol to its unique list, if their
   * signature is new.
   */
  void promoteTerms(OpTermList& ol);
  /**
   * Process all unprocessed merges: for each merged class, re-append the
   * (syntactic) parents of its members to the unique term lists of their
   * operators, so that all triggers re-match them.
   */
  void processMerges();
  /**
   * Refresh the per-round cache of tr (the representatives of the ground
   * arguments of its pattern), if it is not valid for the current round.
   */
  void refreshTriggerCache(EagerTrigger& tr);
  /**
   * Match the term t against trigger tr, whose pattern has the same
   * operator as t, and send the resulting instantiations. The term sig,
   * if non-null, is the signature of t, which is used for cheap filtering:
   * the ground arguments of the pattern must have the same representative
   * as the corresponding argument of t.
   */
  void processTermForTrigger(TNode t, TNode sig, const EagerTrigger& tr);
  /**
   * Continue matching the list of (pattern, ground term) constraints in
   * todo starting at index i, where binding is the current (partial) map
   * from bound variables to ground terms. Complete bindings are appended
   * to matches. Matching is performed modulo the master equality engine.
   */
  void matchRec(size_t i,
                std::vector<std::pair<TNode, TNode>>& todo,
                std::map<Node, Node>& binding,
                std::vector<std::map<Node, Node>>& matches);
  /** Pointer to the lazy instantiation engine, if it exists. */
  QuantifiersModule* d_instEngine = nullptr;
  /** Map from operators to the triggers whose pattern head is that
   * operator. This is context-independent; triggers are activated by
   * d_activeQuants. */
  std::map<Node, std::vector<std::unique_ptr<EagerTrigger>>> d_opTriggers;
  /** The set of quantified formulas currently asserted (SAT context). */
  NodeSet d_activeQuants;
  /**
   * Map from operators to the (SAT-context dependent) lists of ground terms
   * with that operator that have been added to the master equality engine.
   */
  std::map<Node, std::unique_ptr<OpTermList>> d_opTerms;
  /**
   * The (syntactic) parent index: maps each term to the APPLY_UF terms
   * that have it as a direct argument. This is context-independent; stale
   * entries (whose parent is not in the equality engine) are filtered at
   * use. Used for merge-driven re-matching.
   */
  std::map<Node, std::vector<Node>> d_parents;
  /** The terms whose parents have been registered in d_parents. */
  std::unordered_set<Node> d_parentsRegistered;
  /**
   * The generation of terms, used for admission control (option
   * --eager-inst-gen-limit). Terms of the input have generation 0 (they are
   * absent from this map); the APPLY_UF subterms of the body of an
   * instantiation that this module sends get generation
   * (1 + the maximum generation of the instantiating terms), unless they
   * already have a (smaller) generation. Terms whose generation meets the
   * limit are not matched eagerly; instantiations depending on them are
   * found by the lazy instantiation engine at full effort. This bounds the
   * depth of eager instantiation chains (instances whose terms trigger
   * further instances), which can otherwise flood the search with
   * irrelevant instances.
   *
   * This map is context-independent: a term keeps its generation across
   * backtracking, which is a sound over-approximation (the lemma that
   * introduced it persists as well).
   */
  std::unordered_map<Node, uint64_t> d_termGen;
  /**
   * Fingerprints of the instantiations this module has sent (SAT context).
   * A fingerprint is the quantified formula together with the tuple of
   * representatives of the instantiating terms. Matches whose fingerprint
   * is present are duplicates modulo equality of an instantiation we have
   * already sent (whose lemma persists), and are skipped without
   * consulting the instantiation utility. This is important since the
   * same instantiation is typically re-derived many times from different
   * (congruent) terms across rounds.
   */
  NodeSet d_sentFps;
  /** The queue of unprocessed merges (SAT context). */
  context::CDList<std::pair<Node, Node>> d_mergeQueue;
  /** The index of the next unprocessed merge in d_mergeQueue. */
  context::CDO<size_t> d_mergeIdx;
  /** The current processing round, for the per-round trigger caches. */
  uint64_t d_round;
  /** Total time spent in processNewTerms */
  TimerStat d_procTime;
  /** Time spent sending instantiations (subsumed by the above) */
  TimerStat d_addInstTime;
  /** Number of (term, trigger) pairs processed */
  IntStat d_statPairs;
  /** Number of matches found */
  IntStat d_statMatches;
  /** Number of instantiations successfully added */
  IntStat d_statInst;
  /** Number of terms re-appended due to merges */
  IntStat d_statRematch;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER_INST_H */
