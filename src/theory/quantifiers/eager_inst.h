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
 * This module performs E-matching eagerly: it watches new term notifications
 * from the master equality engine and matches them against (user-provided)
 * triggers as soon as possible, that is, at standard effort checks, instead
 * of waiting for a full effort instantiation round. It is intended to run
 * concurrently with the (lazy) InstantiationEngine, which remains the
 * backstop for completeness.
 *
 * In contrast to the lazy E-matching infrastructure (TermDb,
 * InstMatchGenerator, etc.), which re-enumerates candidate terms per
 * instantiation round, this module is incremental: each pair of a ground
 * term and a trigger is considered (at the top level) at most once per
 * SAT context. This is implemented by maintaining, per operator, the
 * (context-dependent) list of ground terms with that operator, and, per
 * trigger, a (context-dependent) cursor into that list. The cursor of a
 * trigger only advances while its quantified formula is asserted, so that
 * a quantified formula that becomes asserted late in the SAT context still
 * matches against all existing terms. Matching of subterms is performed
 * modulo the master equality engine at the time the pair is processed.
 *
 * The current implementation handles single triggers whose pattern is an
 * APPLY_UF application and whose free variables span the variables of the
 * quantified formula. All other triggers (multi-triggers, relational
 * triggers, triggers with interpreted symbols) are left to the lazy
 * instantiation engine.
 *
 * Limitations (planned future work):
 * - Merges in the master equality engine do not (yet) trigger re-matching
 *   of already processed (term, trigger) pairs. A match that becomes
 *   possible only due to a merge of two existing equivalence classes is
 *   found later by the lazy engine at full effort.
 * - No generation/cost-based throttling of eager instances yet.
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
    EagerTrigger(context::Context* c, const Node& q, const Node& pattern)
        : d_quant(q), d_pattern(pattern), d_procIdx(c, 0)
    {
    }
    /** The quantified formula */
    Node d_quant;
    /** The pattern, an APPLY_UF application whose free variables are the
     * bound variables of d_quant */
    Node d_pattern;
    /**
     * The index of the next unprocessed term in the term list of the
     * operator of d_pattern (SAT context). This only advances while
     * d_quant is asserted.
     */
    context::CDO<size_t> d_procIdx;
  };
  /**
   * Match the term t against trigger tr, whose pattern has the same
   * operator as t, and send the resulting instantiations. Performs a
   * cheap top-level filter (ground pattern arguments must be equal to the
   * corresponding arguments of t) before running full matching.
   */
  void processTermForTrigger(TNode t, const EagerTrigger& tr);
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
   *
   * Note that within a SAT context, merges only coarsen the congruence
   * relation, so terms that are congruent at promotion time remain
   * congruent; backtracking pops all structures consistently.
   */
  class OpTermList
  {
   public:
    OpTermList(context::Context* c)
        : d_list(c), d_unique(c), d_sigs(c), d_rawIdx(c, 0)
    {
    }
    /** The raw list of terms with this operator */
    context::CDList<Node> d_list;
    /** The congruence-deduplicated list of terms */
    context::CDList<Node> d_unique;
    /** The signatures of the terms in d_unique */
    NodeSet d_sigs;
    /** The index of the next raw term to consider for promotion */
    context::CDO<size_t> d_rawIdx;
  };
  /** Get (or create) the term lists for operator op. */
  OpTermList& getOpTermList(const Node& op);
  /**
   * Promote all unpromoted raw terms of ol to its unique list, if their
   * signature is new.
   */
  void promoteTerms(OpTermList& ol);
  /**
   * Map from operators to the (SAT-context dependent) lists of ground terms
   * with that operator that have been added to the master equality engine.
   */
  std::map<Node, std::unique_ptr<OpTermList>> d_opTerms;
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
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER_INST_H */
