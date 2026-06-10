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
 * instantiation round, this module is incremental: each ground term is
 * considered for matching (at the top level) at most once per SAT context.
 * Matching of subterms is performed modulo the current state of the master
 * equality engine at the time the new term is processed.
 *
 * The current implementation handles single triggers whose pattern is an
 * APPLY_UF application and whose free variables span the variables of the
 * quantified formula. All other triggers (multi-triggers, relational
 * triggers, triggers with interpreted symbols) are left to the lazy
 * instantiation engine.
 *
 * Limitations (planned future work):
 * - Merges in the master equality engine do not (yet) trigger re-matching.
 *   A match that becomes possible only due to a merge of two existing
 *   equivalence classes is found later by the lazy engine at full effort.
 * - No generation/cost-based throttling of eager instances yet.
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
  /** Needs check at full effort if there are unprocessed terms. */
  bool needsCheck(Theory::Effort e) override;
  /** Check, processes the queue of new terms at QEFFORT_CONFLICT. */
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
   * Process all unprocessed terms in the queue, matching them against the
   * triggers of active quantified formulas and sending instantiation lemmas
   * via the inference manager. Lemmas are buffered in the inference manager;
   * the caller is responsible for flushing them (via doPending).
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
    EagerTrigger(const Node& q, const Node& pattern)
        : d_quant(q), d_pattern(pattern)
    {
    }
    /** The quantified formula */
    Node d_quant;
    /** The pattern, an APPLY_UF application whose free variables are the
     * bound variables of d_quant */
    Node d_pattern;
  };
  /**
   * Match the new term t against all triggers whose pattern has the same
   * operator, for active quantified formulas. Sends instantiations.
   */
  void processTerm(TNode t);
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
  std::map<Node, std::vector<EagerTrigger>> d_opTriggers;
  /** The set of quantified formulas currently asserted (SAT context). */
  NodeSet d_activeQuants;
  /** The queue of new terms from the master equality engine (SAT context). */
  context::CDList<Node> d_newTerms;
  /**
   * The signatures (operator and argument representatives) of terms we have
   * already matched against (SAT context). Terms that are congruent to an
   * already processed term produce the same matches modulo equality, and
   * hence are skipped. This is important since most new terms are introduced
   * by instantiation lemmas, which heavily overlap with existing terms.
   */
  NodeSet d_procSigs;
  /** The index of the next unprocessed term in d_newTerms (SAT context). */
  context::CDO<size_t> d_procIdx;
  /** Total time spent in processNewTerms */
  TimerStat d_procTime;
  /** Time spent sending instantiations (subsumed by the above) */
  TimerStat d_addInstTime;
  /** Number of terms processed */
  IntStat d_statTerms;
  /** Number of matches found */
  IntStat d_statMatches;
  /** Number of instantiations successfully added */
  IntStat d_statInst;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__EAGER_INST_H */
