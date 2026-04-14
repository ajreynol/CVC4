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

#include <map>
#include <vector>

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class InstMatch;

/**
 * Eager instantiation.
 *
 * This module maintains a small incremental term database that is populated
 * only from notification events. It uses the resulting indexed terms to drive
 * a lightweight eager matcher for user-provided patterns.
 */
class EagerInst : public QuantifiersModule
{
  /** A small incremental term database for eager instantiation. */
  struct EagerTermDatabase
  {
    /** Clear the database. */
    void clear();
    /**
     * Add term t to the database.
     * Returns true if t was newly added.
     */
    bool addTerm(Node t, Node op);
    /** Return the ground terms for operator op, if any. */
    const std::vector<Node>* getGroundTerms(Node op) const;
    /** Return the number of ground terms for operator op. */
    size_t getNumGroundTerms(Node op) const;
    /** Terms we have already indexed from notifications. */
    std::map<Node, bool> d_terms;
    /** Indexed ground terms by match operator. */
    std::map<Node, std::vector<Node>> d_opTerms;
  };

  /** A simple atomic pattern term we may eventually match eagerly. */
  struct PatternInfo
  {
    /** The pattern in instantiation-constant form. */
    Node d_pattern;
    /** The match operator of the pattern. */
    Node d_op;
    /** Instantiation constants occurring in the pattern. */
    std::vector<Node> d_vars;
    /** Nested match operators whose equivalence classes can affect matching. */
    std::vector<Node> d_mergeOps;
    /** Ground subterms whose equivalence classes can affect matching. */
    std::vector<Node> d_groundTerms;
    /** Whether the pattern repeats one of its instantiation constants. */
    bool d_hasRepeatedVar = false;
  };

  /** A multi-pattern / trigger candidate comprising one or more pattern terms.
   */
  struct TriggerInfo
  {
    /** The pattern terms comprising the trigger. */
    std::vector<PatternInfo> d_patterns;
    /** The proof argument describing this trigger. */
    Node d_pfArg;
    /** A stable identifier for this trigger. */
    uint64_t d_id = 0;
    /** The operators watched for this trigger. */
    std::vector<Node> d_watchedOps;
    /** All instantiation constants covered by the trigger. */
    std::vector<Node> d_vars;
    /** Nested match operators watched for equality merges. */
    std::vector<Node> d_mergeOps;
    /** Ground subterms watched for equality merges. */
    std::vector<Node> d_groundTerms;
    /** Whether any equality merge can affect this trigger. */
    bool d_needsAnyMerge = false;
  };

  /** Quantifier-local eager-inst metadata. */
  struct QuantInfo
  {
    /** Trigger candidates extracted from its user patterns. */
    std::vector<TriggerInfo> d_triggers;
    /** Operators watched by any trigger candidate. */
    std::vector<Node> d_watchedOps;
    bool empty() const { return d_triggers.empty(); }
  };

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

  /** Whether this module wants to be notified about new equality classes. */
  bool needsNotifyNewClass() const;
  /**
   * Whether this module wants recursive asserted-term notifications on merges.
   * This is intended for future, more aggressive eager processing.
   */
  bool needsNotifyMergeTerms() const;
  /** Whether this module wants recursive asserted-term notifications on facts.
   */
  bool needsNotifyAssertedTerms() const;
  /** Whether this module wants direct equality-merge notifications. */
  bool needsNotifyMerges() const;

  /** Notify asserted term */
  void notifyAssertedTerm(TNode n);

  /* For collecting global terms from all available assertions. */
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;

  void eqNotifyMerge(TNode t1, TNode t2);

 private:
  /** Register simple watch information for quantified formula q. */
  void registerWatchInfo(Node q);
  /** Register a trigger candidate for q, returns true if accepted. */
  bool registerTriggerInfo(Node q, const std::vector<Node>& pats);
  /** Get simple pattern info for pat, returns false if unsupported. */
  bool getPatternInfo(Node q, Node pat, PatternInfo& pinfo) const;
  /** Index terms reachable from notification term t. */
  void indexTerms(TNode t);
  /** Index repeated-variable merge dependencies for ground term t. */
  void indexParentOperators(TNode t);
  /** Add instantiations for trigger ti of quantified formula q. */
  void addInstantiations(Node q, const TriggerInfo& ti, uint64_t& addedLemmas);
  /** Recursive helper for addInstantiations. */
  void addInstantiations(Node q,
                         const TriggerInfo& ti,
                         size_t pindex,
                         InstMatch& m,
                         std::vector<size_t>& assigned,
                         uint64_t& addedLemmas);
  /** Match pattern pat against term t. */
  bool matchPattern(Node q,
                    TNode pat,
                    TNode t,
                    InstMatch& m,
                    std::vector<size_t>& assigned) const;
  /** Add purification lemmas for ground trigger subterms if necessary. */
  void addGroundTermLemmas(const TriggerInfo& ti, uint64_t& addedLemmas);
  /** Add n to nodes if it is not already present. */
  static void pushBackUnique(std::vector<Node>& nodes, Node n);
  /** Whether trigger tr has ground terms for each watched operator. */
  bool isTriggerActive(uint64_t tr) const;
  /** Mark active triggers watching op as dirty. */
  void markOperatorDirty(Node op);
  /** Mark trigger tr as dirty. */
  void markTriggerDirty(uint64_t tr);
  /** Whether we currently have pending work. */
  bool hasPendingWork() const;
  /** Clear pending dirty state after a check. */
  void clearPending();
  /** Add trigger to triggers if it is not already present. */
  static void pushBackUniqueTrigger(std::vector<uint64_t>& triggers,
                                    uint64_t tr);

  /** Watch information for quantifiers. */
  std::map<Node, QuantInfo> d_qinfo;
  /** Incremental term database for eager instantiation. */
  EagerTermDatabase d_termDb;
  /** Reverse watch list from operator to quantifiers. */
  std::map<Node, std::vector<Node>> d_opWatchList;
  /** Reverse watch list from operator to triggers. */
  std::map<Node, std::vector<uint64_t>> d_opTriggerWatchList;
  /** Reverse watch list from merge-relevant operator to triggers. */
  std::map<Node, std::vector<uint64_t>> d_mergeOpWatchList;
  /** Reverse watch list from merge-relevant ground term to triggers. */
  std::map<Node, std::vector<uint64_t>> d_mergeGroundWatchList;
  /** Reverse watch list from parent operator to repeated-variable triggers. */
  std::map<Node, std::vector<uint64_t>> d_mergeParentOpWatchList;
  /** Trigger owner map. */
  std::map<uint64_t, Node> d_triggerOwner;
  /** Root operators watched by each trigger. */
  std::map<uint64_t, std::vector<Node>> d_triggerOps;
  /** Reverse index from a term to parent operators that contain it. */
  std::map<Node, std::vector<Node>> d_parentOpIndex;
  /** Dirty operators since the last eager-inst check. */
  std::map<Node, bool> d_dirtyOps;
  /** Dirty quantifiers since the last eager-inst check. */
  std::map<Node, bool> d_dirtyQuants;
  /** Quantifiers with at least one dirty trigger since the last check. */
  std::map<Node, bool> d_dirtyTriggerQuants;
  /** Dirty triggers since the last eager-inst check. */
  std::map<uint64_t, bool> d_dirtyTriggers;
  /** Whether some relevant equality merge happened since the last check. */
  bool d_hasPendingMerge;
  /** The next eager trigger identifier. */
  uint64_t d_nextTriggerId;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
