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
#include <memory>
#include <vector>

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

namespace inst {
class Trigger;
class TriggerDatabase;
}  // namespace inst

/**
 * Eager instantiation scaffolding.
 *
 * The long-term goal for this module is to support an incremental, E-graph
 * driven instantiation flow in the spirit of de Moura/Bjorner's
 * "Efficient E-matching for SMT solvers". The current implementation is a
 * setup pass: it records simple user-pattern metadata, establishes watch lists
 * by operator, and maintains dirty bookkeeping from equality-engine events.
 *
 * In particular, this gives us:
 * - a stable place to store quantifier-local pattern information,
 * - explicit notification requirements for QuantifiersEngine, and
 * - a minimal event queue that later matching code can consume.
 */
class EagerInst : public QuantifiersModule
{
  /** A simple atomic pattern term we may eventually match eagerly. */
  struct PatternInfo
  {
    /** The pattern in instantiation-constant form. */
    Node d_pattern;
    /** The match operator of the pattern. */
    Node d_op;
    /** Instantiation constants occurring in the pattern. */
    std::vector<Node> d_vars;
    /** Whether the pattern repeats one of its instantiation constants. */
    bool d_hasRepeatedVar = false;
  };

  /** A multi-pattern / trigger candidate comprising one or more pattern terms. */
  struct TriggerInfo
  {
    /** The pattern terms comprising the trigger. */
    std::vector<PatternInfo> d_patterns;
    /** The backend trigger used for matching. */
    inst::Trigger* d_trigger = nullptr;
    /** The operators watched for this trigger. */
    std::vector<Node> d_watchedOps;
    /** All instantiation constants covered by the trigger. */
    std::vector<Node> d_vars;
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
  /** Whether this module wants recursive asserted-term notifications on facts. */
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
  /** Add n to nodes if it is not already present. */
  static void pushBackUnique(std::vector<Node>& nodes, Node n);
  /** Mark all quantifiers watching op as dirty. */
  void markOperatorDirty(Node op);
  /** Mark q as dirty. */
  void markQuantifierDirty(Node q);
  /** Whether we currently have pending work. */
  bool hasPendingWork() const;
  /** Clear pending dirty state after a check. */
  void clearPending();

  /** Watch information for quantifiers. */
  std::map<Node, QuantInfo> d_qinfo;
  /** Trigger database owning the backend trigger objects. */
  std::unique_ptr<inst::TriggerDatabase> d_trdb;
  /** Reverse watch list from operator to quantifiers. */
  std::map<Node, std::vector<Node>> d_opWatchList;
  /** Dirty operators since the last eager-inst check. */
  std::map<Node, bool> d_dirtyOps;
  /** Dirty quantifiers since the last eager-inst check. */
  std::map<Node, bool> d_dirtyQuants;
  /** Whether some relevant equality merge happened since the last check. */
  bool d_hasPendingMerge;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
