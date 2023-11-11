/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Eager term database
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_EAGER_H
#define CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_EAGER_H

#include <vector>

#include "context/cdhashset.h"
#include "expr/node.h"
#include "expr/term_canonize.h"
#include "smt/env_obj.h"
#include "theory/inference_id.h"
#include "theory/quantifiers/eager/fun_info.h"
#include "theory/quantifiers/eager/quant_info.h"
#include "theory/quantifiers/eager/stats.h"
#include "theory/quantifiers/eager/trigger_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersInferenceManager;
class QuantifiersState;
class TermDb;

/**
 */
class TermDbEager : protected EnvObj
{
 public:
  TermDbEager(Env& env,
              QuantifiersState& qs,
              QuantifiersRegistry& qr,
              TermDb& tdb);
  /** Finish init, which sets the inference manager */
  void finishInit(QuantifiersInferenceManager* qim);
  /** notification that a quantified formula was asserted */
  void assertQuantifier(TNode q);
  /** notification when master equality engine is updated */
  void eqNotifyNewClass(TNode t);
  /** notification when master equality engine is updated */
  void eqNotifyMerge(TNode t1, TNode t2);
  /** Is in relevant domain? */
  bool inRelevantDomain(TNode f, size_t i, TNode r);
  /** Get congruent term */
  TNode getCongruentTerm(TNode f, const std::vector<TNode>& args);
  /** Is term congruent */
  bool isCongruent(TNode t) const;
  /** Get trigger info */
  eager::TriggerInfo* getTriggerInfo(const Node& t);
  /** Get quant info */
  eager::QuantInfo* getQuantInfo(TNode q);
  /** Get fun info */
  eager::FunInfo* getFunInfo(TNode f);

  /** Add instantiation */
  bool addInstantiation(const Node& q,
                        std::vector<Node>& terms,
                        bool isConflict);
  /**
   * Is the given quantified formula inactive?
   * This is the case if we successfully inferred triggers for q and those
   * triggers are not active.
   */
  bool isInactive(const Node& q);
  bool isAsserted(TNode n);
  //==========
  Env& getEnv() { return d_env; }
  TermDb& getTermDb() { return d_tdb; }
  eager::Stats& getStats() { return d_stats; }
  QuantifiersState& getState() { return d_qs; }
  CDTNodeTrieAllocator* getCdtAlloc() { return &d_cdalloc; }
  context::Context* getSatContext() { return context(); }
  bool isStatsEnabled() const { return d_statsEnabled; }

 private:
  bool notifyTerm(TNode n, bool notifyTriggers);
  eager::FunInfo* getOrMkFunInfo(TNode f, size_t nchild);
  bool isPropagatingInstance(Node n);
  Node isPropagatingTerm(Node n);
  void refresh();
  /** The null node */
  Node d_null;
  /** Reference to the quantifiers state */
  QuantifiersState& d_qs;
  /** The quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Pointer to the quantifiers inference manager */
  QuantifiersInferenceManager* d_qim;
  /** Reference to term database */
  TermDb& d_tdb;
  /** The CDTrieNode allocator */
  CDTNodeTrieAllocator d_cdalloc;
  /** The terms we have notified if d_whenAsserted is true */
  context::CDHashSet<Node> d_notified;
  /** */
  std::map<TNode, eager::TriggerInfo> d_tinfo;
  /** */
  std::map<TNode, eager::FunInfo> d_finfo;
  /** */
  std::map<TNode, eager::QuantInfo> d_qinfo;
  /** Term canonizer */
  expr::TermCanonize d_tcanon;
  /** Stats */
  eager::Stats d_stats;
  /** Are stats enabled? */
  bool d_statsEnabled;
  /** Are we registering terms when they are asserted? */
  bool d_whenEqc;
  bool d_whenEqcDelay;
  bool d_whenAsserted;
  /** Wait list */
  eager::WaitList d_eqcDelay;
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_EAGER_H */
