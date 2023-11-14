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
 * Quantifier info for eager instantiation
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__TRIGGER_INFO_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__TRIGGER_INFO_H

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/eager/pat_term_info.h"
#include "theory/quantifiers/eager/util.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"
#include "theory/uf/equality_engine.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbEager;

namespace eager {

class QuantInfo;

enum class TriggerStatus
{
  NONE,
  INACTIVE,
  WAIT,
  ACTIVE
};
/** Write a status to out */
std::ostream& operator<<(std::ostream& out, TriggerStatus s);

class TriggerInfo
{
  friend class PatTermInfo;

 public:
  TriggerInfo(TermDbEager& tde);
  /**
   * Initialize this trigger for term t, or multi-trigger if mts is not empty.
   */
  void initialize(const Node& t, const std::vector<Node>& mts);
  /**
   * Notify this trigger that quantified formula q is using it, where vlist
   * specifies the substitution.
   */
  void watch(QuantInfo* qi, const std::vector<Node>& vlist);

  bool doMatching(TNode t);

  bool doMatchingAll();

  /**
   * Notify new ground term. Add instantiations to inst as needed.
   * Return true if we are in conflict.
   */
  bool notifyTerm(TNode t, bool isAsserted);
  /** Get status */
  TriggerStatus getStatus() const { return d_status.get(); }
  /** Set status to s */
  void setStatus(TriggerStatus s);

  Node getPattern() const { return d_pattern; }
  Node getOperator() const { return d_op; }

  std::string toString() const;

 private:
  /** Get patterm term info */
  PatTermInfo* getPatTermInfo(TNode t, bool bindOrder);
  /** Reset */
  bool resetMatching();
  /**
   * Complete matching using doMatchingAll for all patterns in d_mroots
   * starting at index mindex. Return true if in conflict.
   */
  bool completeMatching(size_t mindex);
  /**
   * Process instantiation for ieval quantified formula q.
   * @param q the quantified formula
   * @param inst what to instantiate it with
   * @param isConflict whether the ieval utility indicated this is a conflicting
   * instance.
   */
  void processInstantiation(const Node& q,
                            std::vector<Node>& inst,
                            bool isConflict);
  /** Process instantiations, return true if in conflict. */
  bool processInstantiations(size_t mindex);
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** Instantiation evaluator */
  std::unique_ptr<ieval::InstEvaluator> d_ieval;
  /** Quantified formulas that are actively watching instantiations for this */
  std::vector<QuantInfo*> d_qinfos;
  /** Matching quantified formulas registered to the ieval to their original */
  std::map<Node, Node> d_quantMap;
  /** Reverse of above */
  std::map<Node, Node> d_quantRMap;
  /** The pattern */
  Node d_pattern;
  /** The operator */
  Node d_op;
  /** The arity */
  size_t d_arity;
  /**
   * Mapping terms to pat term infos.
   * Index 0 stores patterns that assume top-level arguments are bound via
   * variables first. Index 1 stores patterns that assume top-level arguments
   * are bound in order.
   */
  std::map<TNode, PatTermInfo> d_pinfo[2];
  /**
   * The root pattern term, for each binding order (0:bind in order, 1:bind
   * direct variables first).
   */
  PatTermInfo* d_root[2];
  /**
   * The list of roots we are considering for doMatchingAll. This stores
   * additional patterns for multi-triggers (when d_mroots.size()>1).
   * It stores d_root[0] at index 0.
   */
  std::vector<PatTermInfo*> d_mroots;
  /** Status */
  context::CDO<TriggerStatus> d_status;
  /** Have we ever activated this? */
  bool d_hasActivated;
  /** Wait list, this would be used if we could deactivate */
  // WaitList d_terms;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
