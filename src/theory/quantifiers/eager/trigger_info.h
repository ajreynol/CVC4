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
  /** Initialize this trigger for term t */
  void initialize(const Node& t);
  void watching(QuantInfo* qi);
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
  /** Set status to s, return true if a conflict is discovered */
  bool setStatus(TriggerStatus s);

  Node getPattern() const { return d_pattern; }
  Node getOperator() const { return d_op; }

 private:
  /** Get patterm term info */
  PatTermInfo* getPatTermInfo(TNode t, bool bindOrder);
  /** Reset */
  bool resetMatching();
  /** Process instantiation */
  void processInstantiation(const Node& q,
                            std::vector<Node>& inst,
                            bool isConflict);
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** Instantiation evaluator */
  std::unique_ptr<ieval::InstEvaluator> d_ieval;
  /** Quantified formulas that are watching for this trigger to activate */
  std::vector<QuantInfo*> d_qinfoWatching;
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
  /** The root pattern term, for each binding order */
  PatTermInfo* d_root[2];
  /** Status */
  context::CDO<TriggerStatus> d_status;
  /** Status proc */
  std::vector<TriggerStatus> d_statusToProc;
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
