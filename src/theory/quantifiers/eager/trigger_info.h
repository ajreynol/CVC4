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
    INACTIVE,
    WAIT,
    ACTIVE
  };

class TriggerInfo
{
  friend class PatTermInfo;

 public:
  TriggerInfo(TermDbEager& tde);
  /** Initialize this trigger for term t */
  void initialize(const Node& t);
  /**
   * Notify this trigger that quantified formula q is using it, where vlist
   * specifies the substitution.
   */
  void watch(QuantInfo* qi, const std::vector<Node>& vlist);

  bool doMatching(TNode t, std::map<Node, std::vector<Node>>& inst);

  bool doMatchingAll(std::map<Node, std::vector<Node>>& inst);

  /** Status */
  context::CDO<TriggerStatus> d_status;
  
  /** Notify new ground term */
  void eqNotifyNewClass(TNode t);

 private:
  /** Get patterm term info */
  PatTermInfo* getPatTermInfo(TNode t);
  /** Reset */
  void resetMatching();
  /** Get active quantifiers */
  std::vector<Node> getQuantsForInst() const;
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** Instantiation evaluator */
  std::unique_ptr<ieval::InstEvaluator> d_ieval;
  /** Matching quantified formulas registered to the ieval to their original */
  std::map<Node, Node> d_quantMap;
  /** The pattern */
  Node d_pattern;
  /** The operator */
  Node d_op;
  /** The arity */
  size_t d_arity;
  /** Mapping terms to pat term infos */
  std::map<TNode, PatTermInfo> d_pinfo;
  /** The root pattern term */
  PatTermInfo* d_root;
  /** Active? */
  // context::CDO<bool> d_active;
  /** Wait list */
  // WaitList d_terms;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
