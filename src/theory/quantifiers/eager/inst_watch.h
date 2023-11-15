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
 * Instantiation watch
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__EAGER__INST_WATCH_H
#define CVC5__THEORY__QUANTIFIERS__EAGER__INST_WATCH_H

#include "context/cdo.h"
#include "expr/node.h"
#include "theory/quantifiers/ieval/inst_evaluator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class TermDbEager;
class QuantifiersState;

namespace eager {

class WatchTermInfo
{
 public:
  WatchTermInfo(context::Context* c) : d_insts(c){}
  /** instantiations */
  context::CDHashMap<Node, bool> d_insts;
};

class WatchQuantInfo
{
public:
  WatchQuantInfo(context::Context* c) {}
  /** Instantiation evaluator */
  std::unique_ptr<ieval::InstEvaluator> d_ieval;
};
/**
 * Instantiation watch class.
 */
class InstWatch
{
 public:
  InstWatch(TermDbEager& tde);
  /** Watch this instantiation, which entailed entv */
  void watch(const Node& q, const std::vector<Node>& terms, const Node& entv);
  /** notification when master equality engine is updated */
  bool eqNotifyMerge(TNode t1, TNode t2);
 private:
  WatchTermInfo* getWatchTermInfo(const Node& t);
  WatchQuantInfo* getWatchQuantInfo(const Node& q);
  Node mkInstantiation(const Node& q, const std::vector<Node>& terms);
  Node getInstantiation(const Node& inst, std::vector<Node>& terms);
  /** Reference to the eager term database */
  TermDbEager& d_tde;
  /** Reference to quantifiers state */
  QuantifiersState& d_qs;
  /** Mapping from terms */
  std::map<Node, WatchTermInfo> d_wtInfo;
  /** Quant info */
  std::map<Node, WatchQuantInfo> d_wqInfo;
};

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
