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

#include "expr/node.h"
#include "expr/term_canonize.h"
#include "smt/env_obj.h"
#include "theory/quantifiers/eager/fun_info.h"
#include "theory/quantifiers/eager/quant_info.h"
#include "theory/quantifiers/eager/stats.h"
#include "theory/quantifiers/eager/trigger_info.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

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
  eager::QuantInfo& getQuantInfo(TNode q);
  /** Get fun info */
  eager::FunInfo& getFunInfo(TNode f);

  //==========
  TermDb& getTermDb() { return d_tdb; }
  expr::TermCanonize& getTermCanon() { return d_tcanon; }
  eager::Stats& getStats() { return d_stats; }
  QuantifiersState& getState() { return d_qs; }
  CDTNodeTrieAllocator* getCdtAlloc() { return &d_cdalloc; }

 private:
  Node d_null;
  QuantifiersState& d_qs;
  /** The quantifiers registry */
  QuantifiersRegistry& d_qreg;
  TermDb& d_tdb;
  CDTNodeTrieAllocator d_cdalloc;
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
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__TERM_DATABASE_EAGER_H */
