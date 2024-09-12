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

#include "smt/env_obj.h"
#include "theory/quantifiers/quant_module.h"
#include "theory/substitutions.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class EagerWatchInfo
{
  using NodeMap = context::CDHashMap<Node, Node>;
public:
};
    
/**
 */
class EagerInst : public QuantifiersModule
{
  using NodePairMap = context::CDHashMap<Node, std::pair<Node, Node>>;
  using NodePairListMap =
      context::CDHashMap<Node, std::vector<std::pair<Node, Node>>>;
  using NodeSet = context::CDHashSet<Node>;
  using NodePairHashFunction =
      PairHashFunction<Node, Node, std::hash<Node>, std::hash<Node>>;
  using NodePairSet =
      context::CDHashSet<std::pair<Node, Node>, NodePairHashFunction>;

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
  /** Register quantified formula q */
  void registerQuantifier(Node q) override;
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

  /** Notify asserted term */
  void notifyAssertedTerm(TNode n);

  /* For collecting global terms from all available assertions. */
  void ppNotifyAssertions(const std::vector<Node>& assertions) override;

 private:
  void registerQuant(const Node& q);
  Node solveMacro(Node& q, Node& pat);
  NodePairSet d_instTerms;
  NodeSet d_ownedQuants;
  size_t d_tmpAddedLemmas;
  bool d_instOutput;
  NodeSet d_ppQuants;
  std::map<Node, size_t> d_termNotifyCount;
  NodeSet d_fullInstTerms;
  NodeSet d_cdOps;
  //
  std::map<Node, std::vector<std::pair<Node, Node>>> d_userPat;
  bool doMatching(const Node& q,
                  const Node& pat,
                  const Node& n,
                  std::vector<Node>& inst,
                  std::map<Node, Node>& failWasCd);
};

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
