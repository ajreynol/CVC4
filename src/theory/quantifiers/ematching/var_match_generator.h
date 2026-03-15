/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 * Variable match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__VAR_MATCH_GENERATOR_H
#define CVC5__THEORY__QUANTIFIERS__VAR_MATCH_GENERATOR_H

#include <utility>
#include <vector>

#include "expr/node.h"
#include "theory/quantifiers/ematching/inst_match_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/** match generator for purified terms
 * This handles the special case of invertible terms like x+1 (see
 * Trigger::getTermInversionVariable).
 */
class VarMatchGeneratorTermSubs : public InstMatchGenerator
{
 public:
  VarMatchGeneratorTermSubs(Env& env, Trigger* tparent, Node var, Node subs);

  /** Reset */
  bool reset(Node eqc) override;
  /** Get the next match. */
  int getNextMatch(InstMatch& m) override;
  /** Get the inference id, for statistics. */
  InferenceId getInferenceId() override;

 private:
  /** variable we are matching (x in the example x+1). */
  Node d_var;
  /** cache of d_var.getType() */
  TypeNode d_var_type;
  /** The substitution for what we match (x-1 in the example x+1). */
  Node d_subs;
  /** stores whether we have written a value for d_var in the current match. */
  bool d_rm_prev;
};

/** match generator for purified bit-vector concatenation terms
 *
 * This handles concat terms that occur below a matchable trigger, e.g.
 * f(concat(c, x)). When matching the concat term against a ground term t,
 * this generator optimistically instantiates x with the extract corresponding
 * to its slice in t. Constant side conditions on the other slices are ignored,
 * making this an over-approximation.
 */
class VarMatchGeneratorBvConcat : public InstMatchGenerator
{
 public:
  VarMatchGeneratorBvConcat(Env& env, Trigger* tparent, Node q, Node pat);

  /** Reset. */
  bool reset(Node eqc) override;
  /** Get the next match. */
  int getNextMatch(InstMatch& m) override;
  /** Get the inference id, for statistics. */
  InferenceId getInferenceId() override;

 private:
  /** Recursively process child generators. */
  int processChildren(size_t cindex, InstMatch& m);
  /** Get the slice [high:low] of n. */
  Node getSlice(Node n, unsigned high, unsigned low) const;
  /** Reset variables that were newly assigned by the previous match. */
  void cleanupMatch(InstMatch& m);

  /** Variables that are directly bound to extracts of the matched term. */
  std::vector<int64_t> d_bindVars;
  /** The slices corresponding to d_bindVars. */
  std::vector<std::pair<unsigned, unsigned>> d_bindSlices;
  /** The slices corresponding to d_children. */
  std::vector<std::pair<unsigned, unsigned>> d_childSlices;
  /** Variables occurring in this concat pattern, in traversal order. */
  std::vector<int64_t> d_patVars;
  /** Variables that were unassigned before the current/previous match. */
  std::vector<int64_t> d_cleanupVars;
  /** Whether cleanup is required before reporting failure. */
  bool d_cleanupRequired;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
