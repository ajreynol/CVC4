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
  /** Get the next match.
   *
   * IMPORTANT: this method must return -1 (and never -2) on failure. Its
   * behavior is not invariant modulo the equality engine, since it applies
   * a term substitution and rewriting to the *concrete* term it was reset
   * with, and moreover it consumes that term in the first call after a
   * reset. Returning -1 ensures that generators upstream in the linked list
   * do not record failures involving this generator in their failure caches
   * (see InstMatchGenerator::getNextMatch).
   */
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

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
