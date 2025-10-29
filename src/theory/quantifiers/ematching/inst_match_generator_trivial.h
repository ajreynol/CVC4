/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Trivial inst match generator class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_TRIVIAL_H
#define CVC5__THEORY__QUANTIFIERS__INST_MATCH_GENERATOR_TRIVIAL_H

#include <map>
#include <vector>

#include "theory/quantifiers/ematching/inst_match_generator.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

/**
 * InstMatchGeneratorTrivial class
 */
class InstMatchGeneratorTrivial : public IMGenerator
{
 public:
  /** constructors */
  InstMatchGeneratorTrivial(Env& env, Trigger* tparent, Node q, Node pat);

  /** Reset instantiation round. */
  void resetInstantiationRound() override;
  /** Add instantiations. */
  uint64_t addInstantiations(InstMatch& m) override;
  /** Get active score. */
  int getActiveScore() override;
  /** Is trivial trigger? */
  static bool isTrivialTrigger(const Node& pat);

 private:
  /** quantified formula for the trigger term */
  Node d_quant;
  /** the trigger term */
  Node d_pat;
  /** The match operator d_match_pattern (see TermDb::getMatchOperator). */
  Node d_op;
  /** List of terms we have matched */
  context::CDHashSet<Node> d_terms;
  /** The variable number for each argument */
  std::vector<uint64_t> d_varNum;
  /** Terms used for instantiation */
  std::vector<Node> d_tvec;
};

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif
