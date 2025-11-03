/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Relevant domain class.
 */

#include "cvc5_private.h"

#ifndef CVC5__THEORY__QUANTIFIERS__ANALYZE_EE_H
#define CVC5__THEORY__QUANTIFIERS__ANALYZE_EE_H

#include "theory/quantifiers/quant_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

class QuantifiersState;
class QuantifiersRegistry;
class TermRegistry;

/**
 */
class AnalyzeEqualityEngine : public QuantifiersUtil
{
 public:
  AnalyzeEqualityEngine(Env& env,
                 QuantifiersState& qs,
                 QuantifiersRegistry& qr,
                 TermRegistry& tr);
  virtual ~AnalyzeEqualityEngine();
  /** Reset. */
  bool reset(Theory::Effort e) override;
  /** identify */
  std::string identify() const override { return "AnalyzeEqualityEngine"; }
private:
  /** Reference to the quantifiers state object */
  QuantifiersState& d_qs;
  /** Reference to the quantifiers registry */
  QuantifiersRegistry& d_qreg;
  /** Reference to the term registry */
  TermRegistry& d_treg;
  class EqcInfo
  {
  public:
    std::vector<Node> d_terms;
  };
  std::map<Node, EqcInfo> d_einfo;
  std::unordered_set<Node> d_es;
};/* class AnalyzeEqualityEngine */

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal

#endif /* CVC5__THEORY__QUANTIFIERS__ANALYZE_EE_H */
