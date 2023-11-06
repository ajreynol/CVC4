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

#include "theory/quantifiers/eager/quant_info.h"

#include "theory/quantifiers/ematching/pattern_term_selector.h"
#include "theory/quantifiers/quantifiers_registry.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

namespace eager {

QuantInfo::QuantInfo(context::Context* c) {}

void QuantInfo::initialize(const Options& opts,
                           QuantifiersRegistry& qr,
                           TermDbEager& tde,
                           const Node& q)
{
  Assert(q.getKind() == Kind::FORALL);
  inst::PatternTermSelector pts(opts, q, opts.quantifiers.triggerSelMode);
  std::vector<Node> patTerms;
  std::map<Node, inst::TriggerTermInfo> tinfo;
  Node bd = qr.getInstConstantBody(q);
  pts.collect(bd, patTerms, tinfo);
  size_t nvars = q[0].getNumChildren();
  for (const Node& p : patTerms)
  {
    inst::TriggerTermInfo& tip = tinfo[p];
    // must be a single trigger
    if (tip.d_fv.size() != nvars)
    {
      continue;
    }
    // convert back
    Node t = qr.substituteInstConstantsToBoundVariables(p, q);
  }
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
