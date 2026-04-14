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

#include "theory/quantifiers/eager_inst.h"

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "options/base_options.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_attributes.h"
#include "theory/quantifiers/term_util.h"

// #define MULTI_TRIGGER_NEW

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EagerInst::EagerInst(Env& env,
                     QuantifiersState& qs,
                     QuantifiersInferenceManager& qim,
                     QuantifiersRegistry& qr,
                     TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr)
{
}

EagerInst::~EagerInst() {}

void EagerInst::presolve() {}

bool EagerInst::needsCheck(Theory::Effort e)
{
  // TODO: determine when to check
  return false;
}

void EagerInst::check(Theory::Effort e, QEffort quant_e)
{
  if (quant_e != QEFFORT_STANDARD)
  {
    return;
  }
  // TODO: maybe use this checkpoint to flush buffers?
}

void EagerInst::reset_round(Theory::Effort e) {}

void EagerInst::preRegisterQuantifier(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  // TODO: maybe determine watch information?
}

void EagerInst::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  // TODO: set up watched ops?
}

void EagerInst::assertNode(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  // TODO: maybe determine watch information?
}

void EagerInst::checkOwnership(Node q)
{
  if (d_ownedQuants.find(q) != d_ownedQuants.end())
  {
    d_qreg.setOwner(q, this, 2);
  }
}

std::string EagerInst::identify() const { return "eager-inst"; }

void EagerInst::notifyAssertedTerm(TNode t)
{
  if (t.getKind() != Kind::APPLY_UF)
  {
    return;
  }
  // TODO: may impact matches
}

void EagerInst::eqNotifyMerge(TNode t1, TNode t2)
{
  // TODO: may impact matches
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
