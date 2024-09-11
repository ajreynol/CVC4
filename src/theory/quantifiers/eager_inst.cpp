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
#include "theory/quantifiers/term_util.h"
#include "theory/quantifiers/quantifiers_attributes.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

EagerInst::EagerInst(Env& env,
                     QuantifiersState& qs,
                     QuantifiersInferenceManager& qim,
                     QuantifiersRegistry& qr,
                     TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_instTerms(userContext()),
      d_ownedQuants(context()),
      d_ppQuants(userContext())
{
  d_tmpAddedLemmas = 0;
  d_instOutput = isOutputOn(OutputTag::INST_STRATEGY);
}

EagerInst::~EagerInst() {}

void EagerInst::presolve() {}

bool EagerInst::needsCheck(Theory::Effort e)
{
  if (d_instOutput)
  {
    Assert(isOutputOn(OutputTag::INST_STRATEGY));
    if (d_tmpAddedLemmas > 0)
    {
      output(OutputTag::INST_STRATEGY) << "(inst-strategy " << identify();
      output(OutputTag::INST_STRATEGY) << " :inst " << d_tmpAddedLemmas;
      output(OutputTag::INST_STRATEGY) << ")" << std::endl;
      d_tmpAddedLemmas = 0;
    }
  }
  return false;
}

void EagerInst::reset_round(Theory::Effort e) {}

void EagerInst::registerQuantifier(Node q) {}

void EagerInst::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  for (const Node& n : assertions)
  {
    if (n.getKind() == Kind::FORALL)
    {
      d_ppQuants.insert(n);
      registerQuant(n);
    }
  }
}

void EagerInst::assertNode(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  //
  if (d_ppQuants.find(q) == d_ppQuants.end())
  {
    registerQuant(q);
  }
}
void EagerInst::registerQuant(const Node& q)
{
  Trace("eager-inst-register") << "Assert " << q << std::endl;
  if (q.getNumChildren() != 3)
  {
    return;
  }
  Node ipl = q[2];
  bool owner = d_ppQuants.find(q) != d_ppQuants.end();
  bool hasPat = false;
  // TODO: do for any pattern selection
  for (const Node& pat : ipl)
  {
    if (pat.getKind() == Kind::INST_PATTERN)
    {
      if (pat.getNumChildren() == 1 && pat[0].getKind() == Kind::APPLY_UF)
      {
        hasPat = true;
        Node spat = d_qreg.substituteBoundVariablesToInstConstants(pat[0], q);
        // TODO: statically analyze if this would lead to matching loops
        Trace("eager-inst-register")
            << "Single pat: " << spat << std::endl;
        Node op = spat.getOperator();
        d_userPat[op].push_back(std::pair<Node, Node>(q, spat));
        if (owner)
        {
          for (const Node& spc : spat)
          {
            if (spc.getKind() != Kind::INST_CONSTANT)
            {
              owner = false;
              break;
            }
          }
        }
      }
      else
      {
        owner = false;
      }
    }
  }
  // can maybe assign owner if only a trivial trigger and the quantified formula
  // is top level.
  if (hasPat && owner)
  {
    QAttributes qa;
    QuantAttributes::computeQuantAttributes(q, qa);
    if (qa.isStandard())
    {
      Trace("eager-inst-register") << "...owned" << std::endl;
      d_ownedQuants.insert(q);
    }
  }
}

void EagerInst::checkOwnership(Node q)
{
  if (d_ownedQuants.find(q) != d_ownedQuants.end())
  {
    d_qreg.setOwner(q, this, 2);
  }
}

void EagerInst::check(Theory::Effort e, QEffort quant_e) {}

std::string EagerInst::identify() const { return "eager-inst"; }

void EagerInst::notifyAssertedTerm(TNode t)
{
  if (t.getKind() != Kind::APPLY_UF)
  {
    return;
  }
  d_termNotifyCount[t]++;
  Trace("eager-inst-debug") << "Asserted term " << t << std::endl;
  Trace("eager-inst-stats") << "#" << d_termNotifyCount[t] << " for " << t << std::endl;
  // NOTE: in some cases a macro definition for this term may come after it is
  // registered, we don't bother handling this.
  Node op = t.getOperator();
  std::map<Node, std::vector<std::pair<Node, Node>>>::iterator it =
      d_userPat.find(op);
  if (it != d_userPat.end())
  {
    Trace("eager-inst-debug")
        << "Asserted term " << t << " has user patterns" << std::endl;
    bool addedInst = false;
    for (const std::pair<Node, Node>& p : it->second)
    {
      const Node& q = p.first;
      std::pair<Node, Node> key(t, p.second);
      if (d_instTerms.find(key)!=d_instTerms.end())
      {
        continue;
      }
      std::vector<Node> inst;
      inst.resize(q[0].getNumChildren());
      if (doMatching(q, p.second, t, inst))
      {
        Instantiate* ie = d_qim.getInstantiate();
        if (ie->addInstantiation(
                q, inst, InferenceId::QUANTIFIERS_INST_MACRO_EAGER_INST))
        {
          addedInst = true;
          d_tmpAddedLemmas++;
          d_instTerms.insert(key);
        }
      }
    }
    if (addedInst)
    {
      d_qim.doPending();
    }
  }
}

bool EagerInst::doMatching(const Node& q,
                           const Node& pat,
                           const Node& t,
                           std::vector<Node>& inst)
{
  Trace("eager-inst-debug")
      << "Do matching " << t << " " << pat << std::endl;
  for (size_t i = 0, nchild = pat.getNumChildren(); i < nchild; i++)
  {
    if (pat[i].getKind() == Kind::INST_CONSTANT)
    {
      uint64_t vnum = TermUtil::getInstVarNum(pat[i]);
      Assert(vnum < inst.size());
      if (!inst[vnum].isNull() && !d_qstate.areEqual(inst[vnum], t[i]))
      {
        return false;
      }
      inst[vnum] = t[i];
    }
    else if (TermUtil::hasInstConstAttr(pat[i]))
    {
      if (pat[i].getNumChildren() == t[i].getNumChildren())
      {
        TermDb* tdb = d_treg.getTermDatabase();
        Node mop1 = tdb->getMatchOperator(pat[i]);
        Node mop2 = tdb->getMatchOperator(t[i]);
        if (!mop1.isNull() && mop1 == mop2)
        {
          if (doMatching(q, pat[i], t[i], inst))
          {
            continue;
          }
        }
      }
      Trace("eager-inst-debug")
          << "...non-simple " << pat[i] << std::endl;
      return false;
    }
    else if (!d_qstate.areEqual(pat[i], t[i]))
    {
      Trace("eager-inst-debug")
          << "...inequal " << pat[i] << " " << t[i] << std::endl;
      return false;
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
