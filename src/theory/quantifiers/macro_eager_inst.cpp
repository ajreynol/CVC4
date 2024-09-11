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
 * Eager instantiation based on macros.
 */

#include "theory/quantifiers/macro_eager_inst.h"

#include "expr/attribute.h"
#include "expr/node_algorithm.h"
#include "options/quantifiers_options.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

MacroEagerInst::MacroEagerInst(Env& env,
                               QuantifiersState& qs,
                               QuantifiersInferenceManager& qim,
                               QuantifiersRegistry& qr,
                               TermRegistry& tr)
    : QuantifiersModule(env, qs, qim, qr, tr),
      d_qm(env, qr),
      d_smap(context()),
      d_macros(context()),
      d_instTerms(userContext()),
      d_ownedQuants(context())
{
  d_reqGround =
      options().quantifiers.macrosQuantMode != options::MacrosQuantMode::ALL;
}

MacroEagerInst::~MacroEagerInst() {}

void MacroEagerInst::presolve() {}

bool MacroEagerInst::needsCheck(Theory::Effort e) { return false; }

void MacroEagerInst::reset_round(Theory::Effort e) {}

void MacroEagerInst::registerQuantifier(Node q) {}

void MacroEagerInst::ppNotifyAssertions(const std::vector<Node>& assertions)
{
  // temporary
  for (const Node& n : assertions)
  {
    if (n.getKind() == Kind::FORALL)
    {
      assertNode(n);
    }
  }
}

void MacroEagerInst::assertNode(Node q)
{
  Assert(q.getKind() == Kind::FORALL);
  Trace("macro-eager-inst-debug") << "Assert " << q << std::endl;
  if (q.getNumChildren() != 3)
  {
    return;
  }
  Node ipl = q[2];
  for (const Node& pat : ipl)
  {
    if (pat.getKind() == Kind::INST_PATTERN && pat.getNumChildren() == 1
        && pat[0].getKind() == Kind::APPLY_UF)
    {
      Node spat = d_qreg.substituteBoundVariablesToInstConstants(pat[0], q);
      Trace("macro-eager-inst-debug") << "Single pat: " << spat << std::endl;
      Node op = spat.getOperator();
      d_userPat[op].push_back(std::pair<Node, Node>(q, spat));
    }
  }
  /*
  Node pat;
  Node eq = d_qm.solve(q, d_reqGround, pat);
  if (!eq.isNull())
  {
    Trace("macro-eager-inst-debug") << "...is macro for " << eq[0] << std::endl;
    Assert(eq.getKind() == Kind::EQUAL);
    Assert(eq[0].isVar());
    // check if cyclic
    if (d_smap.hasSubstitution(eq[0]))
    {
      Trace("macro-eager-inst-debug") << "...already have macro" << std::endl;
      return;
    }
    Node srhs = d_smap.apply(eq[1]);
    if (expr::hasSubterm(srhs, eq[0]))
    {
      Trace("macro-eager-inst-debug") << "...cyclic macro" << std::endl;
      return;
    }
    // otherwise, we have a macro
    Trace("macro-eager-inst") << "Asserted macro: " << eq[0] << std::endl;
    Trace("macro-eager-inst") << "    definition: " << q << std::endl;
    Node patn = d_qreg.substituteBoundVariablesToInstConstants(pat, q);
    Trace("macro-eager-inst") << "       pattern: " << patn << std::endl;
    d_macros.insert(eq[0], std::pair<Node, Node>(q, patn));
    d_ownedQuants.insert(q);
  }
  else
  {
    Trace("macro-eager-inst-debug") << "...not a macro quant" << std::endl;
  }
  */
}

void MacroEagerInst::checkOwnership(Node q)
{
  // maybe take ownership???
  if (d_ownedQuants.find(q) != d_ownedQuants.end())
  {
    d_qreg.setOwner(q, this, 1);
  }
}

void MacroEagerInst::check(Theory::Effort e, QEffort quant_e) {}

std::string MacroEagerInst::identify() const { return "MacroEagerInst"; }

void MacroEagerInst::notifyAssertedTerm(TNode t)
{
  if (t.getKind() != Kind::APPLY_UF)
  {
    return;
  }
  Trace("macro-eager-inst-debug") << "Asserted term " << t << std::endl;
  // NOTE: in some cases a macro definition for this term may come after it is
  // registered, we don't bother handling this.
  Node op = t.getOperator();
  std::map<Node, std::vector<std::pair<Node, Node>>>::iterator it =
      d_userPat.find(op);
  if (it != d_userPat.end())
  {
    Trace("macro-eager-inst-debug")
        << "Asserted term " << t << " has user patterns" << std::endl;
    bool addedInst = false;
    for (const std::pair<Node, Node>& p : it->second)
    {
      const Node& q = p.first;
      std::vector<Node> inst;
      inst.resize(q[0].getNumChildren());
      if (doMatching(q, p.second, t, inst))
      {
        Instantiate* ie = d_qim.getInstantiate();
        ie->addInstantiation(q, inst, InferenceId::QUANTIFIERS_INST_MACRO_EAGER_INST);
        addedInst = true;
      }
    }
    if (addedInst)
    {
      d_qim.doPending();
    }
  }
  /*
  NodePairMap::const_iterator it = d_macros.find(op);
  if (it == d_macros.end())
  {
    return;
  }
  Node q = it->second.first;
  std::pair<Node, Node> key(t, q);
  if (d_instTerms.find(key) != d_instTerms.end())
  {
    return;
  }
  d_instTerms.insert(key);
  Node pat = it->second.second;
  Trace("macro-eager-inst-debug")
      << "Asserted term " << t << " has a macro definition" << std::endl;
  std::vector<Node> inst;
  inst.resize(q[0].getNumChildren());
  for (size_t i = 0, nchild = pat.getNumChildren(); i < nchild; i++)
  {
    uint64_t vnum = TermUtil::getInstVarNum(pat[i]);
    Assert(vnum < inst.size());
    inst[vnum] = t[i];
  }
  Trace("macro-eager-inst-debug") << "Instantiation is: " << inst << std::endl;
  Instantiate* ie = d_qim.getInstantiate();
  // note that the instantiation may already be implied, we mark t has processed
  // regardless
  ie->addInstantiation(q, inst, InferenceId::QUANTIFIERS_INST_MACRO_EAGER_INST);
  */
}

bool MacroEagerInst::doMatching(const Node& q, const Node& pat, const Node& t, std::vector<Node>& inst)
{
  Trace("macro-eager-inst-debug")
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
      Trace("macro-eager-inst-debug")
          << "...non-simple " << pat[i] << std::endl;
      return false;
    }
    else if (!d_qstate.areEqual(pat[i], t[i]))
    {
      Trace("macro-eager-inst-debug")
          << "...inequal " << pat[i] << " " << t[i] << std::endl;
      return false;
    }
  }
  return true;
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
