/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of variable match generator class.
 */
#include <algorithm>

#include "theory/quantifiers/ematching/var_match_generator.h"

#include "theory/quantifiers/term_util.h"
#include "theory/rewriter.h"
#include "util/bitvector.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

namespace {

void collectPatVars(Node n, Node q, std::vector<int64_t>& vars)
{
  if (n.getKind() == Kind::INST_CONSTANT
      && quantifiers::TermUtil::getInstConstAttr(n) == q)
  {
    int64_t v = n.getAttribute(InstVarNumAttribute());
    if (std::find(vars.begin(), vars.end(), v) == vars.end())
    {
      vars.push_back(v);
    }
    return;
  }
  for (const Node& nc : n)
  {
    if (quantifiers::TermUtil::hasInstConstAttr(nc))
    {
      collectPatVars(nc, q, vars);
    }
  }
}

}  // namespace

VarMatchGeneratorTermSubs::VarMatchGeneratorTermSubs(Env& env,
                                                     Trigger* tparent,
                                                     Node var,
                                                     Node subs)
    : InstMatchGenerator(env, tparent, Node::null()),
      d_var(var),
      d_subs(subs),
      d_rm_prev(false)
{
  d_children_types.push_back(d_var.getAttribute(InstVarNumAttribute()));
  d_var_type = d_var.getType();
}

bool VarMatchGeneratorTermSubs::reset(Node eqc)
{
  d_eq_class = eqc;
  return true;
}

int VarMatchGeneratorTermSubs::getNextMatch(InstMatch& m)
{
  size_t index = d_children_types[0];
  int ret_val = -1;
  if (!d_eq_class.isNull())
  {
    Trace("var-trigger-matching") << "Matching " << d_eq_class << " against "
                                  << d_var << " in " << d_subs << std::endl;
    TNode tvar = d_var;
    Node s = d_subs.substitute(tvar, d_eq_class);
    s = rewrite(s);
    Trace("var-trigger-matching")
        << "...got " << s << ", " << s.getKind() << std::endl;
    d_eq_class = Node::null();
    d_rm_prev = m.get(index).isNull();
    if (!m.set(index, s))
    {
      return -1;
    }
    else
    {
      ret_val = continueNextMatch(m);
      if (ret_val > 0)
      {
        return ret_val;
      }
    }
  }
  if (d_rm_prev)
  {
    m.reset(index);
    d_rm_prev = false;
  }
  return -1;
}

InferenceId VarMatchGeneratorTermSubs::getInferenceId()
{
  return InferenceId::QUANTIFIERS_INST_E_MATCHING_VAR_GEN;
}

VarMatchGeneratorBvConcat::VarMatchGeneratorBvConcat(Env& env,
                                                     Trigger* tparent,
                                                     Node q,
                                                     Node pat)
    : InstMatchGenerator(env, tparent, Node::null()),
      d_cleanupRequired(false)
{
  Assert(pat.getKind() == Kind::BITVECTOR_CONCAT);
  collectPatVars(pat, q, d_patVars);
  unsigned currHigh = pat.getType().getBitVectorSize();
  for (const Node& pc : pat)
  {
    unsigned psize = pc.getType().getBitVectorSize();
    Assert(currHigh >= psize);
    unsigned high = currHigh - 1;
    unsigned low = currHigh - psize;
    currHigh -= psize;
    if (!quantifiers::TermUtil::hasInstConstAttr(pc))
    {
      continue;
    }
    Node qa = quantifiers::TermUtil::getInstConstAttr(pc);
    if (pc.getKind() == Kind::INST_CONSTANT && qa == q)
    {
      d_bindVars.push_back(pc.getAttribute(InstVarNumAttribute()));
      d_bindSlices.emplace_back(high, low);
      continue;
    }
    InstMatchGenerator* cimg =
        InstMatchGenerator::mkInstMatchGenerator(env, tparent, q, pc);
    cimg->setActiveAdd(false);
    d_children.push_back(cimg);
    d_childSlices.emplace_back(high, low);
  }
  Assert(currHigh == 0);
}

bool VarMatchGeneratorBvConcat::reset(Node eqc)
{
  d_eq_class = eqc;
  d_cleanupRequired = false;
  d_cleanupVars.clear();
  return !eqc.isNull();
}

int VarMatchGeneratorBvConcat::getNextMatch(InstMatch& m)
{
  if (d_cleanupRequired)
  {
    cleanupMatch(m);
    return -1;
  }
  if (d_eq_class.isNull())
  {
    return -1;
  }
  for (int64_t v : d_patVars)
  {
    if (m.get(v).isNull())
    {
      d_cleanupVars.push_back(v);
    }
  }
  Node eqc = d_eq_class;
  d_eq_class = Node::null();
  bool success = true;
  for (size_t i = 0, size = d_bindVars.size(); i < size; i++)
  {
    Node slice = getSlice(eqc, d_bindSlices[i].first, d_bindSlices[i].second);
    if (!m.set(d_bindVars[i], slice))
    {
      success = false;
      break;
    }
  }
  for (size_t i = 0, size = d_children.size(); success && i < size; i++)
  {
    Node slice = getSlice(eqc, d_childSlices[i].first, d_childSlices[i].second);
    success = d_children[i]->reset(slice);
  }
  int ret = -1;
  if (success)
  {
    ret = processChildren(0, m);
  }
  if (ret > 0)
  {
    d_cleanupRequired = true;
    return ret;
  }
  cleanupMatch(m);
  return -1;
}

InferenceId VarMatchGeneratorBvConcat::getInferenceId()
{
  return InferenceId::QUANTIFIERS_INST_E_MATCHING_VAR_GEN;
}

int VarMatchGeneratorBvConcat::processChildren(size_t cindex, InstMatch& m)
{
  if (cindex == d_children.size())
  {
    return continueNextMatch(m);
  }
  while (d_children[cindex]->getNextMatch(m) > 0)
  {
    int ret = processChildren(cindex + 1, m);
    if (ret > 0)
    {
      return ret;
    }
  }
  return -1;
}

Node VarMatchGeneratorBvConcat::getSlice(Node n, unsigned high, unsigned low) const
{
  if (low == 0 && high + 1 == n.getType().getBitVectorSize())
  {
    return n;
  }
  NodeManager* nm = nodeManager();
  Node extractOp = nm->mkConst<BitVectorExtract>(BitVectorExtract(high, low));
  return rewrite(nm->mkNode(extractOp, n));
}

void VarMatchGeneratorBvConcat::cleanupMatch(InstMatch& m)
{
  for (auto it = d_cleanupVars.rbegin(); it != d_cleanupVars.rend(); ++it)
  {
    if (!m.get(*it).isNull())
    {
      m.reset(*it);
    }
  }
  d_cleanupVars.clear();
  d_cleanupRequired = false;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
