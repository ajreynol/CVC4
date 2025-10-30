/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Gereon Kremer, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Simple inst match generator class.
 */
#include "theory/quantifiers/ematching/inst_match_generator_simple.h"

#include "options/quantifiers_options.h"
#include "theory/quantifiers/ematching/trigger_term_info.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/quantifiers_state.h"
#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_registry.h"
#include "theory/quantifiers/term_util.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace inst {

InstMatchGeneratorSimple::InstMatchGeneratorSimple(Env& env,
                                                   Trigger* tparent,
                                                   Node q,
                                                   Node pat)
    : IMGenerator(env, tparent), d_quant(q), d_match_pattern(pat),
      d_terms(d_env.getUserContext())
{
  if (d_match_pattern.getKind() == Kind::NOT)
  {
    d_match_pattern = d_match_pattern[0];
    d_pol = false;
  }
  else
  {
    d_pol = true;
  }
  if (d_match_pattern.getKind() == Kind::EQUAL)
  {
    d_eqc = d_match_pattern[1];
    d_match_pattern = d_match_pattern[0];
    Assert(!TermUtil::hasInstConstAttr(d_eqc));
  }
  Assert(TriggerTermInfo::isSimpleTrigger(d_match_pattern));
  for (size_t i = 0, nchild = d_match_pattern.getNumChildren(); i < nchild; i++)
  {
    Node p = d_match_pattern[i];
    if (p.getKind() == Kind::INST_CONSTANT && TermUtil::getInstConstAttr(p) == q)
    {
      // check independent of options
      if (TermUtil::getInstConstAttr(p) == q)
      {
        d_varNum.push_back(p.getAttribute(InstVarNumAttribute()));
      }
      else
      {
        d_varNum.push_back(-1);
      }
    }
    else
    {
      d_varNum.push_back(-1);
    }
    d_match_pattern_arg_types.push_back(p.getType());
  }
  TermDb* tdb = d_treg.getTermDatabase();
  d_op = tdb->getMatchOperator(d_match_pattern);
  d_tvec.resize(d_quant[0].getNumChildren());
}

void InstMatchGeneratorSimple::resetInstantiationRound() {}
uint64_t InstMatchGeneratorSimple::addInstantiations(InstMatch& m)
{
  uint64_t addedLemmas = 0;
  TNodeTrie* tat;
  TermDb* tdb = d_treg.getTermDatabase();
  if (d_eqc.isNull())
  {
    tat = tdb->getTermArgTrie(d_op);
  }
  else
  {
    if (d_pol)
    {
      tat = tdb->getTermArgTrie(d_eqc, d_op);
    }
    else
    {
      // iterate over all classes except r
      tat = tdb->getTermArgTrie(Node::null(), d_op);
      if (tat && !d_qstate.isInConflict())
      {
        Node r = d_qstate.getRepresentative(d_eqc);
        for (std::pair<const TNode, TNodeTrie>& t : tat->d_data)
        {
          if (t.first != r)
          {
            m.resetAll();
            addInstantiations(m, addedLemmas, 0, &(t.second));
            if (d_qstate.isInConflict())
            {
              break;
            }
          }
        }
      }
      tat = nullptr;
    }
  }
  Trace("simple-trigger-debug")
      << "Adding instantiations based on " << tat << " from " << d_op << " "
      << d_eqc << std::endl;
  if (tat && !d_qstate.isInConflict())
  {
    m.resetAll();
    addInstantiations(m, addedLemmas, 0, tat);
  }
  return addedLemmas;
}

void InstMatchGeneratorSimple::addInstantiations(InstMatch& m,
                                                 uint64_t& addedLemmas,
                                                 size_t argIndex,
                                                 TNodeTrie* tat)
{
  Trace("simple-trigger-debug")
      << "Add inst " << argIndex << " " << d_match_pattern << std::endl;
  if (argIndex == d_match_pattern.getNumChildren())
  {
    Assert(!tat->d_data.empty());
    TNode t = tat->getData();
    Trace("simple-trigger") << "Actual term is " << t << std::endl;
    // convert to actual used terms
    Assert (d_tvec.size()==t.getNumChildren());
    for (size_t i = 0, nvars = d_varNum.size(); i < nvars; i++)
    {
      if (d_varNum[i]>=0)
      {
        Assert(d_varNum[i] < t.getNumChildren());
        d_tvec[d_varNum[i]] = t[i];
      }
    }
    // we do not need the trigger parent for simple triggers (no post-processing
    // required)
    if (sendInstantiation(d_tvec,
                          InferenceId::QUANTIFIERS_INST_E_MATCHING_SIMPLE))
    {
      d_terms.insert(t);
      addedLemmas++;
      Trace("simple-trigger")
          << "-> Produced instantiation " << d_tvec << std::endl;
    }
    return;
  }
  if (d_match_pattern[argIndex].getKind() == Kind::INST_CONSTANT)
  {
    int v = d_varNum[argIndex];
    if (v != -1)
    {
      for (std::pair<const TNode, TNodeTrie>& tt : tat->d_data)
      {
        Node t = tt.first;
        // using representatives, just check if equal
        Assert(t.getType() == d_match_pattern_arg_types[argIndex]);
        bool wasSet = !m.get(v).isNull();
        if (!m.set(v, t))
        {
          continue;
        }
        if (d_qstate.isInConflict())
        {
          break;
        }
        addInstantiations(m, addedLemmas, argIndex + 1, &(tt.second));
        if (!wasSet)
        {
          m.reset(v);
        }
        if (d_qstate.isInConflict())
        {
          break;
        }
      }
      return;
    }
    // inst constant from another quantified formula, treat as ground term?
  }
  Node r = d_qstate.getRepresentative(d_match_pattern[argIndex]);
  std::map<TNode, TNodeTrie>::iterator it = tat->d_data.find(r);
  if (it != tat->d_data.end())
  {
    addInstantiations(m, addedLemmas, argIndex + 1, &(it->second));
  }
}

int InstMatchGeneratorSimple::getActiveScore()
{
  TermDb* tdb = d_treg.getTermDatabase();
  size_t ngt = tdb->getNumGroundTerms(d_op);
  Trace("trigger-active-sel-debug") << "Number of ground terms for (simple) "
                                    << d_op << " is " << ngt << std::endl;
  return static_cast<int>(ngt);
}

uint64_t InstMatchGeneratorSimple::addInstantiationsIncremental()
{
  TermDb* tdb = d_treg.getTermDatabase();
  TNodeTrie* tat = tdb->getTermArgTrie(d_op);
  if (tat == nullptr || d_qstate.isInConflict())
  {
    return 0;
  }
  // get the list of non-redundant terms from the arg trie of the operator
  std::vector<Node> list = tat->getLeaves(d_tvec.size());
  uint64_t addedLemmas = 0;
  Trace("trivial-trigger") << "Process trivial trigger " << d_match_pattern
                           << ", #terms=" << list.size() << std::endl;
  size_t procTerms = 0;
  size_t tli = 0;
  size_t tlLimit = list.size();
  while (tli < tlLimit)
  {
    Node n = list[tli];
    ++tli;
    // if already considered this term
    if (d_terms.find(n) != d_terms.end())
    {
      continue;
    }
    Trace("trivial-trigger-debug") << "...check active " << n << std::endl;
    // should be relevant if it was indexed
    Assert(tdb->hasTermCurrent(n));
    ++procTerms;
    Assert(n.getNumChildren() == d_varNum.size());
    // it is an instantiation, map it based on the variable order
    for (size_t i = 0, nvars = d_varNum.size(); i < nvars; i++)
    {
      Assert(d_varNum[i] < n.getNumChildren());
      d_tvec[d_varNum[i]] = n[i];
    }
    if (sendInstantiation(d_tvec,
                          InferenceId::QUANTIFIERS_INST_E_MATCHING_SIMPLE))
    {
      // now we can cache
      d_terms.insert(n);
      addedLemmas++;
    }
  }
  Trace("trivial-trigger") << "...lemmas/processed/total " << addedLemmas << "/"
                           << procTerms << "/" << list.size() << std::endl;
  return addedLemmas;
}

}  // namespace inst
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
