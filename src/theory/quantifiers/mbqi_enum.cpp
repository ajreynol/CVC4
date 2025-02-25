/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Daniel Larraz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for augmenting model-based instantiations via fast sygus enumeration.
 */

#include "theory/quantifiers/mbqi_enum.h"

#include "expr/node_algorithm.h"
#include "expr/skolem_manager.h"
#include "expr/subs.h"
#include "printer/smt2/smt2_printer.h"
#include "smt/set_defaults.h"
#include "theory/datatypes/sygus_datatype_utils.h"
#include "theory/quantifiers/inst_strategy_mbqi.h"
#include "theory/quantifiers/instantiate.h"
#include "theory/quantifiers/sygus/sygus_enumerator.h"
#include "theory/quantifiers/sygus/sygus_grammar_cons.h"
#include "theory/smt_engine_subsolver.h"
#include "util/random.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

void MVarInfo::initialize(Env& env,
                          const Node& q,
                          const Node& v,
                          const std::vector<Node>& etrules)
{
  NodeManager* nm = env.getNodeManager();
  TypeNode tn = v.getType();
  Assert(MQuantInfo::shouldEnumerate(tn));
  TypeNode retType = tn;
  std::vector<Node> trules;
  if (tn.isFunction())
  {
    std::vector<TypeNode> argTypes = tn.getArgTypes();
    retType = tn.getRangeType();
    std::vector<Node> vs;
    for (const TypeNode& tnc : argTypes)
    {
      Node vc = NodeManager::mkBoundVar(tnc);
      vs.push_back(vc);
    }
    d_lamVars = nm->mkNode(Kind::BOUND_VAR_LIST, vs);
    trules.insert(trules.end(), vs.begin(), vs.end());
  }
  // include free symbols from body of quantified formula if applicable
  if (env.getOptions().quantifiers.mbqiEnumFreeSymsGrammar)
  {
    std::unordered_set<Node> syms;
    expr::getSymbols(q[1], syms);
    trules.insert(trules.end(), syms.begin(), syms.end());
  }
  // include the external terminal rules
  for (const Node& symbol : etrules)
  {
    if (std::find(trules.begin(), trules.end(), symbol) == trules.end())
    {
      trules.push_back(symbol);
    }
  }
  Trace("mbqi-fast-enum") << "Symbols: " << trules << std::endl;
  SygusGrammarCons sgc;
  Node bvl;
  TypeNode tng = sgc.mkDefaultSygusType(env, retType, bvl, trules);
  if (TraceIsOn("mbqi-fast-enum"))
  {
    Trace("mbqi-fast-enum") << "Enumerate terms for " << retType;
    if (!d_lamVars.isNull())
    {
      Trace("mbqi-fast-enum") << ", variable list " << d_lamVars;
    }
    Trace("mbqi-fast-enum") << std::endl;
    Trace("mbqi-fast-enum") << "Based on grammar:" << std::endl;
    Trace("mbqi-fast-enum")
        << printer::smt2::Smt2Printer::sygusGrammarString(tng) << std::endl;
  }
  TypeNode tuse = tng;
  const Options& opts = env.getOptions();
  if (opts.quantifiers.mbqiEnumChoiceGrammar && !retType.isBoolean())
  {
    // we will be eliminating choice
    d_cenc.reset(new ChoiceElimNodeConverter(nm));
    TypeNode bt = nm->booleanType();
    // not Boolean?
    Node x = nm->mkBoundVar("x", retType);
    trules.push_back(x);
    Trace("mbqi-fast-enum") << "Make predicate grammar " << trules << std::endl;
    TypeNode tnb = sgc.mkDefaultSygusType(env, bt, bvl, trules);
    Trace("mbqi-fast-enum") << "Predicate grammar:" << std::endl;
    Trace("mbqi-fast-enum")
        << printer::smt2::Smt2Printer::sygusGrammarString(tnb) << std::endl;
    SygusGrammar sgg({}, tng);
    SygusGrammar sgb({}, tnb);
    const std::vector<Node>& nts = sgg.getNtSyms();
    const std::vector<Node>& ntsb = sgb.getNtSyms();
    std::vector<Node> ntAll = nts;
    ntAll.insert(ntAll.end(), ntsb.begin(), ntsb.end());
    Trace("mbqi-fast-enum") << "Make combined " << ntAll << std::endl;
    SygusGrammar sgcom({}, ntAll);
    // get the non-terminal for Bool of the predicate grammar
    Trace("mbqi-fast-enum")
        << "Find non-terminal Bool in predicate grammar..." << std::endl;
    Node ntBool;
    for (const Node& nt : ntsb)
    {
      const std::vector<Node>& rules = sgb.getRulesFor(nt);
      if (nt.getType().isBoolean())
      {
        Trace("mbqi-fast-enum") << "...found " << ntBool << std::endl;
        ntBool = nt;
      }
      sgcom.addRules(nt, rules);
    }
    Assert(!ntBool.isNull());
    for (const Node& nt : nts)
    {
      Trace("mbqi-fast-enum") << "- non-terminal in sgg: " << nt << std::endl;
      std::vector<Node> rules = sgg.getRulesFor(nt);
      if (nt.getType() == retType)
      {
        Node witness = nm->mkNode(
            Kind::WITNESS, nm->mkNode(Kind::BOUND_VAR_LIST, x), ntBool);
        Trace("mbqi-fast-enum")
            << "...add " << witness << " to " << nt << std::endl;
        rules.insert(rules.begin(), witness);
      }
      sgcom.addRules(nt, rules);
    }
    TypeNode gcom = sgcom.resolve();
    Trace("mbqi-fast-enum") << "Combined grammar:" << std::endl;
    Trace("mbqi-fast-enum")
        << printer::smt2::Smt2Printer::sygusGrammarString(gcom) << std::endl;
    tuse = gcom;
  }
  d_senum.reset(new SygusTermEnumerator(env, tuse));

  for (size_t i = 0; i < 50; i++)
  {
    Node et;
    do
    {
      et = getEnumeratedTerm(nm, i);
    } while (et.isNull());
    Trace("mbqi-tmp") << "TMP Enum term: #" << i << " is " << et << std::endl;
    /*
    std::vector<std::pair<Node, InferenceId>> lemmas = getEnumeratedLemmas(et);
    for (std::pair<Node, InferenceId>& al : lemmas)
    {
      Trace("mbqi-fast-enum") << "...new lemma: " << al.first << std::endl;
    }
    */
  }
  // exit(1);
}

MVarInfo::ChoiceElimNodeConverter::ChoiceElimNodeConverter(NodeManager* nm)
    : NodeConverter(nm)
{
}
Node MVarInfo::ChoiceElimNodeConverter::postConvert(Node n)
{
  if (n.getKind() == Kind::WITNESS)
  {
    NodeManager* nm = d_nm;
    Trace("mbqi-fast-enum") << "---> convert " << n << std::endl;
    std::unordered_set<Node> fvs;
    expr::getFreeVariables(n, fvs);
    Node exists = nm->mkNode(Kind::EXISTS, n[0], n[1]);
    TypeNode retType = n[0][0].getType();
    std::vector<TypeNode> argTypes;
    std::vector<Node> ubvl;
    for (const Node& v : fvs)
    {
      ubvl.push_back(v);
      argTypes.push_back(v.getType());
    }
    if (!argTypes.empty())
    {
      retType = nm->mkFunctionType(argTypes, retType);
    }
    SkolemManager* skm = nm->getSkolemManager();
    Node sym = skm->mkInternalSkolemFunction(
        InternalSkolemId::MBQI_CHOICE_FUN, retType, {n});
    Node h = sym;
    if (!ubvl.empty())
    {
      std::vector<Node> wchildren;
      wchildren.push_back(h);
      wchildren.insert(wchildren.end(), ubvl.begin(), ubvl.end());
      h = nm->mkNode(Kind::APPLY_UF, wchildren);
    }
    Assert(h.getType() == n.getType());
    Subs subs;
    subs.add(n[0][0], h);
    Node kpred = subs.apply(n[1]);
    Node lem = nm->mkNode(Kind::OR, exists.negate(), kpred);
    if (!ubvl.empty())
    {
      lem =
          nm->mkNode(Kind::FORALL, nm->mkNode(Kind::BOUND_VAR_LIST, ubvl), lem);
    }
    Trace("mbqi-fast-enum") << "-----> lemma " << lem << std::endl;
    d_lemmas[sym] = lem;
    return h;
  }
  return n;
}

std::vector<std::pair<Node, InferenceId>> MVarInfo::getEnumeratedLemmas(
    const Node& t)
{
  std::vector<std::pair<Node, InferenceId>> lemmas;
  if (d_cenc != nullptr)
  {
    lemmas = d_cenc->getEnumeratedLemmas(t);
  }
  return lemmas;
}

std::vector<std::pair<Node, InferenceId>>
MVarInfo::ChoiceElimNodeConverter::getEnumeratedLemmas(const Node& t)
{
  std::vector<std::pair<Node, InferenceId>> lemmas;
  std::unordered_set<Node> syms;
  expr::getSymbols(t, syms, d_visited);
  Trace("mbqi-tmp") << "getEnumeratedLemmas for " << t << std::endl;
  std::map<Node, Node>::iterator itl;
  for (const Node& s : syms)
  {
    Trace("mbqi-tmp") << "...is lemma sym " << s << "?" << std::endl;
    itl = d_lemmas.find(s);
    if (itl != d_lemmas.end())
    {
      lemmas.emplace_back(itl->second,
                          InferenceId::QUANTIFIERS_MBQI_ENUM_CHOICE);
    }
  }
  return lemmas;
}

Node MVarInfo::getEnumeratedTerm(NodeManager* nm, size_t i)
{
  size_t nullCount = 0;
  while (i >= d_enum.size())
  {
    Node curr = d_senum->getCurrent();
    Trace("mbqi-fast-enum-debug") << "Enumerate: " << curr << std::endl;
    if (!curr.isNull())
    {
      // use converter if it exists
      if (d_cenc != nullptr)
      {
        curr = d_cenc->convert(curr);
      }
      if (!d_lamVars.isNull())
      {
        curr = nm->mkNode(Kind::LAMBDA, d_lamVars, curr);
      }
      Assert(!curr.isNull());
      d_enum.push_back(curr);
      nullCount = 0;
    }
    else
    {
      nullCount++;
      if (nullCount > 100)
      {
        // break if we aren't making progress
        break;
      }
    }
    if (!d_senum->incrementPartial())
    {
      // enumeration is finished
      break;
    }
  }
  if (i >= d_enum.size())
  {
    Trace("mbqi-fast-enum-debug") << "... return null" << std::endl;
    return Node::null();
  }
  Assert(!d_enum[i].isNull());
  return d_enum[i];
}

void MQuantInfo::initialize(Env& env, InstStrategyMbqi& parent, const Node& q)
{
  // The externally provided terminal rules. This set is shared between
  // all variables we instantiate.
  std::vector<Node> etrules;
  for (const Node& v : q[0])
  {
    size_t index = d_vinfo.size();
    d_vinfo.emplace_back();
    TypeNode vtn = v.getType();
    // if enumerated, add to list
    if (shouldEnumerate(vtn))
    {
      d_indices.push_back(index);
    }
    else
    {
      d_nindices.push_back(index);
      // include variables defined in terms of others if applicable
      if (env.getOptions().quantifiers.mbqiEnumExtVarsGrammar)
      {
        etrules.push_back(v);
      }
    }
  }
  // include the global symbols if applicable
  if (env.getOptions().quantifiers.mbqiEnumGlobalSymGrammar)
  {
    const context::CDHashSet<Node>& gsyms = parent.getGlobalSyms();
    for (const Node& v : gsyms)
    {
      etrules.push_back(v);
    }
  }
  // initialize the variables we are instantiating
  for (size_t index : d_indices)
  {
    d_vinfo[index].initialize(env, q, q[0][index], etrules);
  }
}

MVarInfo& MQuantInfo::getVarInfo(size_t index)
{
  Assert(index < d_vinfo.size());
  return d_vinfo[index];
}

std::vector<size_t> MQuantInfo::getInstIndices() { return d_indices; }
std::vector<size_t> MQuantInfo::getNoInstIndices() { return d_nindices; }

bool MQuantInfo::shouldEnumerate(const TypeNode& tn)
{
  if (tn.isUninterpretedSort())
  {
    return false;
  }
  return true;
}

MbqiEnum::MbqiEnum(Env& env, InstStrategyMbqi& parent)
    : EnvObj(env), d_parent(parent)
{
  d_subOptions.copyValues(options());
  smt::SetDefaults::disableChecking(d_subOptions);
}

MQuantInfo& MbqiEnum::getOrMkQuantInfo(const Node& q)
{
  auto [it, inserted] = d_qinfo.try_emplace(q);
  if (inserted)
  {
    it->second.initialize(d_env, d_parent, q);
  }
  return it->second;
}

bool MbqiEnum::constructInstantiation(
    const Node& q,
    const Node& query,
    const std::vector<Node>& vars,
    std::vector<Node>& mvs,
    const std::map<Node, Node>& mvFreshVar,
    std::vector<std::pair<Node, InferenceId>>& auxLemmas)
{
  Assert(q[0].getNumChildren() == vars.size());
  Assert(vars.size() == mvs.size());
  if (TraceIsOn("mbqi-model-enum"))
  {
    Trace("mbqi-model-enum") << "Instantiate " << q << std::endl;
    for (size_t i = 0, nvars = vars.size(); i < nvars; i++)
    {
      Trace("mbqi-model-enum")
          << "  " << q[0][i] << " -> " << mvs[i] << std::endl;
    }
  }
  SubsolverSetupInfo ssi(d_env, d_subOptions);
  MQuantInfo& qi = getOrMkQuantInfo(q);
  std::vector<size_t> indices = qi.getInstIndices();
  std::vector<size_t> nindices = qi.getNoInstIndices();
  Subs inst;
  Subs vinst;
  std::unordered_map<Node, Node> tmpCMap;
  for (size_t i : nindices)
  {
    Node v = mvs[i];
    v = d_parent.convertFromModel(v, tmpCMap, mvFreshVar);
    if (v.isNull())
    {
      return false;
    }
    Trace("mbqi-model-enum")
        << "* Assume: " << q[0][i] << " -> " << v << std::endl;
    // if we don't enumerate it, we are already considering this instantiation
    inst.add(vars[i], v);
    vinst.add(q[0][i], v);
  }
  Node queryCurr = query;
  Trace("mbqi-model-enum") << "...query is " << queryCurr << std::endl;
  queryCurr = rewrite(inst.apply(queryCurr));
  Trace("mbqi-model-enum") << "...processed is " << queryCurr << std::endl;
  // consider variables in random order, for diversity of instantiations
  std::shuffle(indices.begin(), indices.end(), Random::getRandom());
  for (size_t i = 0, isize = indices.size(); i < isize; i++)
  {
    size_t ii = indices[i];
    TNode v = vars[ii];
    MVarInfo& vi = qi.getVarInfo(ii);
    size_t cindex = 0;
    bool success = false;
    bool successEnum;
    bool lastVar = (i + 1 == isize);
    do
    {
      Node ret = vi.getEnumeratedTerm(nodeManager(), cindex);
      cindex++;
      Node retc;
      if (!ret.isNull())
      {
        Trace("mbqi-tmp") << "TMP - Try candidate: " << q.getId() << " " << v
                          << " " << cindex << " " << ret << std::endl;
        Trace("mbqi-model-enum") << "- Try candidate: " << ret << std::endl;
        // apply current substitution (to account for cases where ret has
        // other variables in its grammar).
        ret = vinst.apply(ret);
        retc = ret;
        successEnum = true;
        // now convert the value
        std::unordered_map<Node, Node> tmpConvertMap;
        std::map<TypeNode, std::unordered_set<Node> > freshVarType;
        retc = d_parent.convertToQuery(retc, tmpConvertMap, freshVarType);
      }
      else
      {
        Trace("mbqi-model-enum")
            << "- Failed to enumerate candidate" << std::endl;
        // if we failed to enumerate, just try the original
        Node mc = d_parent.convertFromModel(mvs[ii], tmpCMap, mvFreshVar);
        if (mc.isNull())
        {
          // if failed to convert, we fail
          return false;
        }
        ret = mc;
        retc = mc;
        successEnum = false;
      }
      Trace("mbqi-model-enum")
          << "- Converted candidate: " << v << " -> " << retc << std::endl;
      Node queryCheck;
      if (lastVar)
      {
        Instantiate* qinst = d_parent.d_qim.getInstantiate();
        mvs[ii] = ret;
        success = qinst->addInstantiation(
            q, mvs, InferenceId::QUANTIFIERS_INST_MBQI_ENUM);
      }
      else
      {
        // see if it is still satisfiable, if still SAT, we replace
        queryCheck = queryCurr.substitute(v, TNode(retc));
        queryCheck = rewrite(queryCheck);
        Trace("mbqi-model-enum") << "...check " << queryCheck << std::endl;
        Result r = checkWithSubsolver(queryCheck, ssi);
        success = (r == Result::SAT);
      }
      if (success)
      {
        // remember the updated query
        queryCurr = queryCheck;
        Trace("mbqi-model-enum") << "...success" << std::endl;
        Trace("mbqi-model-enum")
            << "* Enumerated " << q[0][ii] << " -> " << ret << std::endl;
        mvs[ii] = ret;
        vinst.add(q[0][ii], ret);
      }
      else if (!successEnum)
      {
        // we did not enumerate a candidate, and tried the original, which
        // failed.
        return false;
      }
    } while (!success);
  }
  // see if there are aux lemmas
  Trace("mbqi-tmp") << "TMP Instantiate: " << q.getId() << std::endl;
  for (size_t i = 0, isize = indices.size(); i < isize; i++)
  {
    size_t ii = indices[i];
    TNode v = vars[ii];
    Trace("mbqi-tmp") << "TMP - " << v << " -> " << mvs[ii] << std::endl;
    MVarInfo& vi = qi.getVarInfo(ii);
    std::vector<std::pair<Node, InferenceId>> alv =
        vi.getEnumeratedLemmas(mvs[ii]);
    Trace("mbqi-tmp") << ".TMP ..." << alv.size() << " aux lemmas" << std::endl;
    auxLemmas.insert(auxLemmas.end(), alv.begin(), alv.end());
  }
  return true;
}
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
