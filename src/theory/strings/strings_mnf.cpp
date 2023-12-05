/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2022 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Model normal form finder for strings
 */

#include "theory/strings/strings_mnf.h"

#include "options/strings_options.h"
#include "theory/strings/base_solver.h"
#include "theory/strings/core_solver.h"
#include "theory/strings/extf_solver.h"
#include "theory/strings/theory_strings_utils.h"
#include "theory/strings/word.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace theory {
namespace strings {

std::string ModelEqcInfo::toString() const
{
  std::stringstream ss;
  ss << d_mnf << " / " << d_length;
  return ss.str();
}

void ModelEqcInfo::expand(const Node& n, const std::vector<Node>& nn)
{
  expandNormalForm(d_mnf, n, nn);
}

void ModelEqcInfo::expandNormalForm(std::vector<Node>& mnf,
                                    const Node& n,
                                    const std::vector<Node>& nn)
{
  Assert(!nn.empty());
  size_t i = 0;
  while (i < mnf.size())
  {
    if (mnf[i] == n)
    {
      mnf[i] = nn[0];
      mnf.insert(mnf.begin() + i + 1, nn.begin() + 1, nn.end());
      i += nn.size();
    }
    else
    {
      i++;
    }
  }
}

StringsMnf::StringsMnf(Env& env,
                       SolverState& s,
                       InferenceManager& im,
                       TermRegistry& tr,
                       BaseSolver& bs,
                       CoreSolver& cs)
    : ModelCons(env),
      d_state(s),
      d_im(im),
      d_termReg(tr),
      d_bsolver(bs),
      d_csolver(cs)
{
  d_zero = NodeManager::currentNM()->mkConstInt(Rational(0));
  // get the maximum model length
  d_maxModelLen = options().strings.stringsModelMaxLength;
  if (d_maxModelLen < 65536)
  {
    d_maxModelLen = 65536;
  }
}

bool StringsMnf::checkModelNormalforms()
{
  const std::vector<Node>& stringsEqc = d_csolver.getStringsEqc();
  Trace("strings-mnf") << "StringsMnf: findModelNormalForms..." << std::endl;
  // reset the state
  d_minfo.clear();
  d_mrepMap.clear();
  d_constLike.clear();
  // Try to find model normal form for each equivalence class, where stringsEqc
  // is sorted based on containment ordering.
  for (const Node& eqc : stringsEqc)
  {
    Trace("strings-mnf") << "process-eqc " << eqc << std::endl;
    if (!normalizeEqc(eqc))
    {
      Trace("strings-mnf") << "StringsMnf: ...fail eqc" << std::endl;
      return false;
    }
  }
  // also check disequalities
  if (!checkDisequalities())
  {
    return false;
  }
  // also check cardinality
  if (!checkCardinality())
  {
    return false;
  }

  Trace("strings-mnf") << "StringsMnf: ...success!!!" << std::endl;
  // If successful and non-trivial, this class will be the model constructor.
  if (!stringsEqc.empty())
  {
    d_state.setModelConstructor(this);
  }
  return true;
}

bool StringsMnf::checkDisequalities()
{
  const context::CDList<Node>& deqs = d_state.getDisequalityList();
  std::map<Node, std::unordered_set<Node>> processed;
  for (const Node& deq : deqs)
  {
    Assert(deq.getKind() == Kind::EQUAL);
    Node a = getModelRepresentative(deq[0]);
    Node b = getModelRepresentative(deq[1]);
    if (a < b)
    {
      std::swap(a, b);
    }
    std::unordered_set<Node>& pa = processed[a];
    if (pa.find(b) != pa.end())
    {
      continue;
    }
    pa.insert(b);
    Trace("strings-mnf") << "process-disequality " << deq << " (" << a << ", "
                         << b << ")" << std::endl;
    Rational la = getLength(a);
    Rational lb = getLength(b);
    if (la != lb)
    {
      continue;
    }
    if (!normalizeDeq(a, b))
    {
      Trace("strings-mnf") << "StringsMnf: ...fail disequality" << std::endl;
      return false;
    }
  }
  return true;
}

bool StringsMnf::checkCardinality()
{
  // ensure cardinality is ok?
  std::map<TypeNode, size_t> typeReq;
  std::map<TypeNode, size_t>::iterator itt;
  std::map<std::pair<TypeNode, Rational>, size_t> eqcCounts;
  for (const std::pair<const Node, ModelEqcInfo>& mi : d_minfo)
  {
    TypeNode tn = mi.first.getType();
    itt = typeReq.find(tn);
    if (itt == typeReq.end())
    {
      size_t typeCard;
      BaseSolver::CardinalityResponse cr =
          d_bsolver.getCardinalityReq(tn, typeCard);
      if (cr == BaseSolver::CardinalityResponse::UNHANDLED)
      {
        Trace("strings-mnf")
            << "StringsMnf: ...fail cardinality type" << std::endl;
        return false;
      }
      else if (cr == BaseSolver::CardinalityResponse::NO_REQ)
      {
        typeReq[tn] = 0;
        continue;
      }
      typeReq[tn] = typeCard;
    }
    else if (itt->second == 0)
    {
      continue;
    }
    std::pair<TypeNode, Rational> key(tn, mi.second.d_length);
    eqcCounts[key]++;
  }
  NodeManager* nm = NodeManager::currentNM();
  for (const std::pair<const std::pair<TypeNode, Rational>, size_t>& ec :
       eqcCounts)
  {
    TypeNode tn = ec.first.first;
    Assert(typeReq.find(tn) != typeReq.end());
    size_t treq = typeReq[tn];
    Node lr = nm->mkConstInt(ec.first.second);
    if (!d_bsolver.isCardinalityOk(treq, lr, ec.second))
    {
      Trace("strings-mnf")
          << "StringsMnf: ...fail cardinality for number of eqc " << tn
          << " of length " << lr << std::endl;
      return false;
    }
  }
  return true;
}

bool StringsMnf::hasCandidateModel() { return true; }

void StringsMnf::getStringRepresentativesFrom(
    const std::set<Node>& termSet,
    std::unordered_set<TypeNode>& repTypes,
    std::map<TypeNode, std::unordered_set<Node>>& repSet,
    std::vector<Node>& auxEq)
{
  std::vector<Node> toProcess(termSet.begin(), termSet.end());
  size_t i = 0;
  std::unordered_set<Node> processed;
  std::map<Node, ModelEqcInfo>::iterator it;
  while (i < toProcess.size())
  {
    Node t = d_state.getRepresentative(toProcess[i]);
    i++;
    if (processed.find(t) != processed.end())
    {
      continue;
    }
    processed.insert(t);
    TypeNode tn = t.getType();
    if (!tn.isStringLike())
    {
      continue;
    }
    Node mt = getModelRepresentative(t);
    if (mt != t)
    {
      // set equal and continue
      toProcess.push_back(mt);
      auxEq.push_back(t.eqNode(mt));
      continue;
    }
    repTypes.insert(tn);
    repSet[tn].insert(mt);
    // also ensure all terms in the normal form are processed, in case
    // we split mt
    it = d_minfo.find(mt);
    if (it != d_minfo.end())
    {
      toProcess.insert(
          toProcess.end(), it->second.d_mnf.begin(), it->second.d_mnf.end());
    }
  }
}

void StringsMnf::separateByLength(const std::vector<Node>& ns,
                                  std::vector<std::vector<Node>>& cols,
                                  std::vector<Node>& lts)
{
  std::map<Node, ModelEqcInfo>::iterator it;
  std::map<Rational, size_t> lenToIndex;
  std::map<Rational, size_t>::iterator itl;
  NodeManager* nm = NodeManager::currentNM();
  for (const Node& n : ns)
  {
    Rational len;
    if (n.isConst())
    {
      len = Rational(Word::getLength(n));
    }
    else
    {
      it = d_minfo.find(n);
      Assert(it != d_minfo.end());
      len = it->second.d_length;
    }
    itl = lenToIndex.find(len);
    if (itl != lenToIndex.end())
    {
      cols[itl->second].push_back(n);
    }
    else
    {
      lenToIndex[len] = cols.size();
      cols.emplace_back(std::vector<Node>{n});
      lts.push_back(nm->mkConstInt(len));
    }
  }
}

std::vector<Node> StringsMnf::getNormalForm(Node n)
{
  Node r = getModelRepresentative(n);
  return getNormalFormInternal(r);
}

std::vector<Node> StringsMnf::getNormalFormInternal(const Node& n)
{
  Assert(n == getModelRepresentative(n));
  std::vector<Node> vec;
  std::map<Node, ModelEqcInfo>::iterator it = d_minfo.find(n);
  if (it != d_minfo.end())
  {
    vec = it->second.d_mnf;
  }
  else
  {
    // Shouln't ask for normal forms of strings that weren't computed. This
    // likely means that n is not a representative or not a term in the current
    // context. We simply return a default normal form here in this case.
    Assert(false) << "No normal form for " << n << std::endl;
    vec.push_back(n);
  }
  return vec;
}

bool StringsMnf::normalizeEqc(Node eqc)
{
  Valuation& val = d_state.getValuation();
  ModelEqcInfo& mei = d_minfo[eqc];
  // if empty string, we initialize normal form to empty
  Node emp = Word::mkEmptyWord(eqc.getType());
  if (d_state.areEqual(eqc, emp))
  {
    mei.d_length = Rational(0);
    Trace("strings-mnf") << "NF " << eqc << " (empty): " << mei.toString()
                         << std::endl;
    return true;
  }
  // compute the length of the equivalence class
  EqcInfo* ei = d_state.getOrMakeEqcInfo(eqc, false);
  Node lt = ei ? ei->d_lengthTerm : Node::null();
  if (lt.isNull())
  {
    // does not have a length term, we must fail
    Trace("strings-mnf") << "Fail: " << eqc << " has no length term."
                         << std::endl;
    return false;
  }
  // otherwise, look up the model value now
  mei.d_length = val.getCandidateModelValue(lt).getConst<Rational>();

  // get the normal form for each term in the equivalence class
  std::vector<std::pair<Node, std::vector<Node>>> nfs;
  eq::EqualityEngine* ee = d_state.getEqualityEngine();
  eq::EqClassIterator eqc_i = eq::EqClassIterator(eqc, ee);
  bool addedConstLike = false;
  while (!eqc_i.isFinished())
  {
    Node n = (*eqc_i);
    ++eqc_i;
    Trace("strings-mnf-debug") << "Compute normal form " << n << std::endl;
    if (d_bsolver.isCongruent(n))
    {
      Trace("strings-mnf-debug") << "...congruent" << std::endl;
      continue;
    }
    if (utils::isConstantLike(n))
    {
      nfs.emplace_back(n, std::vector<Node>{n});
      if (n != eqc && !addedConstLike)
      {
        d_constLike.emplace_back(eqc, n);
        addedConstLike = true;
      }
      Trace("strings-mnf-debug") << "...constant-like" << std::endl;
      continue;
    }
    if (n.getKind() == Kind::STRING_CONCAT)
    {
      // expand the normal form of the representative of each child
      std::vector<Node> nf;
      for (const Node& nc : n)
      {
        Trace("strings-mnf-debug") << "...concat child " << nc << std::endl;
        std::vector<Node> nfr = getNormalForm(nc);
        nf.insert(nf.end(), nfr.begin(), nfr.end());
      }
      // if not singular, add to vector
      if (nf.size() > 1 || (nf.size() == 1 && utils::isConstantLike(nf[0])))
      {
        nfs.emplace_back(n, nf);
      }
    }
  }

  // if we are an atomic equivalence class, just add
  if (nfs.empty())
  {
    mei.d_mnf.emplace_back(eqc);
    Trace("strings-mnf") << "NF " << eqc << " (singular): " << mei.toString()
                         << std::endl;
  }
  else
  {
    // now, process each normal form
    bool firstTime = true;
    // list of modifications done to normal forms while processing this
    // equivalence class
    std::vector<std::pair<Node, std::vector<Node>>> currExpands;
    for (std::pair<Node, std::vector<Node>>& nf : nfs)
    {
      if (firstTime)
      {
        // first one sets the model normal form of the overall eqc
        mei.d_mnf = nf.second;
        firstTime = false;
        continue;
      }
      // First, update nf.second based on expands done for previous normal forms
      // in this equivalence class
      for (const std::pair<Node, std::vector<Node>>& ce : currExpands)
      {
        ModelEqcInfo::expandNormalForm(nf.second, ce.first, ce.second);
      }
      Trace("strings-mnf-solve") << "Compare: " << std::endl;
      Trace("strings-mnf-solve") << "[1] " << mei.d_mnf << std::endl;
      Trace("strings-mnf-solve") << "[2] " << nf.second << std::endl;

      // Now, compare mei.d_mnf and nf.second left to right
      size_t i = 0;
      while (i < mei.d_mnf.size())
      {
        Node a = mei.d_mnf[i];
        Node b = nf.second[i];
        if (a == b)
        {
          i++;
          continue;
        }
        Rational la = getLength(a);
        Rational lb = getLength(b);
        Trace("strings-mnf-solve")
            << "Compare " << a << " / " << b << ", lengths=" << la << " / "
            << lb << std::endl;
        // should have positive lengths
        Assert(la.sgn() == 1 && lb.sgn() == 1);
        // if lengths are already equal, merge b into a
        if (la == lb)
        {
          // fail if merging constant-like terms
          bool constA = utils::isConstantLike(a);
          bool constB = utils::isConstantLike(b);
          if (constA && constB)
          {
            // conflict, we fail
            Trace("strings-mnf") << "Fail: " << eqc << " while merging " << a
                                 << ", " << b << std::endl;
            return false;
          }
          if (!constA
              && (constB || (!d_state.hasTerm(a) && d_state.hasTerm(b))))
          {
            // Flip is b is constant and a is not.
            // Also flip if a is an auxiliary skolem but b is not. This is
            // required for properly tracking other information during
            // collectModelValues, e.g. str.code, which expects equivalence
            // classes of the equality engine.
            std::swap(a, b);
          }
          // otherwise merge b into a
          merge(a, b);
          // remember the operation
          currExpands.emplace_back(b, std::vector<Node>{a});
          i++;
        }
        else if (la > lb)
        {
          // otherwise, split
          std::vector<Node> avec = split(a, la, lb);
          currExpands.emplace_back(a, avec);
        }
        else
        {
          Assert(la < lb);
          std::vector<Node> bvec = split(b, lb, la);
          currExpands.emplace_back(b, bvec);
        }
        // apply the expansion to the current normal form (nf.second) we are
        // processing, which makes a difference in the current equivalence
        // class has multiple occurrences of b.
        Assert(!currExpands.empty());
        std::pair<Node, std::vector<Node>> ce = currExpands.back();
        ModelEqcInfo::expandNormalForm(nf.second, ce.first, ce.second);
      }
    }
    Trace("strings-mnf") << "NF " << eqc << " : " << mei.toString()
                         << std::endl;
  }

  // if there is a code term, we look up its value and merge?
  if (!ei->d_codeTerm.get().isNull() && mei.d_length.isOne())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node ct = nm->mkNode(Kind::STRING_TO_CODE, ei->d_codeTerm.get());
    Node ctv = val.getCandidateModelValue(ct);
    unsigned cvalue = ctv.getConst<Rational>().getNumerator().toUnsignedInt();
    std::vector<unsigned> vec;
    vec.push_back(cvalue);
    Node assignedValue = nm->mkConst(String(vec));
    // only if the value is not already in this equivalance class, in which
    // case it should be the representative.
    if (assignedValue != eqc)
    {
      Rational one(1);
      ensureModelInfo(assignedValue, one);
      merge(assignedValue, eqc);
    }
  }

  return true;
}

bool StringsMnf::normalizeDeq(Node ar, Node br)
{
  Assert(ar == getModelRepresentative(ar) && d_minfo.find(ar) != d_minfo.end());
  Assert(br == getModelRepresentative(br) && d_minfo.find(br) != d_minfo.end());
  ModelEqcInfo& meia = d_minfo[ar];
  ModelEqcInfo& meib = d_minfo[br];

  Trace("strings-mnf-solve") << "Compare-disequal: " << std::endl;
  Trace("strings-mnf-solve") << "[1] " << meia.d_mnf << std::endl;
  Trace("strings-mnf-solve") << "[2] " << meib.d_mnf << std::endl;
  size_t i = 0;
  while (i < meia.d_mnf.size())
  {
    Assert(i < meib.d_mnf.size());
    Node a = meia.d_mnf[i];
    Node b = meib.d_mnf[i];
    if (a == b)
    {
      i++;
      continue;
    }
    Rational la = getLength(a);
    Rational lb = getLength(b);
    if (la == lb)
    {
      // equal length components will be assigned different values, we are done
      return true;
    }
    Node s;
    std::vector<Node> svec;
    if (la > lb)
    {
      // otherwise, split
      s = a;
      svec = split(a, la, lb);
    }
    else
    {
      Assert(la < lb);
      s = b;
      svec = split(b, lb, la);
    }
    ModelEqcInfo::expandNormalForm(meia.d_mnf, s, svec);
    ModelEqcInfo::expandNormalForm(meib.d_mnf, s, svec);
  }
  return false;
}

Rational StringsMnf::getLength(const Node& r)
{
  Assert(r.getType().isStringLike());
  if (r.isConst())
  {
    return Word::getLength(r);
  }
  else if (r.getKind() == Kind::STRING_UNIT || r.getKind() == Kind::SEQ_UNIT)
  {
    return Rational(1);
  }
  std::map<Node, ModelEqcInfo>::iterator it = d_minfo.find(r);
  Assert(it != d_minfo.end()) << "No model info for " << r;
  return it->second.d_length;
}

Node StringsMnf::getModelRepresentative(const Node& n)
{
  Node r = d_state.getRepresentative(n);
  std::map<Node, Node>::iterator it = d_mrepMap.find(r);
  if (it != d_mrepMap.end())
  {
    // union find
    std::vector<Node> eqc;
    std::map<Node, Node>::iterator itnext = it;
    do
    {
      it = itnext;
      itnext = d_mrepMap.find(it->second);
      if (itnext != d_mrepMap.end())
      {
        eqc.push_back(it->second);
      }
    } while (itnext != d_mrepMap.end());
    for (const Node& e : eqc)
    {
      d_mrepMap[e] = it->second;
    }
    return it->second;
  }
  return r;
}

void StringsMnf::merge(const Node& a, const Node& b)
{
  Trace("strings-mnf") << "...merge " << b << ": " << a << std::endl;
  // should not merge constant
  Assert(!b.isConst());
  Assert(a == getModelRepresentative(a));
  Assert(b == getModelRepresentative(b));
  d_mrepMap[b] = a;
  // don't need the normal form info for b anymore?
  d_minfo.erase(b);
  // replace b with a in all current normal forms
  std::vector<Node> vec{a};
  expandNormalForms(b, vec);
}

std::vector<Node> StringsMnf::split(const Node& a,
                                    const Rational& alen,
                                    const Rational& pos)
{
  Assert(alen > pos);
  Assert(pos.sgn() == 1);
  std::vector<Node> vec;
  if (a.isConst())
  {
    // split concretely
    // since pos is less than alen which is the length of the constant, which
    // should be less than the maximum model length (or 65536).
    Assert(pos < d_maxModelLen);
    Assert(alen < d_maxModelLen);
    std::size_t pvalue = pos.getNumerator().toUnsignedInt();
    std::size_t alvalue = alen.getNumerator().toUnsignedInt();
    vec.push_back(Word::prefix(a, pvalue));
    vec.push_back(Word::suffix(a, alvalue - pvalue));
  }
  else
  {
    // split based on skolems, these are dummy since there is no need to cache
    // them
    TypeNode atn = a.getType();
    SkolemManager* sm = NodeManager::currentNM()->getSkolemManager();
    vec.push_back(sm->mkDummySkolem("m", atn));
    vec.push_back(sm->mkDummySkolem("m", atn));
  }
  // Allocate new equivalence class infos. Note that in rare cases we may
  // split a word into components where one of those components is already
  // a representative. In this case, we don't
  Assert(vec.size() == 2);
  Trace("strings-mnf") << "...split " << a << ": " << vec << std::endl;
  for (size_t i = 0; i < 2; i++)
  {
    const Rational& len = i == 0 ? pos : alen - pos;
    ensureModelInfo(vec[i], len);
  }
  // expand a in all current normal forms
  expandNormalForms(a, vec);
  return vec;
}

void StringsMnf::expandNormalForms(const Node& n, const std::vector<Node>& nn)
{
  // TODO: could do uselists
  for (std::pair<const Node, ModelEqcInfo>& m : d_minfo)
  {
    m.second.expand(n, nn);
  }
}

void StringsMnf::ensureModelInfo(const Node& n, const Rational& len)
{
  std::map<Node, ModelEqcInfo>::iterator it = d_minfo.find(n);
  if (it == d_minfo.end())
  {
    // allocate, where the length depends on alen / pos
    ModelEqcInfo& meic = d_minfo[n];
    meic.d_mnf.push_back(n);
    meic.d_length = len;
    Trace("strings-mnf") << "NF " << n << " (alloc): " << meic.toString()
                         << std::endl;
  }
}

}  // namespace strings
}  // namespace theory
}  // namespace cvc5::internal
