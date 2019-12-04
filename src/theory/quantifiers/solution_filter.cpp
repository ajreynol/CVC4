/*********************                                                        */
/*! \file solution_filter.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2019 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Utilities for filtering solutions.
 **/

#include "theory/quantifiers/solution_filter.h"

#include <fstream>
#include "options/quantifiers_options.h"
#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"
#include "util/random.h"

using namespace CVC4::kind;

namespace CVC4 {
namespace theory {
namespace quantifiers {

SolutionFilterStrength::SolutionFilterStrength() : d_isStrong(true) {}
void SolutionFilterStrength::initialize(const std::vector<Node>& vars,
                                        SygusSampler* ss)
{
  ExprMiner::initialize(vars, ss);
}

void SolutionFilterStrength::setLogicallyStrong(bool isStrong)
{
  d_isStrong = isStrong;
}

bool SolutionFilterStrength::addTerm(Node n, std::ostream& out)
{
  if (!n.getType().isBoolean())
  {
    // currently, should not register non-Boolean terms here
    Assert(false);
    return true;
  }
  Node basen = d_isStrong ? n : n.negate();
  NodeManager* nm = NodeManager::currentNM();
  // Do i subsume the disjunction of all previous solutions? If so, we discard
  // this immediately
  Node curr;
  if (!d_curr_sols.empty())
  {
    curr = d_curr_sols.size() == 1
               ? d_curr_sols[0]
               : nm->mkNode(d_isStrong ? OR : AND, d_curr_sols);
    Node imp = nm->mkNode(AND, basen.negate(), curr);
    Trace("sygus-sol-implied")
        << "  implies: check subsumed (strong=" << d_isStrong << ") " << imp
        << "..." << std::endl;
    // check the satisfiability query
    Result r = doCheck(imp);
    Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
    if (r.asSatisfiabilityResult().isSat() == Result::UNSAT)
    {
      // it is subsumed by the current, discard this
      return false;
    }
  }
  // check which solutions would have been filtered if the current had come
  // first
  if (options::sygusFilterSolRevSubsume())
  {
    std::vector<Node> nsubsume;
    for (const Node& s : d_curr_sols)
    {
      Node imp = nm->mkNode(AND, s.negate(), basen);
      Trace("sygus-sol-implied")
          << "  implies: check subsuming " << imp << "..." << std::endl;
      // check the satisfiability query
      Result r = doCheck(imp);
      Trace("sygus-sol-implied") << "  implies: ...got : " << r << std::endl;
      if (r.asSatisfiabilityResult().isSat() != Result::UNSAT)
      {
        nsubsume.push_back(s);
      }
      else
      {
        Options& nodeManagerOptions = nm->getOptions();
        std::ostream* out = nodeManagerOptions.getOut();
        (*out) << "; (filtered " << (d_isStrong ? s : s.negate()) << ")"
               << std::endl;
      }
    }
    d_curr_sols.clear();
    d_curr_sols.insert(d_curr_sols.end(), nsubsume.begin(), nsubsume.end());
  }
  d_curr_sols.push_back(basen);
  return true;
}

void SolutionFilterObjFun::setObjectiveFunction(const std::vector<Node>& vars,
                                                Node f)
{
  d_objFunVars = vars;
  d_objFun = f;
  // must be real valued
  AlwaysAssert(d_objFun.getType().isReal());
}

bool SolutionFilterObjFun::addTerm(Node n, std::ostream& out)
{
  Trace("sygus-filter-obj-fun-debug")
      << "Filter via objective function: " << n << std::endl;
  std::vector<Node> vals;
  vals.push_back(n);
  Node res = d_eval.eval(d_objFun, d_objFunVars, vals);
  if (res.isNull())
  {
    Trace("sygus-filter-obj-fun-debug") << "...must substitute" << std::endl;
    res = d_objFun.substitute(
        d_objFunVars.begin(), d_objFunVars.end(), vals.begin(), vals.end());
    res = Rewriter::rewrite(res);
  }
  Trace("sygus-filter-obj-fun")
      << "Value of objective function is " << res << std::endl;
  if (!res.isConst())
  {
    // not constant, must keep but don't set value
    Trace("sygus-filter-obj-fun") << "...keep (non-constant)" << std::endl;
    return true;
  }
  bool retValue = false;
  if (d_maxValue.isNull())
  {
    d_maxValue = res;
    retValue = true;
    Trace("sygus-filter-obj-fun") << "...keep (first)" << std::endl;
  }
  else if (res.getConst<Rational>() > d_maxValue.getConst<Rational>())
  {
    d_maxValue = res;
    retValue = true;
    Trace("sygus-filter-obj-fun") << "...keep (new max)" << std::endl;
  }
  if (retValue)
  {
    NodeManager* nm = NodeManager::currentNM();
    Options& nodeManagerOptions = nm->getOptions();
    std::ostream* out = nodeManagerOptions.getOut();
    (*out) << "; optimal value is now " << d_maxValue << std::endl;
  }
  return retValue;
}

Node SolutionFilterObjFun::getCurrentMaxValue() const { return d_maxValue; }

}  // namespace quantifiers
}  // namespace theory
}  // namespace CVC4
