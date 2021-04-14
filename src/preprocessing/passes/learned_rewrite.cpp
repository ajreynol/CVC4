/*********************                                                        */
/*! \file learned_rewrite.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Caleb Donovick
 ** This file is part of the CVC5 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Rewriting based on learned literals
 **/

#include "preprocessing/passes/learned_rewrite.h"

#include "expr/skolem_manager.h"
#include "expr/term_context_stack.h"
#include "preprocessing/assertion_pipeline.h"
#include "theory/arith/arith_msum.h"
#include "theory/rewriter.h"

using namespace cvc5::theory;
using namespace cvc5::kind;

namespace cvc5 {
namespace preprocessing {
namespace passes {

LearnedRewrite::LearnedRewrite(PreprocessingPassContext* preprocContext)
    : PreprocessingPass(preprocContext, "learned-rewrite")
{
}

PreprocessingPassResult LearnedRewrite::applyInternal(
    AssertionPipeline* assertionsToPreprocess)
{
  arith::BoundInference binfer;
  std::vector<Node>& learnedLits = d_preprocContext->getLearnedLiterals();
  std::vector<Node> llrw;
  if (learnedLits.empty())
  {
    Trace("learned-rewrite-ll") << "No learned literals" << std::endl;
  }
  else
  {
    Trace("learned-rewrite-ll") << "Learned literals:" << std::endl;
    for (const Node& l : learnedLits)
    {
      Node e = rewriteLearnedRec(l, binfer);
      // maybe for bound inference?
      Kind k = e.getKind();
      if (k == EQUAL || k == GEQ)
      {
        binfer.add(e);
        llrw.push_back(e);
      }
      Trace("learned-rewrite-ll") << "- " << e << std::endl;
    }
    Trace("learned-rewrite-ll") << "end" << std::endl;
  }
  size_t size = assertionsToPreprocess->size();
  for (size_t i = 0; i < size; ++i)
  {
    Node prev = (*assertionsToPreprocess)[i];
    Trace("learned-rewrite-assert")
        << "LearnedRewrite: assert: " << prev << std::endl;
    Node e = rewriteLearnedRec(prev, binfer);
    if (e != prev)
    {
      Trace("learned-rewrite-assert")
          << ".......................: " << e << std::endl;
      assertionsToPreprocess->replace(i, e);
    }
  }
  // add the conjunction of learned literals back to assertions
  if (!llrw.empty())
  {
    NodeManager* nm = NodeManager::currentNM();
    Node llc = nm->mkAnd(llrw);
    Trace("learned-rewrite-assert") << "Re-add rewritten learned conjunction: " << llc << std::endl;
    assertionsToPreprocess->push_back(llc);
  }

  return PreprocessingPassResult::NO_CONFLICT;
}

Node LearnedRewrite::rewriteLearnedRec(Node n, arith::BoundInference& binfer)
{
  NodeManager* nm = NodeManager::currentNM();
  std::unordered_map<TNode, Node, TNodeHashFunction> visited;
  std::unordered_map<TNode, Node, TNodeHashFunction>::iterator it;
  std::vector<TNode> visit;
  TNode cur;
  visit.push_back(n);
  do
  {
    cur = visit.back();
    visit.pop_back();
    it = visited.find(cur);

    if (it == visited.end())
    {
      visited[cur] = Node::null();
      visit.push_back(cur);
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
    else if (it->second.isNull())
    {
      Node ret = cur;
      bool needsRcons = false;
      std::vector<Node> children;
      if (cur.getMetaKind() == kind::metakind::PARAMETERIZED)
      {
        children.push_back(cur.getOperator());
      }
      for (const Node& cn : cur)
      {
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        needsRcons = needsRcons || cn != it->second;
        children.push_back(it->second);
      }
      if (needsRcons)
      {
        ret = nm->mkNode(cur.getKind(), children);
      }
      // rewrite here
      ret = rewriteLearned(ret, binfer);
      visited[cur] = ret;
    }
  } while (!visit.empty());
  Assert(visited.find(n) != visited.end());
  Assert(!visited.find(n)->second.isNull());
  return visited[n];
}

Node LearnedRewrite::rewriteLearned(Node n, arith::BoundInference& binfer)
{
  NodeManager* nm = NodeManager::currentNM();
  Trace("learned-rewrite-rr-debug") << "Rewrite " << n << std::endl;
  Node nr = Rewriter::rewrite(n);
  Kind k = nr.getKind();
  if (k == INTS_DIVISION || k == INTS_MODULUS || k == DIVISION)
  {
    // simpler if we know the divisor is non-zero
    Node num = n[0];
    Node den = n[1];
    bool isNonZeroDen = false;
    if (den.isConst())
    {
      isNonZeroDen = (den.getConst<Rational>().sgn() != 0);
    }
    else
    {
      arith::Bounds db = binfer.get(den);
      Trace("learned-rewrite-rr-debug")
          << "Bounds for " << den << " : " << db.lower_value << " "
          << db.upper_value << std::endl;
      if (!db.lower_value.isNull()
          && db.lower_value.getConst<Rational>().sgn() == 1)
      {
        isNonZeroDen = true;
      }
      else if (!db.upper_value.isNull()
               && db.upper_value.getConst<Rational>().sgn() == -1)
      {
        isNonZeroDen = true;
      }
    }
    if (isNonZeroDen)
    {
      Trace("learned-rewrite-rr-debug")
          << "...non-zero denominator" << std::endl;
      Kind nk = k;
      switch (k)
      {
        case INTS_DIVISION: nk = INTS_DIVISION_TOTAL; break;
        case INTS_MODULUS: nk = INTS_MODULUS_TOTAL; break;
        case DIVISION: nk = DIVISION_TOTAL; break;
        default: Assert(false); break;
      }
      std::vector<Node> children;
      children.insert(children.end(), n.begin(), n.end());
      Node ret = nm->mkNode(nk, children);
      nr = returnRewriteLearned(nr, ret, "non_zero_den");
      nr = Rewriter::rewrite(nr);
      k = nr.getKind();
    }
  }
  // constant int mod elimination by bound inference
  if (k == INTS_MODULUS_TOTAL)
  {
    Node num = n[0];
    Node den = n[1];
    arith::Bounds db = binfer.get(den);
    if ((!db.lower_value.isNull()
         && db.lower_value.getConst<Rational>().sgn() == 1)
        || (!db.upper_value.isNull()
            && db.upper_value.getConst<Rational>().sgn() == -1))
    {
      Rational bden = db.lower_value.isNull()
                          ? db.lower_value.getConst<Rational>()
                          : db.upper_value.getConst<Rational>().abs();
      // if 0 <= UB(num) < LB(den) or 0 <= UB(num) < -UB(den)
      arith::Bounds nb = binfer.get(num);
      if (!nb.upper_value.isNull())
      {
        Rational bnum = nb.upper_value.getConst<Rational>();
        if (bnum.sgn() != -1 && bnum < bden)
        {
          nr = returnRewriteLearned(nr, nr[0], "int_mod_range");
        }
      }
      // could also do num + k*den checks
    }
  }
  else if (k == GEQ || k == EQUAL)
  {
    std::map<Node, Node> msum;
    if (ArithMSum::getMonomialSumLit(nr, msum))
    {
      Rational lb(0);
      Rational ub(0);
      bool lbSuccess = true;
      bool ubSuccess = true;
      Rational one(1);
      for (const std::pair<const Node, Node>& m : msum)
      {
        bool isOneCoeff = m.second.isNull();
        Assert(isOneCoeff || m.second.isConst());
        if (m.first.isNull())
        {
          lb = lb + (isOneCoeff ? one : m.second.getConst<Rational>());
          ub = ub + (isOneCoeff ? one : m.second.getConst<Rational>());
        }
        else
        {
          arith::Bounds b = binfer.get(m.first);
          bool isNeg = !isOneCoeff && m.second.getConst<Rational>().sgn() == -1;
          // flip lower/upper if negative coefficient
          TNode l = isNeg ? b.upper_value : b.lower_value;
          TNode u = isNeg ? b.lower_value : b.upper_value;
          if (lbSuccess && !l.isNull())
          {
            Rational lc = l.getConst<Rational>();
            lb = lb + (isOneCoeff ? lc : Rational(lc * m.second.getConst<Rational>()));
          }
          else
          {
            lbSuccess = false;
          }
          if (ubSuccess && !u.isNull())
          {
            Rational uc = u.getConst<Rational>();
            ub = ub + (isOneCoeff ? uc : Rational(uc * m.second.getConst<Rational>()));
          }
          else
          {
            ubSuccess = false;
          }
          if (!lbSuccess && !ubSuccess)
          {
            break;
          }
        }
      }
      if (lbSuccess)
      {
        if (lb.sgn() == 1)
        {
          // if positive lower bound, then GEQ is true, EQUAL is false
          Node ret = nm->mkConst(k == GEQ);
          nr = returnRewriteLearned(nr, ret, "pred_pos_lb");
        }
        else if (lb.sgn() == 0 && k == GEQ)
        {
          // zero lower bound, GEQ is true
          Node ret = nm->mkConst(true);
          nr = returnRewriteLearned(nr, ret, "pred_zero_lb");
        }
      }
      else if (ubSuccess)
      {
        if (ub.sgn() == -1)
        {
          // if negative upper bound, then GEQ and EQUAL are false
          Node ret = nm->mkConst(false);
          nr = returnRewriteLearned(nr, ret, "pred_neg_ub");
        }
      }
    }
  }
  return nr;
}

Node LearnedRewrite::returnRewriteLearned(Node n, Node nr, const char* c)
{
  if (Trace.isOn("learned-rewrite-rr"))
  {
    Trace("learned-rewrite-rr") << "LearnedRewrite::Rewrite: (" << c << ") "
                                << n << " == " << nr << std::endl;
  }
  return nr;
}

}  // namespace passes
}  // namespace preprocessing
}  // namespace cvc5
