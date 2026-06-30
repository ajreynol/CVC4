/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of the justification SAT decision strategy
 */

#include "decision/justification_strategy.h"

#include "expr/node_algorithm.h"
#include "options/main_options.h"
#include "prop/skolem_def_manager.h"

using namespace cvc5::internal::kind;
using namespace cvc5::internal::prop;

namespace cvc5::internal {
namespace decision {

JustificationStrategy::JustificationStrategy(Env& env,
                                             prop::CDCLTSatSolver* ss,
                                             prop::CnfStream* cs)
    : DecisionEngine(env, ss, cs),
      d_assertions(
          userContext(),
          context(),
          options().decision.jhRlvOrder,
          options()
              .decision.jhRandom),  // assertions are user-context dependent
      d_localAssertions(
          context(),
          context(),
          false,
          options()
              .decision.jhRandom),  // local assertions are SAT-context dependent
      d_jcache(context(), ss, cs),
      d_stack(context()),
      d_lastDecisionLit(context()),
      d_currStatusDec(false),
      d_useRlvOrder(options().decision.jhRlvOrder),
      d_decisionStopOnly(options().decision.decisionMode
                         == options::DecisionMode::STOPONLY),
      d_jhRandom(options().decision.jhRandom),
      d_seed(options().driver.seed),
      d_jhSkMode(options().decision.jhSkolemMode),
      d_jhSkRlvMode(options().decision.jhSkolemRlvMode),
      d_stats(statisticsRegistry())
{
}

void JustificationStrategy::presolve()
{
  d_lastDecisionLit = Node::null();
  d_currUnderStatus = Node::null();
  d_currStatusDec = false;
  // reset the dynamic assertion list data
  d_assertions.presolve();
  d_localAssertions.presolve();
  // clear the stack
  d_stack.clear();
}

SatLiteral JustificationStrategy::getNextInternal(bool& stopSearch)
{
  CodeTimer codeTimer(d_stats.d_time);
  // ensure we have an assertion
  if (!refreshCurrentAssertion())
  {
    Trace("jh-process") << "getNext, already finished" << std::endl;
    stopSearch = true;
    return undefSatLiteral;
  }
  Assert(d_stack.hasCurrentAssertion());
  // temporary information in the loop below
  JustifyInfo* ji;
  JustifyNode next;
  // we start with the value implied by the last decision, if it exists
  SatValue lastChildVal = SAT_VALUE_UNKNOWN;
  Trace("jh-process") << "getNext" << std::endl;
  // If we had just sent a decision, then we lookup its value here. This may
  // correspond to a context where the decision was carried out, or
  // alternatively it may correspond to a case where we have backtracked and
  // propagated that literal with opposite polarity. Thus, we do not assume we
  // know the value of d_lastDecisionLit and look it up again here. The value
  // of lastChildVal will be used to update the justify info in the current
  // stack below.
  if (!d_lastDecisionLit.get().isNull())
  {
    Trace("jh-process") << "last decision = " << d_lastDecisionLit.get()
                        << std::endl;
    lastChildVal = d_jcache.lookupValue(d_lastDecisionLit.get());
    if (lastChildVal == SAT_VALUE_UNKNOWN)
    {
      // if the value is now unknown, we must reprocess the assertion, since
      // we have backtracked
      TNode curr = d_stack.getCurrentAssertion();
      d_stack.clear();
      d_stack.reset(curr);
    }
  }
  d_lastDecisionLit = TNode::null();
  // while we are trying to satisfy assertions
  do
  {
    Assert(d_stack.getCurrent() != nullptr);
    // We get the next justify node, if it can be found.
    do
    {
      // get the current justify info, which should be ready
      ji = d_stack.getCurrent();
      if (ji == nullptr)
      {
        break;
      }
      // get the next child to process from the current justification info
      // based on the fact that its last child processed had value lastChildVal.
      next = getNextJustifyNode(ji, lastChildVal);
      // if the current node is finished, we pop the stack
      if (next.first.isNull())
      {
        d_stack.popStack();
      }
    } while (next.first.isNull());

    if (ji == nullptr)
    {
      // the assertion we just processed should have value true
      Assert(lastChildVal == SAT_VALUE_TRUE);
      if (!d_currUnderStatus.isNull())
      {
        // notify status if we are watching it
        DecisionStatus ds;
        if (d_currStatusDec)
        {
          ds = DecisionStatus::DECISION;
          ++(d_stats.d_numStatusDecision);
        }
        else
        {
          ds = DecisionStatus::NO_DECISION;
          ++(d_stats.d_numStatusNoDecision);
        }
        d_assertions.notifyStatus(d_currUnderStatus, ds);
      }
      // we did not find a next node for current, refresh current assertion
      d_stack.clear();
      refreshCurrentAssertion();
      lastChildVal = SAT_VALUE_UNKNOWN;
      Trace("jh-process") << "...exhausted assertion, now "
                          << d_stack.getCurrentAssertion() << std::endl;
    }
    else
    {
      // must have requested a next child to justify
      Assert(!next.first.isNull());
      Assert(next.second != SAT_VALUE_UNKNOWN);
      // Look up whether the next child already has a value
      lastChildVal = d_jcache.lookupValue(next.first);
      if (lastChildVal == SAT_VALUE_UNKNOWN)
      {
        bool nextPol = next.first.getKind() != Kind::NOT;
        TNode nextAtom = nextPol ? next.first : next.first[0];
        if (expr::isTheoryAtom(nextAtom))
        {
          // should be assigned a literal
          Assert(d_cnfStream->hasLiteral(nextAtom));
          // get the SAT literal
          SatLiteral nsl = d_cnfStream->getLiteral(nextAtom);
          // flip if the atom was negated
          // store the last decision value here, which will be used at the
          // starting value on the next call to this method
          lastChildVal = nextPol ? next.second : invertValue(next.second);
          // (1) atom with unassigned value, return it as the decision, possibly
          // inverted
          Trace("jh-process")
              << "...return " << nextAtom << " " << lastChildVal << std::endl;
          // Note that the last child of the current node we looked at does
          // *not* yet have a value. Although we are returning it as a decision,
          // we cannot set its value in d_jcache, because we have yet to
          // push a decision level. Thus, we remember the literal we decided
          // on. The value of d_lastDecisionLit will be processed at the
          // beginning of the next call to getNext above.
          d_lastDecisionLit = next.first;
          // record that we made a decision
          d_currStatusDec = true;
          if (d_decisionStopOnly)
          {
            // only doing stop-only, return undefSatLiteral.
            return undefSatLiteral;
          }
          return lastChildVal == SAT_VALUE_FALSE ? ~nsl : nsl;
        }
        else
        {
          // NOTE: it may be the case that we have yet to justify this node,
          // as indicated by the return of d_jcache.lookupValue. We may have a
          // value assigned to next.first by the SAT solver, but we ignore it
          // here.
          // (2) unprocessed non-atom, push to the stack
          d_stack.pushToStack(next.first, next.second);
          d_stats.d_maxStackSize.maxAssign(d_stack.size());
          // we have yet to process children for the next node, so lastChildVal
          // remains set to SAT_VALUE_UNKNOWN.
        }
      }
      else
      {
        Trace("jh-debug") << "in main loop, " << next.first << " has value "
                          << lastChildVal << std::endl;
      }
      // (3) otherwise, next already has a value lastChildVal which will be
      // processed in the next iteration of the loop.
    }
  } while (d_stack.hasCurrentAssertion());
  // we exhausted all assertions
  Trace("jh-process") << "...exhausted all assertions" << std::endl;
  stopSearch = true;
  return undefSatLiteral;
}

JustifyNode JustificationStrategy::getNextJustifyNode(
    JustifyInfo* ji, prop::SatValue& lastChildVal)
{
  // get the node we are trying to justify and its desired value
  JustifyNode jc = ji->getNode();
  Assert(!jc.first.isNull());
  Assert(jc.second != SAT_VALUE_UNKNOWN);
  // extract the non-negated formula we are trying to justify
  bool currPol = jc.first.getKind() != Kind::NOT;
  TNode curr = currPol ? jc.first : jc.first[0];
  Kind ck = curr.getKind();
  // the current node should be a non-theory literal and not have double
  // negation, due to our invariants of what is pushed onto the stack
  Assert(!expr::isTheoryAtom(curr));
  Assert(ck != Kind::NOT);
  // get the next child index to process
  size_t i = ji->getNextChildIndex();
  // For the randomized heuristic, when processing a symmetric connective
  // (AND/OR), explore its children in a random order. The children of other
  // connectives have positional meaning, so their order is left unchanged.
  // Note i is the logical child index that drives the control flow below; the
  // actual child position is obtained via ji->mapChildIndex(i) when accessing
  // curr. The permutation is keyed deterministically on the node (via its
  // seed), so it is stable across backtracking even though it is stored in a
  // context-independent member that may be overwritten when the justify info
  // is reused for another node.
  if (d_jhRandom && (ck == Kind::AND || ck == Kind::OR))
  {
    ji->ensureChildPermutation(curr.getNumChildren(), nodeSeed(curr));
  }
  Trace("jh-debug") << "getNextJustifyNode " << curr << " / " << currPol
                    << ", index = " << i
                    << ", last child value = " << lastChildVal << std::endl;
  // NOTE: if i>0, we just computed the value of the (i-1)^th child
  // i.e. i == 0 || lastChildVal != SAT_VALUE_UNKNOWN,
  // however this does not hold when backtracking has occurred.
  // if i=0, we shouldn't have a last child value
  Assert(i > 0 || lastChildVal == SAT_VALUE_UNKNOWN)
      << "in getNextJustifyNode, value given for non-existent last child";
  // we are trying to make the value of curr equal to currDesiredVal
  SatValue currDesiredVal = currPol ? jc.second : invertValue(jc.second);
  // value is set to TRUE/FALSE if the value of curr can be determined.
  SatValue value = SAT_VALUE_UNKNOWN;
  // if we require processing the next child of curr, we set desiredVal to
  // value which we want that child to be to make curr's value equal to
  // currDesiredVal.
  SatValue desiredVal = SAT_VALUE_UNKNOWN;
  if (ck == Kind::AND || ck == Kind::OR)
  {
    if (i == 0)
    {
      // See if a single child with currDesiredVal forces value, which is the
      // case if ck / currDesiredVal in { and / false, or / true }.
      if ((ck == Kind::AND) == (currDesiredVal == SAT_VALUE_FALSE))
      {
        // lookahead to determine if already satisfied
        // we scan only once, when processing the first child
        for (const Node& c : curr)
        {
          SatValue v = d_jcache.lookupValue(c);
          if (v == currDesiredVal)
          {
            Trace("jh-debug") << "already forcing child " << c << std::endl;
            value = currDesiredVal;
            break;
          }
          // NOTE: if v == SAT_VALUE_UNKNOWN, then we can add this to a watch
          // list and short circuit processing in the children of this node.
        }
      }
      desiredVal = currDesiredVal;
    }
    else if ((ck == Kind::AND && lastChildVal == SAT_VALUE_FALSE)
             || (ck == Kind::OR && lastChildVal == SAT_VALUE_TRUE)
             || i == curr.getNumChildren())
    {
      Trace("jh-debug") << "current is forcing child" << std::endl;
      // forcing or exhausted case
      value = lastChildVal;
    }
    else
    {
      // otherwise, no forced value, value of child should match the parent
      desiredVal = currDesiredVal;
    }
  }
  else if (ck == Kind::IMPLIES)
  {
    if (i == 0)
    {
      // lookahead to second child to determine if value already forced
      if (d_jcache.lookupValue(curr[1]) == SAT_VALUE_TRUE)
      {
        value = SAT_VALUE_TRUE;
      }
      else
      {
        // otherwise, we request the opposite of what parent wants
        desiredVal = invertValue(currDesiredVal);
      }
    }
    else if (i == 1)
    {
      // forcing case
      if (lastChildVal == SAT_VALUE_FALSE)
      {
        value = SAT_VALUE_TRUE;
      }
      else
      {
        desiredVal = currDesiredVal;
      }
    }
    else
    {
      // exhausted case
      value = lastChildVal;
    }
  }
  else if (ck == Kind::ITE)
  {
    if (i == 0)
    {
      // lookahead on branches
      SatValue val1 = d_jcache.lookupValue(curr[1]);
      SatValue val2 = d_jcache.lookupValue(curr[2]);
      if (val1 == val2)
      {
        // branches have no difference, value is that of branches, which may
        // be unknown
        value = val1;
      }
      // if first branch is already wrong or second branch is already correct,
      // try to make condition false. Note that if both children are unknown the
      // choice is arbitrary: we default to true, but randomize it when using
      // the randomized heuristic. If both children have the same value and that
      // value is not unknown, desiredVal will be ignored, since value is set
      // above.
      if (val1 == invertValue(currDesiredVal) || val2 == currDesiredVal)
      {
        desiredVal = SAT_VALUE_FALSE;
      }
      else if (d_jhRandom && val1 == SAT_VALUE_UNKNOWN
               && val2 == SAT_VALUE_UNKNOWN)
      {
        // The choice of condition polarity is arbitrary here (both branches
        // are unknown). Randomize it deterministically based on the node.
        desiredVal = randomChoice(curr, 0) ? SAT_VALUE_TRUE : SAT_VALUE_FALSE;
      }
      else
      {
        desiredVal = SAT_VALUE_TRUE;
      }
    }
    else if (i == 1)
    {
      Assert(lastChildVal != SAT_VALUE_UNKNOWN);
      // we just computed the value of the condition, check if the condition
      // was false
      if (lastChildVal == SAT_VALUE_FALSE)
      {
        // this increments to the else branch
        i = ji->getNextChildIndex();
      }
      // make the branch equal to the desired value
      desiredVal = currDesiredVal;
    }
    else
    {
      // return the branch value
      value = lastChildVal;
    }
  }
  else if (ck == Kind::XOR || ck == Kind::EQUAL)
  {
    Assert(curr[0].getType().isBoolean());
    if (i == 0)
    {
      // check if the rhs forces a value
      SatValue val1 = d_jcache.lookupValue(curr[1]);
      if (val1 == SAT_VALUE_UNKNOWN)
      {
        // not forced, the choice is arbitrary; choose true, or randomize it
        // deterministically based on the node when using the randomized
        // heuristic
        desiredVal = (d_jhRandom && !randomChoice(curr, 1)) ? SAT_VALUE_FALSE
                                                            : SAT_VALUE_TRUE;
      }
      else
      {
        // if the RHS of the XOR/EQUAL already had a value val1, then:
        // ck    / currDesiredVal
        // equal / true             ... LHS should have same value as RHS
        // equal / false            ... LHS should have opposite value as RHS
        // xor   / true             ... LHS should have opposite value as RHS
        // xor   / false            ... LHS should have same value as RHS
        desiredVal = ((ck == Kind::EQUAL) == (currDesiredVal == SAT_VALUE_TRUE))
                         ? val1
                         : invertValue(val1);
      }
    }
    else if (i == 1)
    {
      Assert(lastChildVal != SAT_VALUE_UNKNOWN);
      // same as above, choosing a value for RHS based on the value of LHS,
      // which is stored in lastChildVal.
      desiredVal = ((ck == Kind::EQUAL) == (currDesiredVal == SAT_VALUE_TRUE))
                       ? lastChildVal
                       : invertValue(lastChildVal);
    }
    else
    {
      // recompute the value of the first child
      SatValue val0 = d_jcache.lookupValue(curr[0]);
      Assert(val0 != SAT_VALUE_UNKNOWN);
      Assert(lastChildVal != SAT_VALUE_UNKNOWN);
      // compute the value of the equal/xor. The values for LHS/RHS are
      // stored in val0 and lastChildVal.
      // (val0 == lastChildVal) / ck
      // true                  / equal ... value of curr is true
      // true                  / xor   ... value of curr is false
      // false                 / equal ... value of curr is false
      // false                 / xor   ... value of curr is true
      value = ((val0 == lastChildVal) == (ck == Kind::EQUAL)) ? SAT_VALUE_TRUE
                                                              : SAT_VALUE_FALSE;
    }
  }
  else
  {
    // curr should not be an atom
    DebugUnhandled();
  }
  // we return null if we have determined the value of the current node
  if (value != SAT_VALUE_UNKNOWN)
  {
    Assert(!expr::isTheoryAtom(curr));
    // add to justify if so
    d_jcache.setValue(curr, value);
    // update the last child value, which will be used by the parent of the
    // current node, if it exists.
    lastChildVal = currPol ? value : invertValue(value);
    Trace("jh-debug") << "getJustifyNode: return null with value "
                      << lastChildVal << std::endl;
    // return null, indicating there is nothing left to do for current
    return JustifyNode(TNode::null(), SAT_VALUE_UNKNOWN);
  }
  // The next child should be a valid argument in curr. Otherwise, we did not
  // recognize when its value could be inferred above.
  Assert(i < curr.getNumChildren()) << curr.getKind() << " had no value";
  // Map the logical child index to the actual child position. This is the
  // identity unless we are randomizing the order of children of curr, which we
  // only do for symmetric connectives (AND/OR). We must not apply the
  // permutation for other connectives, both because their children have
  // positional meaning and because a stale permutation (which is not restored
  // on backtracking) may be present for this justify info.
  size_t childIndex =
      (d_jhRandom && (ck == Kind::AND || ck == Kind::OR)) ? ji->mapChildIndex(i)
                                                          : i;
  Trace("jh-debug") << "getJustifyNode: return " << curr[childIndex]
                    << " with desired value " << desiredVal << std::endl;
  // should set a desired value
  Assert(desiredVal != SAT_VALUE_UNKNOWN)
      << "Child " << i << " of " << curr.getKind() << " had no desired value";
  // return the justify node
  return JustifyNode(curr[childIndex], desiredVal);
}

bool JustificationStrategy::isDone() { return !refreshCurrentAssertion(); }

void JustificationStrategy::addAssertions(const std::vector<TNode>& lems)
{
  Trace("jh-assert") << "addAssertions " << lems << std::endl;
  insertToAssertionList(lems, false);
}

void JustificationStrategy::addLocalAssertions(const std::vector<TNode>& lems)
{
  Trace("jh-assert") << "addLocalAssertions: " << lems << std::endl;
  insertToAssertionList(lems, true);
}

void JustificationStrategy::insertToAssertionList(
    const std::vector<TNode>& lems, bool local)
{
  std::vector<TNode> toProcess(lems.begin(), lems.end());
  AssertionList& al = local ? d_localAssertions : d_assertions;
  IntStat& sizeStat =
      local ? d_stats.d_maxSkolemDefsSize : d_stats.d_maxAssertionsSize;
  // always miniscope AND and negated OR immediately
  size_t index = 0;
  // must keep some intermediate nodes below around for ref counting
  std::vector<Node> keep;
  while (index < toProcess.size())
  {
    TNode curr = toProcess[index];
    bool pol = curr.getKind() != Kind::NOT;
    TNode currAtom = pol ? curr : curr[0];
    index++;
    Kind k = currAtom.getKind();
    if (k == Kind::AND && pol)
    {
      toProcess.insert(toProcess.begin() + index, curr.begin(), curr.end());
    }
    else if (k == Kind::OR && !pol)
    {
      std::vector<Node> negc;
      for (TNode c : currAtom)
      {
        Node cneg = c.negate();
        negc.push_back(cneg);
        // ensure ref counted
        keep.push_back(cneg);
      }
      toProcess.insert(toProcess.begin() + index, negc.begin(), negc.end());
    }
    else if (!expr::isTheoryAtom(currAtom))
    {
      al.addAssertion(curr);
      // take stats
      sizeStat.maxAssign(al.size());
    }
    else
    {
      // we skip (top-level) theory literals, since these are always propagated
      // NOTE: skolem definitions that are always relevant should be added to
      // assertions, for uniformity via a method notifyJustified(currAtom)
    }
  }
  // clear since toProcess may contain nodes with 0 ref count after returning
  // otherwise
  toProcess.clear();
}

bool JustificationStrategy::refreshCurrentAssertion()
{
  Trace("jh-process") << "refreshCurrentAssertion" << std::endl;
  // if we already have a current assertion, nothing to be done
  TNode curr = d_stack.getCurrentAssertion();
  if (!curr.isNull())
  {
    if (curr != d_currUnderStatus && !d_currUnderStatus.isNull())
    {
      ++(d_stats.d_numStatusBacktrack);
      d_assertions.notifyStatus(d_currUnderStatus, DecisionStatus::BACKTRACK);
      // we've backtracked to another assertion which may be partially
      // processed. don't track its status?
      d_currUnderStatus = Node::null();
      // NOTE: could reset the stack here to preserve other invariants,
      // currently we do not.
    }
    return true;
  }
  bool skFirst = (d_jhSkMode != options::JutificationSkolemMode::LAST);
  // use main assertions first
  if (refreshCurrentAssertionFromList(skFirst))
  {
    return true;
  }
  // if satisfied all main assertions, use the skolem assertions, which may
  // fail
  return refreshCurrentAssertionFromList(!skFirst);
}

bool JustificationStrategy::refreshCurrentAssertionFromList(bool local)
{
  AssertionList& al = local ? d_localAssertions : d_assertions;
  bool doWatchStatus = !local;
  d_currUnderStatus = Node::null();
  TNode curr = al.getNextAssertion();
  SatValue currValue;
  while (!curr.isNull())
  {
    Trace("jh-process") << "Check assertion " << curr << std::endl;
    // we never add theory literals to our assertions lists
    Assert(!isTheoryLiteral(curr));
    currValue = d_jcache.lookupValue(curr);
    if (currValue == SAT_VALUE_UNKNOWN)
    {
      // if not already justified, we reset the stack and push to it
      d_stack.reset(curr);
      d_lastDecisionLit = TNode::null();
      // for activity
      if (doWatchStatus)
      {
        // initially, mark that we have not found a decision in this
        d_currUnderStatus = d_stack.getCurrentAssertion();
        d_currStatusDec = false;
      }
      return true;
    }
    // assertions should all be satisfied, otherwise we are in conflict
    Assert(currValue == SAT_VALUE_TRUE);
    if (doWatchStatus)
    {
      // mark that we did not find a decision in it
      ++(d_stats.d_numStatusNoDecision);
      d_assertions.notifyStatus(curr, DecisionStatus::NO_DECISION);
    }
    // already justified, immediately skip
    curr = al.getNextAssertion();
  }
  return false;
}

bool JustificationStrategy::isTheoryLiteral(TNode n)
{
  return expr::isTheoryAtom(n.getKind() == Kind::NOT ? n[0] : n);
}

uint64_t JustificationStrategy::nodeSeed(TNode n) const
{
  // mix the random seed with the node identifier (splitmix64-style finalizer)
  uint64_t x = d_seed + static_cast<uint64_t>(n.getId()) * 0x9e3779b97f4a7c15ULL;
  x = (x ^ (x >> 30)) * 0xbf58476d1ce4e5b9ULL;
  x = (x ^ (x >> 27)) * 0x94d049bb133111ebULL;
  x = x ^ (x >> 31);
  return x;
}

bool JustificationStrategy::randomChoice(TNode n, uint64_t salt) const
{
  // deterministic pseudo-random bit derived from the node's seed and salt
  uint64_t x = nodeSeed(n) ^ (salt * 0x9e3779b97f4a7c15ULL);
  x = (x ^ (x >> 33)) * 0xff51afd7ed558ccdULL;
  x = x ^ (x >> 33);
  return (x & 1u) != 0;
}

}  // namespace decision
}  // namespace cvc5::internal
