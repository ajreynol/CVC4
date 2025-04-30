/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Mathias Preiner, Aina Niemetz
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * N-ary term utilities
 */

#include "expr/nary_term_util.h"

#include "expr/aci_norm.h"
#include "expr/attribute.h"
#include "expr/emptyset.h"
#include "expr/node_algorithm.h"
#include "expr/sort_to_term.h"
#include "theory/bv/theory_bv_utils.h"
#include "theory/strings/word.h"
#include "util/bitvector.h"
#include "util/finite_field_value.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {
namespace expr {

struct IsListTag
{
};
using IsListAttr = expr::Attribute<IsListTag, bool>;

struct IsMatchListTag
{
};
using IsMatchListAttr = expr::Attribute<IsMatchListTag, bool>;

void markListVar(TNode fv, bool isMatchOnly)
{
  Assert(fv.isVar());
  if (isMatchOnly)
  {
    fv.setAttribute(IsMatchListAttr(), true);
  }
  else
  {
    fv.setAttribute(IsMatchListAttr(), true);
    fv.setAttribute(IsListAttr(), true);
  }
}

bool isListVar(TNode fv, bool isMatch)
{
  return isMatch ? fv.getAttribute(IsMatchListAttr())
                 : fv.getAttribute(IsListAttr());
}

bool hasListVar(TNode n, bool isMatch)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
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
      visited.insert(cur);
      if (isListVar(cur, isMatch))
      {
        return true;
      }
      visit.insert(visit.end(), cur.begin(), cur.end());
    }
  } while (!visit.empty());
  return false;
}

bool getListVarContext(TNode n, std::map<Node, Node>& context)
{
  std::unordered_set<TNode> visited;
  std::unordered_set<TNode>::iterator it;
  std::map<Node, Node>::iterator itc;
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
      visited.insert(cur);
      if (isListVar(cur, true))
      {
        // top-level list variable, undefined
        return false;
      }
      for (const Node& cn : cur)
      {
        if (isListVar(cn, true))
        {
          itc = context.find(cn);
          if (itc == context.end())
          {
            if (!NodeManager::isNAryKind(cur.getKind()))
            {
              return false;
            }
            context[cn] = cur;
          }
          else if (itc->second.getKind() != cur.getKind())
          {
            return false;
          }
          continue;
        }
        visit.push_back(cn);
      }
    }
  } while (!visit.empty());
  return true;
}

Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs)
{
  std::unordered_map<TNode, Node> visited;
  std::unordered_set<Node> noListVars;
  return narySubstitute(src, vars, subs, visited, noListVars);
}

Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs,
                    const std::unordered_set<Node>& noListVars)
{
  std::unordered_map<TNode, Node> visited;
  return narySubstitute(src, vars, subs, visited, noListVars);
}

Node narySubstitute(Node src,
                    const std::vector<Node>& vars,
                    const std::vector<Node>& subs,
                    std::unordered_map<TNode, Node>& visited,
                    const std::unordered_set<Node>& noListVars)
{
  // assumes all variables are list variables
  NodeManager* nm = src.getNodeManager();
  std::unordered_map<TNode, Node>::iterator it;
  std::vector<TNode> visit;
  std::vector<Node>::const_iterator itv;
  TNode cur;
  visit.push_back(src);
  do
  {
    cur = visit.back();
    it = visited.find(cur);
    if (it == visited.end())
    {
      if (!expr::hasBoundVar(cur))
      {
        visited[cur] = cur;
        visit.pop_back();
        continue;
      }
      // if it is a non-list variable, do the replacement
      itv = std::find(vars.begin(), vars.end(), cur);
      if (itv != vars.end())
      {
        size_t d = std::distance(vars.begin(), itv);
        if (!isListVar(vars[d]))
        {
          visited[cur] = subs[d];
          continue;
        }
      }
      visited[cur] = Node::null();
      visit.insert(visit.end(), cur.begin(), cur.end());
      continue;
    }
    visit.pop_back();
    if (it->second.isNull())
    {
      Node ret = cur;
      bool childChanged = false;
      bool hasNullChild = false;
      std::vector<Node> children;
      for (const Node& cn : cur)
      {
        // if it is a list variable, insert the corresponding list as children;
        itv = std::find(vars.begin(), vars.end(), cn);
        if (itv != vars.end())
        {
          childChanged = true;
          size_t d = std::distance(vars.begin(), itv);
          Assert(d < subs.size());
          Node sd = subs[d];
          if (isListVar(vars[d]) && noListVars.find(vars[d])==noListVars.end())
          {
            Assert(sd.getKind() == Kind::SEXPR);
            // add its children
            children.insert(children.end(), sd.begin(), sd.end());
          }
          else if (sd.getKind() == Kind::SEXPR)
          {
            AlwaysAssert (isListVar(vars[d]));
            // A list variable that we are treating as a non list variable
            // We either must construct the null terminator, take the single
            // child, or construct a nested expression of the same kind/type.
            // Note it may have been the case that sd is not an SEXPR, in which
            // case the caller of this method has already done this conversion.
            if (sd.getNumChildren() == 0)
            {
              hasNullChild = true;
              // we don't know the type to use for the null terminator yet, wait to do this below
              children.push_back(Node::null());
            }
            else if (sd.getNumChildren()==1)
            {
              children.push_back(sd[0]);
            }
            else
            {
              std::vector<Node> gchildren(sd.begin(), sd.end());
              Node g = nm->mkNode(cur.getKind(), gchildren);
              children.push_back(g);
            }
          }
          else
          {
            children.push_back(sd);
          }
          continue;
        }
        it = visited.find(cn);
        Assert(it != visited.end());
        Assert(!it->second.isNull());
        childChanged = childChanged || cn != it->second;
        children.push_back(it->second);
      }
      if (childChanged)
      {
        if (hasNullChild)
        {
          Node nt = getNullTerminator(nm, cur.getKind(), cur.getType());
          if (nt.isNull())
          {
            // If the null terminator above cannot be determine, it is dependent
            // on the return type (where the type of cur is an abstract type).
            // We get the type of a sibling, which should have the same type.
            // (This is not the case for bv concat, but its null terminator
            // is not dependent on the type and hence will not reach this
            // block of code).
            for (const Node& c : children)
            {
              if (!c.isNull())
              {
                nt = getNullTerminator(nm, cur.getKind(), c.getType());
                break;
              }
            }
          }
          // failed to find null terminator, should never happen
          if (nt.isNull())
          {
            Assert(false) << "Failed to find null terminator";
            return nt;
          }
          // go back and replace null placeholders with the null terminator
          // computed above.
          for (Node& c : children)
          {
            if (c.isNull())
            {
              c = nt;
            }
          }
        }
        if (children.size() != cur.getNumChildren())
        {
          // n-ary operators cannot be parameterized
          Assert(cur.getMetaKind() != metakind::PARAMETERIZED);
          if (children.empty())
          {
            ret = getNullTerminator(nm, cur.getKind(), cur.getType());
            // if we don't know the null terminator, just return null now
            if (ret.isNull())
            {
              return ret;
            }
          }
          else
          {
            // Assertion fails if we are doing singleton elimination after
            // using :match-list variables. This will fail if a RARE
            // rule depends on implicit singleton elimination, i.e. we
            // are using match-list but there still exists a term with fewer
            // than 2 :list variables.
            Assert (children.size()>1 || noListVars.empty());
            // implicit singleton elimination happens here
            ret = (children.size() == 1 ? children[0]
                                        : nm->mkNode(cur.getKind(), children));
          }
        }
        else
        {
          if (cur.getMetaKind() == metakind::PARAMETERIZED)
          {
            children.insert(children.begin(), cur.getOperator());
          }
          Kind k = cur.getKind();
          // We treat @set.empty_of_type, @seq.empty_of_type, @type_of as
          // macros in this method, meaning they are immediately evaluated
          // as soon as RARE rules are instantiated.
          switch (k)
          {
            case Kind::SET_EMPTY_OF_TYPE:
            case Kind::SEQ_EMPTY_OF_TYPE:
            {
              if (children[0].getKind() == Kind::SORT_TO_TERM)
              {
                const SortToTerm& st = children[0].getConst<SortToTerm>();
                TypeNode tn = st.getType();
                if (k == Kind::SET_EMPTY_OF_TYPE)
                {
                  ret = nm->mkConst(EmptySet(tn));
                }
                else
                {
                  Assert(k == Kind::SEQ_EMPTY_OF_TYPE);
                  ret = theory::strings::Word::mkEmptyWord(tn);
                }
              }
              else
              {
                ret = nm->mkNode(k, children);
              }
            }
            break;
            case Kind::TYPE_OF:
              ret = nm->mkConst(SortToTerm(children[0].getType()));
              break;
            default: ret = nm->mkNode(k, children); break;
          }
        }
      }
      visited[cur] = ret;
    }

  } while (!visit.empty());
  Assert(visited.find(src) != visited.end());
  Assert(!visited.find(src)->second.isNull());
  return visited[src];
}

}  // namespace expr
}  // namespace cvc5::internal
