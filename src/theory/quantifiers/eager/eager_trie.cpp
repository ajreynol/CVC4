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

#include "theory/quantifiers/eager/eager_trie.h"

#include "theory/quantifiers/term_database.h"
#include "theory/quantifiers/term_util.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {

bool EagerTrie::add(TermDb* tdb, const Node& n)
{
  std::vector<std::pair<Node, size_t>> ets;
  std::vector<uint64_t> bound;
  return addInternal(tdb, n, n, 0, ets, bound, false);
}

bool EagerTrie::erase(TermDb* tdb, const Node& n)
{
  std::vector<std::pair<Node, size_t>> ets;
  std::vector<uint64_t> bound;
  return addInternal(tdb, n, n, 0, ets, bound, true);
}

bool EagerTrie::addInternal(TermDb* tdb,
                            const Node& pat,
                            const Node& n,
                            size_t i,
                            std::vector<std::pair<Node, size_t>>& ets,
                            std::vector<uint64_t>& bound,
                            bool isErase)
{
  EagerTrie* et = this;
  bool ret;
  if (i == n.getNumChildren())
  {
    if (!ets.empty())
    {
      // we have another child to continue from a higher level
      std::pair<Node, size_t> p = ets.back();
      ets.pop_back();
      ret = addInternal(tdb, pat, p.first, p.second, ets, bound, isErase);
    }
    else
    {
      // we are at the leaf, we add or remove the pattern
      if (isErase)
      {
        AlwaysAssert(d_pats.back() == pat);
        d_pats.pop_back();
      }
      else
      {
        d_pats.push_back(pat);
      }
      ret = true;
    }
  }
  else
  {
    const Node& nc = n[i];
    if (nc.getKind() == Kind::INST_CONSTANT)
    {
      uint64_t vnum = TermUtil::getInstVarNum(nc);
      /*
      if (std::find(bound.begin(), bound.end(), vnum)
          != bound.end())
      {
        // TODO
      }
      bound.push_back(vnum);
      */
      std::map<uint64_t, EagerTrie>& etv = et->d_varChildren;
      if (isErase)
      {
        std::map<uint64_t, EagerTrie>::iterator it = etv.find(vnum);
        if (it == etv.end())
        {
          return false;
        }
        ret = it->second.addInternal(tdb, pat, n, i + 1, ets, bound, isErase);
        if (it->second.empty())
        {
          etv.erase(it);
        }
      }
      else
      {
        ret = etv[vnum].addInternal(tdb, pat, n, i + 1, ets, bound, isErase);
      }
    }
    else if (!TermUtil::hasInstConstAttr(nc))
    {
      std::map<Node, EagerTrie>& etg = et->d_groundChildren;
      if (isErase)
      {
        std::map<Node, EagerTrie>::iterator it = etg.find(nc);
        if (it == etg.end())
        {
          return false;
        }
        ret = it->second.addInternal(tdb, pat, n, i + 1, ets, bound, isErase);
        if (it->second.empty())
        {
          etg.erase(it);
        }
      }
      else
      {
        ret = etg[nc].addInternal(tdb, pat, n, i + 1, ets, bound, isErase);
      }
    }
    else
    {
      Node op = tdb->getMatchOperator(nc);
      if (op.isNull())
      {
        return false;
      }
      std::map<Node, EagerTrie>& etng = et->d_ngroundChildren;
      ets.emplace_back(n, i + 1);
      if (isErase)
      {
        std::map<Node, EagerTrie>::iterator it = etng.find(op);
        if (it == etng.end())
        {
          return false;
        }
        ret = it->second.addInternal(tdb, pat, nc, 0, ets, bound, isErase);
        if (it->second.empty())
        {
          etng.erase(it);
        }
      }
      else
      {
        ret = etng[op].addInternal(tdb, pat, nc, 0, ets, bound, isErase);
      }
    }
  }
  return ret;
}

bool EagerTrie::empty() const
{
  return d_varChildren.empty() && d_checkVarChildren.empty()
         && d_groundChildren.empty() && d_ngroundChildren.empty()
         && d_pats.empty();
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
