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

EagerTrie::EagerTrie() {}

bool EagerTrie::add(TermDb* tdb, const Node& n)
{
  std::vector<uint64_t> bound;
  // if n has kind INST_PATTERN, it is a filtering multi-trigger where the first
  // child is a single trigger
  Node t = n.getKind() == Kind::INST_PATTERN ? n[0] : n;
  EagerTermIterator eti(n, t);
  return addInternal(tdb, eti, bound, false);
}

bool EagerTrie::erase(TermDb* tdb, const Node& n)
{
  std::vector<uint64_t> bound;
  // if n has kind INST_PATTERN, it is a filtering multi-trigger where the first
  // child is a single trigger
  Node t = n.getKind() == Kind::INST_PATTERN ? n[0] : n;
  EagerTermIterator eti(n, t);
  return addInternal(tdb, eti, bound, true);
}

bool EagerTrie::addInternal(TermDb* tdb,
                            EagerTermIterator& eti,
                            std::vector<uint64_t>& bound,
                            bool isErase)
{
  // remember the pattern, even if being erased
  d_exPat = eti.getOriginal();
  bool ret;
  if (eti.needsBacktrack())
  {
    if (eti.pop())
    {
      // we have another child to continue from a higher level
      ret = addInternal(tdb, eti, bound, isErase);
    }
    else
    {
      const Node& pat = eti.getOriginal();
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
    const Node& nc = eti.getCurrent();
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
      eti.incrementChild();
      std::map<uint64_t, EagerTrie>& etv = d_varChildren;
      if (isErase)
      {
        std::map<uint64_t, EagerTrie>::iterator it = etv.find(vnum);
        if (it == etv.end())
        {
          return false;
        }
        ret = it->second.addInternal(tdb, eti, bound, isErase);
        if (it->second.empty())
        {
          etv.erase(it);
        }
      }
      else
      {
        ret = etv[vnum].addInternal(tdb, eti, bound, isErase);
      }
    }
    else if (!TermUtil::hasInstConstAttr(nc))
    {
      eti.incrementChild();
      std::map<Node, EagerTrie>& etg = d_groundChildren;
      if (isErase)
      {
        std::map<Node, EagerTrie>::iterator it = etg.find(nc);
        if (it == etg.end())
        {
          return false;
        }
        ret = it->second.addInternal(tdb, eti, bound, isErase);
        if (it->second.empty())
        {
          etg.erase(it);
        }
      }
      else
      {
        ret = etg[nc].addInternal(tdb, eti, bound, isErase);
      }
    }
    else
    {
      Node op = tdb->getMatchOperator(nc);
      if (op.isNull())
      {
        return false;
      }
      eti.incrementChild();
      eti.push(nc);
      std::map<Node, EagerTrie>& etng = d_ngroundChildren;
      if (isErase)
      {
        std::map<Node, EagerTrie>::iterator it = etng.find(op);
        if (it == etng.end())
        {
          return false;
        }
        ret = it->second.addInternal(tdb, eti, bound, isErase);
        if (it->second.empty())
        {
          etng.erase(it);
        }
      }
      else
      {
        ret = etng[op].addInternal(tdb, eti, bound, isErase);
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
