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

EagerTermIterator::EagerTermIterator(TNode t) : d_orig(t)
{
  Assert(t.getKind() != Kind::INST_PATTERN);
  d_stack.emplace_back(t, 0);
}

EagerTrie::EagerTrie() {}

EagerTrie* EagerTrie::add(TermDb* tdb, TNode n)
{
  std::vector<uint64_t> bound;
  EagerTermIterator eti(n);
  return addInternal(tdb, eti, bound, false);
}

void EagerTrie::erase(TermDb* tdb, TNode n)
{
  std::vector<uint64_t> bound;
  EagerTermIterator eti(n);
  addInternal(tdb, eti, bound, true);
}

EagerTrie* EagerTrie::addInternal(TermDb* tdb,
                                  EagerTermIterator& eti,
                                  std::vector<uint64_t>& bound,
                                  bool isErase)
{
  EagerTrie* ret;
  // add or remove the pattern, even if not at leaf
  if (isErase)
  {
    Assert(d_pats.back() == eti.getOriginal());
    d_pats.pop_back();
    ret = nullptr;
  }
  else
  {
    d_pats.push_back(eti.getOriginal());
    ret = this;
  }
  // we have another child to continue from a higher level
  while (eti.needsBacktrack())
  {
    if (!eti.pop())
    {
      return ret;
    }
  }
  TNode nc = eti.getCurrent();
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
        return nullptr;
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
        return nullptr;
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
      return nullptr;
    }
    eti.incrementChild();
    eti.push(nc);
    std::map<Node, EagerTrie>& etng = d_ngroundChildren;
    if (isErase)
    {
      std::map<Node, EagerTrie>::iterator it = etng.find(op);
      if (it == etng.end())
      {
        return nullptr;
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

  return ret;
}

bool EagerTrie::empty() const
{
  return d_varChildren.empty() && d_checkVarChildren.empty()
         && d_groundChildren.empty() && d_ngroundChildren.empty()
         && d_pats.empty();
}

CDEagerTrie::CDEagerTrie(context::Context* c) : d_pats(c) {}

EagerTrie* CDEagerTrie::addPattern(TermDb* tdb, TNode pat)
{
  Trace("eager-inst-pattern") << "add pat: " << pat << std::endl;
  makeCurrent(tdb);
  d_pats.push_back(pat);
  d_triePats.emplace_back(pat);
  return d_trie.add(tdb, pat);
}

EagerTrie* CDEagerTrie::getCurrent(TermDb* tdb)
{
  makeCurrent(tdb);
  return &d_trie;
}

void CDEagerTrie::makeCurrent(TermDb* tdb)
{
  size_t i = d_triePats.size();
  size_t tsize = d_pats.size();
  // clean up any stale patterns that appear in the trie
  while (i > tsize)
  {
    i--;
    Node pat = d_triePats[i];
    Trace("eager-inst-pattern") << "remove pat: " << pat << std::endl;
    d_trie.erase(tdb, pat);
  }
  d_triePats.resize(tsize);
}

}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
