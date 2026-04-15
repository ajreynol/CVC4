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
 * Eager instantiation term database.
 */

#include "theory/quantifiers/eager/eager_term_database.h"

namespace cvc5::internal {
namespace theory {
namespace quantifiers {
namespace eager {

TermDatabase::TermDatabase(context::Context* c)
    : d_terms(c), d_opTerms(c), d_parentOps(c), d_context(c)
{
}

bool TermDatabase::addTerm(Node t, Node op)
{
  if (!d_terms.insert(t))
  {
    return false;
  }
  if (!op.isNull())
  {
    getOrMkList(d_opTerms, op)->d_list.push_back(t);
  }
  return true;
}

const NodeList* TermDatabase::getGroundTerms(Node op) const
{
  NodeListMap::const_iterator it = d_opTerms.find(op);
  if (it == d_opTerms.end())
  {
    return nullptr;
  }
  return it->second.get();
}

size_t TermDatabase::getNumGroundTerms(Node op) const
{
  const NodeList* gts = getGroundTerms(op);
  return gts == nullptr ? 0 : gts->d_list.size();
}

void TermDatabase::addParentOperator(Node t, Node op)
{
  NodeList* parents = getOrMkList(d_parentOps, t);
  for (const Node& parent : parents->d_list)
  {
    if (parent == op)
    {
      return;
    }
  }
  parents->d_list.push_back(op);
}

const NodeList* TermDatabase::getParentOperators(Node t) const
{
  NodeListMap::const_iterator it = d_parentOps.find(t);
  if (it == d_parentOps.end())
  {
    return nullptr;
  }
  return it->second.get();
}

NodeList* TermDatabase::getOrMkList(NodeListMap& map, Node key)
{
  NodeListMap::iterator it = map.find(key);
  if (it != map.end())
  {
    return it->second.get();
  }
  std::shared_ptr<NodeList> list = std::make_shared<NodeList>(d_context);
  map.insert(key, list);
  return list.get();
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
