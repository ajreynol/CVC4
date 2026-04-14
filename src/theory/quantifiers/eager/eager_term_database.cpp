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

void TermDatabase::clear()
{
  d_terms.clear();
  d_opTerms.clear();
}

bool TermDatabase::addTerm(Node t, Node op)
{
  if (d_terms.find(t) != d_terms.end())
  {
    return false;
  }
  d_terms[t] = true;
  if (!op.isNull())
  {
    d_opTerms[op].push_back(t);
  }
  return true;
}

const std::vector<Node>* TermDatabase::getGroundTerms(Node op) const
{
  std::map<Node, std::vector<Node>>::const_iterator it = d_opTerms.find(op);
  if (it == d_opTerms.end())
  {
    return nullptr;
  }
  return &it->second;
}

size_t TermDatabase::getNumGroundTerms(Node op) const
{
  const std::vector<Node>* gts = getGroundTerms(op);
  return gts == nullptr ? 0 : gts->size();
}

}  // namespace eager
}  // namespace quantifiers
}  // namespace theory
}  // namespace cvc5::internal
