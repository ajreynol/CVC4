/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2023 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of canonical variable.
 */

#include "theory/builtin/canon_var.h"

#include <iostream>

#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const CanonVar& asa)
{
  return out << "CanonVar(" << asa.getId() << " " << asa.getType() << ')';
}

size_t CanonVarHashFunction::operator()(const CanonVar& cv) const
{
  return std::hash<TypeNode>()(cv.getType());
}

CanonVar::CanonVar(SkolemFunId id, const TypeNode& setType)
    : d_id(id), d_type(new TypeNode(setType))
{
}

CanonVar::CanonVar(const CanonVar& cv)
    : d_id(cv.getId()), d_type(new TypeNode(cv.getType()))
{
}

CanonVar& CanonVar::operator=(const CanonVar& cv)
{
  (*d_type) = cv.getType();
  return *this;
}

CanonVar::~CanonVar() {}
SkolemFunId CanonVar::getId() const { return d_id; }
const TypeNode& CanonVar::getType() const { return *d_type; }
bool CanonVar::operator==(const CanonVar& cv) const
{
  return getType() == cv.getType();
}

bool CanonVar::operator!=(const CanonVar& cv) const { return !(*this == cv); }
bool CanonVar::operator<(const CanonVar& cv) const
{
  return getType() < cv.getType();
}

bool CanonVar::operator<=(const CanonVar& cv) const
{
  return getType() <= cv.getType();
}

bool CanonVar::operator>(const CanonVar& cv) const { return !(*this <= cv); }
bool CanonVar::operator>=(const CanonVar& cv) const { return !(*this < cv); }

}  // namespace cvc5::internal
