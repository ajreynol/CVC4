/******************************************************************************
 * Top contributors (to current version):
 *   Mudathir Mohamed, Mathias Preiner
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2024 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A class for empty bags.
 */

#include "theory/uf/opaque_value.h"

#include "expr/node.h"
#include "expr/type_node.h"

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const OpaqueValue& ov)
{
  return out << "(opaque_value " << ov.getValue() << ")";
}

size_t OpaqueValueHashFunction::operator()(const OpaqueValue& ov) const
{
  return std::hash<Node>()(ov.getValue());
}

/**
 * Constructs an emptybag of the specified type. Note that the argument
 * is the type of the bag itself, NOT the type of the elements.
 */
OpaqueValue::OpaqueValue(const Node& val) : d_value(new Node(val)) {}

OpaqueValue::OpaqueValue(const OpaqueValue& ov)
    : d_value(new Node(ov.getValue()))
{
}

OpaqueValue& OpaqueValue::operator=(const OpaqueValue& ov)
{
  (*d_value) = ov.getValue();
  return *this;
}

OpaqueValue::~OpaqueValue() {}

const Node& OpaqueValue::getValue() const { return *d_value; }

bool OpaqueValue::operator==(const OpaqueValue& ov) const
{
  return getValue() == ov.getValue();
}

}  // namespace cvc5::internal
