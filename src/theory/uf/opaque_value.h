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
 * A class for opaque values.
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__UF__OPAQUE_VALUE_H
#define CVC5__THEORY__UF__OPAQUE_VALUE_H

#include <iosfwd>
#include <memory>

namespace cvc5::internal {

template <bool ref_count>
class NodeTemplate;
typedef NodeTemplate<true> Node;

class OpaqueValue
{
 public:
  explicit OpaqueValue(const Node& val);
  ~OpaqueValue();
  OpaqueValue(const OpaqueValue& other);
  OpaqueValue& operator=(const OpaqueValue& other);

  const Node& getValue() const;
  bool operator==(const OpaqueValue& ov) const;

 private:
  OpaqueValue();

  /** the value this constant represents */
  std::unique_ptr<Node> d_value;
};

std::ostream& operator<<(std::ostream& out, const OpaqueValue& ov);

struct OpaqueValueHashFunction
{
  size_t operator()(const OpaqueValue& ov) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__UF__OPAQUE_VALUE_H */
