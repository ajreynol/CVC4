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
 * Canonical variable.
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__BUILTIN__CANON_VAR_H
#define CVC5__THEORY__BUILTIN__CANON_VAR_H

#include <iosfwd>
#include <memory>
#include "expr/skolem_manager.h"

namespace cvc5::internal {

class TypeNode;

class CanonVar
{
 public:
  /**
   * Constructs an emptyset of the specified type. Note that the argument
   * is the type of the set itself, NOT the type of the elements.
   */
  CanonVar(SkolemFunId id, const TypeNode& type);
  ~CanonVar();
  CanonVar(const CanonVar& other);
  CanonVar& operator=(const CanonVar& other);

  SkolemFunId getId() const;
  const TypeNode& getType() const;
  bool operator==(const CanonVar& cv) const;
  bool operator!=(const CanonVar& cv) const;
  bool operator<(const CanonVar& cv) const;
  bool operator<=(const CanonVar& cv) const;
  bool operator>(const CanonVar& cv) const;
  bool operator>=(const CanonVar& cv) const;

 private:
  CanonVar();
  SkolemFunId d_id;
  std::unique_ptr<TypeNode> d_type;
  std::unique_ptr<Node> d_cacheVal;
}; /* class CanonVar */

std::ostream& operator<<(std::ostream& out, const CanonVar& cv);

struct CanonVarHashFunction
{
  size_t operator()(const CanonVar& cv) const;
}; /* struct CanonVarHashFunction */

} 

#endif /* CVC5__EMPTY_SET_H */
