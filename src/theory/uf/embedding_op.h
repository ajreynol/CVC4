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
 * A class for representing embedding operators.
 */

#include "cvc5_public.h"

#ifndef CVC5__THEORY__UF__EMBEDDING_OP_H
#define CVC5__THEORY__UF__EMBEDDING_OP_H

#include <vector>

#include "expr/kind.h"
#include "expr/node.h"

namespace cvc5::internal {

/**
 * The payload for embedding operators, which carries a kind specifying the kind
 * of type this embedding operator corresponds to.
 */
class EmbeddingOp
{
 public:
  EmbeddingOp(const TypeNode& ftype, Kind k);
  EmbeddingOp(const EmbeddingOp& op);

  /** */
  const TypeNode& getType() const;
  /** Return the kind of indexed operator this operator represents */
  Kind getKind() const;

  bool operator==(const EmbeddingOp& op) const;

  /**
   * Get the concrete term corresponding to the application of
   * APPLY_INDEXED_SYMBOLIC. Requires all indices to be constant.
   */
  static Node convertToConcrete(const Node& app);

  /** */
  static Node convertToEmbedding(const Node& n, const TypeNode& tn);

 private:
  EmbeddingOp();
  /** The type */
  std::unique_ptr<TypeNode> d_ftype;
  /** The kind of indexed operator this operator represents */
  Kind d_kind;
};

std::ostream& operator<<(std::ostream& out, const EmbeddingOp& op);

/**
 * Hash function for the EmbeddingOp objects.
 */
struct EmbeddingOpHashFunction
{
  size_t operator()(const EmbeddingOp& op) const;
};

}  // namespace cvc5::internal

#endif /* CVC5__THEORY__BUILTIN__GENERIC_OP_H */
