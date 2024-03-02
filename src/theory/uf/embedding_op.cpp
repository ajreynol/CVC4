/******************************************************************************
 * Top contributors (to current version):
 *   Andrew Reynolds, Aina Niemetz, Mathias Preiner
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

#include "theory/uf/embedding_op.h"

#include <iostream>

#include "expr/node_converter.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const EmbeddingOp& op)
{
  return out << "(EmbeddingOp " << op.getKind() << ')';
}

size_t EmbeddingOpHashFunction::operator()(const EmbeddingOp& op) const
{
  return kind::KindHashFunction()(op.getKind());
}

EmbeddingOp::EmbeddingOp(const TypeNode& ftype, Kind k)
    : d_ftype(new TypeNode(ftype)), d_kind(k)
{
}

EmbeddingOp::EmbeddingOp(const EmbeddingOp& op)
    : d_ftype(new TypeNode(op.getType())), d_kind(op.getKind())
{
}

const TypeNode& EmbeddingOp::getType() const { return *d_ftype.get(); }
Kind EmbeddingOp::getKind() const { return d_kind; }

bool EmbeddingOp::operator==(const EmbeddingOp& op) const
{
  return getType() == op.getType() && getKind() == op.getKind();
}

class EmbeddingOpConverter : public NodeConverter
{
 public:
  EmbeddingOpConverter(const TypeNode& usort) : d_usort(usort) {}
  Node postConvertUntyped(Node orig,
                                  const std::vector<Node>& terms,
                                  bool termsChanged)
  {
    NodeManager* nm = NodeManager::currentNM();
    if (n.isVar())
    {
      // replace by new var
      return nm->getSkolemManager()->mkInternalSkolemFunction(InternalSkolemFunId::EMBED_VAR, d_usort, {n});
    }
    // TODO: what if terms are empty???
    Kind k = n.getKind();
    std::vector<Node> args;
    args.push_back(nm->mkConst(EmbeddingOp(d_usort, k)));
    args.insert(args.end(), terms.begin(), terms.end());
    return nm->mkNode(Kind::APPLY_EMBEDDING, args);
  }
private:
  TypeNode d_usort;
};

Node EmbeddingOp::convertToEmbedding(const Node& n, const TypeNode& tn)
{
  EmbeddingOpConverter eoc(tn);
  return eoc.convert(n, false);
}

Node EmbeddingOp::convertToConcrete(const Node& app)
{
  Trace("generic-op") << "getConcreteApp " << app << std::endl;
  Assert(app.getKind() == Kind::APPLY_INDEXED_SYMBOLIC);
  Kind okind = app.getOperator().getConst<EmbeddingOp>().getKind();
  std::vector<Node> args;
  args.insert(args.end(), app.begin(), app.end());
  Node ret = NodeManager::currentNM()->mkNode(okind, args);
  return ret;
}

}  // namespace cvc5::internal
