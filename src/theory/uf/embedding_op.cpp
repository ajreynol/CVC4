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
#include "expr/skolem_manager.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const EmbeddingOp& op)
{
  out << "e_" << op.getType().getId() << "_" << op.getKind();
  /*
  if (!op.getOp().isNull())
  {
    out << "_" << op.getOp().getId();
  }
  */
  return out;
}

size_t EmbeddingOpHashFunction::operator()(const EmbeddingOp& op) const
{
  return kind::KindHashFunction()(op.getKind())
         * std::hash<TypeNode>()(op.getType()) * std::hash<Node>()(op.getOp());
}

EmbeddingOp::EmbeddingOp(const TypeNode& ftype, const Node& op, Kind k)
    : d_ftype(new TypeNode(ftype)), d_kind(k), d_op(new Node(op))
{
}

EmbeddingOp::EmbeddingOp(const EmbeddingOp& op)
    : d_ftype(new TypeNode(op.getType())),
      d_kind(op.getKind()),
      d_op(new Node(op.getOp()))
{
}

const TypeNode& EmbeddingOp::getType() const { return *d_ftype.get(); }
Kind EmbeddingOp::getKind() const { return d_kind; }
const Node& EmbeddingOp::getOp() const { return *d_op.get(); }

bool EmbeddingOp::operator==(const EmbeddingOp& op) const
{
  return getType() == op.getType() && getKind() == op.getKind()
         && getOp() == op.getOp();
}

bool EmbeddingOp::isNaryKind(Kind k)
{
  // NOTE: this may not be precise
  return NodeManager::isNAryKind(k) && k != Kind::APPLY_UF
         && k != Kind::APPLY_CONSTRUCTOR;
}

class EmbeddingOpConverter : public NodeConverter
{
 public:
  EmbeddingOpConverter(const TypeNode& usort)
      : d_usort(usort)
  {
  }
  Node postConvertUntyped(Node orig,
                          const std::vector<Node>& terms,
                          bool termsChanged) override
  {
    NodeManager* nm = NodeManager::currentNM();
    if (orig.isVar())
    {
      // replace by new var
      return nm->getSkolemManager()->mkInternalSkolemFunction(
          InternalSkolemFunId::EMBEDDING_VAR, d_usort, {orig});
    }
    Kind k = orig.getKind();
    Node eop;
    if (orig.getMetaKind() == metakind::PARAMETERIZED)
    {
      eop = orig.getOperator();
    }
    else if (orig.getNumChildren() == 0)
    {
      // constants are stored as the operator
      eop = orig;
    }
    Node op = nm->mkConst(EmbeddingOp(d_usort, eop, k));
    // make binary
    if (EmbeddingOp::isNaryKind(k))
    {
      Assert(terms.size() >= 2) << "Expecting at least 2 terms for " << k;
      Node curr = nm->mkNode(Kind::APPLY_EMBEDDING, op, terms[0], terms[1]);
      for (size_t i = 2, tsize = terms.size(); i < tsize; i++)
      {
        curr = nm->mkNode(Kind::APPLY_EMBEDDING, op, curr, terms[i]);
      }
      return curr;
    }
    std::vector<Node> args;
    args.push_back(op);
    args.insert(args.end(), terms.begin(), terms.end());
    return nm->mkNode(Kind::APPLY_EMBEDDING, args);
  }

 private:
  TypeNode d_usort;
};


class EmbeddingOpReverter : public NodeConverter
{
 public:
  EmbeddingOpReverter()
  {
  }
  Node postConvertUntyped(Node orig,
                          const std::vector<Node>& terms,
                          bool termsChanged) override
  {
    NodeManager* nm = NodeManager::currentNM();
    if (orig.isVar())
    {
      SkolemFunId id;
      Node cacheVal;
      SkolemManager * sm = nm->getSkolemManager();
      if (sm->isSkolemFunction(orig, id, cacheVal))
      {
        InternalSkolemFunId iid = sm->getInternalId(orig);
        if (iid==InternalSkolemFunId::EMBEDDING_VAR)
        {
          Assert (cacheVal.getKind()==Kind::SEXPR && cacheVal.getNumChildren()==2);
          return cacheVal[1];
        }
      }
    }
    Kind k = orig.getKind();
    if (k==Kind::APPLY_EMBEDDING)
    {
      const EmbeddingOp& eop = orig.getOperator().getConst<EmbeddingOp>();
      if (terms.size()==1)
      {
        Assert(!eop.getOp().isNull());
        return eop.getOp();
      }
      std::vector<Node> args;
      if (!eop.getOp().isNull())
      {
        args.push_back(eop.getOp());
      }
      args.insert(args.end(), terms.begin()+1, terms.end());
      return nm->mkNode(eop.getKind(), args);
    }
    else if (k==Kind::APPLY_EMBEDDING_OP)
    {
      return orig;
    }
    Assert (false) << "Unexpected kind " << k;
    return orig;
  }
};

Node EmbeddingOp::convertToEmbedding(const Node& n,
                                     const TypeNode& tn)
{
  EmbeddingOpConverter eoc(tn);
  return eoc.convert(n, false);
}

Node EmbeddingOp::convertToConcrete(const Node& app)
{
  Trace("generic-op") << "getConcreteApp " << app << std::endl;
  EmbeddingOpReverter eor;
  return eor.convert(app, false);
}

}  // namespace cvc5::internal
