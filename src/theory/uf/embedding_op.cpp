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
#include "theory/evaluator.h"

using namespace cvc5::internal::kind;

namespace cvc5::internal {

std::ostream& operator<<(std::ostream& out, const EmbeddingOp& op)
{
  out << "e_" << op.getType().getId();
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

bool isNaryKind(Kind k)
{
  // NOTE: this may not be precise
  return NodeManager::isNAryKind(k) && k != Kind::APPLY_UF
         && k != Kind::APPLY_CONSTRUCTOR;
}

class EmbeddingOpConverter : public NodeConverter
{
 public:
  EmbeddingOpConverter(const TypeNode& usort,
                       std::unordered_set<Kind>& naryKinds)
      : d_usort(usort), d_naryKinds(naryKinds)
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
    // TODO: what if terms are empty???
    // parametric???
    Kind k = orig.getKind();
    if (k == Kind::EQUAL)
    {
      // equality is preserved
      return terms[0].eqNode(terms[1]);
    }
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
    if (isNaryKind(k))
    {
      d_naryKinds.insert(k);
      Assert(terms.size() >= 2);
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
  std::unordered_set<Kind>& d_naryKinds;
};

Node EmbeddingOp::convertToEmbedding(const Node& n,
                                     const TypeNode& tn,
                                     std::unordered_set<Kind>& naryKinds)
{
  EmbeddingOpConverter eoc(tn, naryKinds);
  return eoc.convert(n, false);
}
Node EmbeddingOp::convertToEmbedding(const Node& n, const TypeNode& tn)
{
  std::unordered_set<Kind> naryKinds;
  return convertToEmbedding(n, tn, naryKinds);
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

std::vector<Node> EmbeddingOp::simplifyApplyEmbedding(const Node& node)
{
  Assert(node.getKind() == Kind::APPLY_EMBEDDING);
  std::vector<Node> lemmas;
  if (node.getNumChildren() > 0)
  {
    bool allConst = true;
    // if all arguments are constant, we return the non-symbolic version
    for (const Node& nc : node)
    {
      if (!nc.isConst())
      {
        allConst = false;
        break;
      }
    }
    if (allConst)
    {
      Trace("builtin-rewrite")
          << "rewriteApplyEmbedding: " << node << std::endl;
      // use the utility
      Node n = EmbeddingOp::convertToConcrete(node);
      theory::Evaluator ev(nullptr);
      Node nev = ev.eval(n, {}, {});
      if (!nev.isNull() && nev.isConst())
      {
        // convert?
        Node nevc = convertToEmbedding(nev, node.getType());
        Node lem = nev.eqNode(nevc);
        lemmas.push_back(lem);
      }
    }
  }
  // TODO: more, arith poly norm???
  return lemmas;
}

}  // namespace cvc5::internal
