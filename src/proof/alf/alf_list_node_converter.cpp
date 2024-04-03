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
 * Implementation of ALF node conversion for list variables in DSL rules
 */

#include "proof/alf/alf_list_node_converter.h"

#include "expr/nary_term_util.h"
#include "printer/printer.h"
#include "printer/smt2/smt2_printer.h"

namespace cvc5::internal {
namespace proof {

AlfListNodeConverter::AlfListNodeConverter(NodeManager* nm,
                                           BaseAlfNodeConverter& tproc)
    : NodeConverter(nm), d_tproc(tproc)
{
  d_absType = nm->mkAbstractType(Kind::ABSTRACT_TYPE);
}

Node AlfListNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  if (!NodeManager::isNAryKind(k))
  {
    // not an n-ary kind
    return n;
  }
  TypeNode tn = n.getType();
  Node alfNullt = d_tproc.getNullTerminator(k, tn);
  if (alfNullt.isNull())
  {
    // no nil terminator
    return n;
  }
  if (!expr::isListVar(n[n.getNumChildren() - 1]))
  {
    switch (n.getKind())
    {
      case Kind::STRING_CONCAT:
      {
        std::vector<Node> children;
        std::vector<Node> ochildren;
        ochildren.push_back(d_tproc.mkInternalSymbol(
            printer::smt2::Smt2Printer::smtKindString(k), d_absType));
        ochildren.push_back(d_tproc.mkInternalApp(
            "$char_type_of",
            {d_tproc.mkInternalApp("alf.typeof", {n[0]}, d_absType)},
            d_absType));
        children.push_back(
            d_tproc.mkInternalApp("alf._", ochildren, d_absType));
        children.insert(children.end(), n.begin(), n.end());
        n = d_tproc.mkInternalApp("_", children, n.getType());
      }
      break;
      case Kind::BITVECTOR_ADD:
      case Kind::BITVECTOR_MULT:
      case Kind::BITVECTOR_AND:
      case Kind::BITVECTOR_OR:
      case Kind::BITVECTOR_XOR: break;
      case Kind::FINITE_FIELD_ADD:
      case Kind::FINITE_FIELD_MULT: break;
      default: break;
    }
  }
  size_t nlistChildren = 0;
  for (const Node& nc : n)
  {
    if (!expr::isListVar(nc))
    {
      nlistChildren++;
    }
  }
  // if less than 2 non-list children, it might collapse to a single element
  if (nlistChildren < 2)
  {
    return d_tproc.mkInternalApp("$dsl.singleton_elim", {n}, n.getType());
  }
  return n;
}

AlfAbstractTypeConverter::AlfAbstractTypeConverter(NodeManager* nm,
                                                   BaseAlfNodeConverter& tproc)
    : d_nm(nm), d_tproc(tproc), d_typeCounter(0), d_intCounter(0)
{
  d_sortType = nm->mkSort("Type");
  d_kindToName[Kind::ARRAY_TYPE] = "Array";
  d_kindToName[Kind::BITVECTOR_TYPE] = "BitVec";
  d_kindToName[Kind::FLOATINGPOINT_TYPE] = "FloatingPoint";
  d_kindToName[Kind::FINITE_FIELD_TYPE] = "FiniteField";
  d_kindToName[Kind::SET_TYPE] = "Set";
  d_kindToName[Kind::BAG_TYPE] = "Bag";
  d_kindToName[Kind::SEQUENCE_TYPE] = "Seq";
}

Node AlfAbstractTypeConverter::process(const TypeNode& tn)
{
  // if abstract
  if (tn.isAbstract())
  {
    Kind ak = tn.getAbstractedKind();
    switch (ak)
    {
      case Kind::ABSTRACT_TYPE:
      case Kind::FUNCTION_TYPE:
      case Kind::TUPLE_TYPE:
      {
        std::stringstream ss;
        ss << "@T" << d_typeCounter;
        d_typeCounter++;
        Node n = d_tproc.mkInternalSymbol(ss.str(), d_sortType);
        d_params.push_back(n);
        return n;
      }
      break;
      case Kind::BITVECTOR_TYPE:
      case Kind::FINITE_FIELD_TYPE:
      {
        std::stringstream ss;
        ss << "@n" << d_intCounter;
        d_intCounter++;
        Node n = d_tproc.mkInternalSymbol(ss.str(), d_nm->integerType());
        d_params.push_back(n);
        Node ret = d_tproc.mkInternalApp(d_kindToName[ak], {n}, d_sortType);
        return ret;
      }
      break;
      case Kind::FLOATINGPOINT_TYPE:
      default: Unhandled() << "Cannot process abstract type kind " << ak; break;
    }
  }
  if (tn.getNumChildren() == 0)
  {
    std::stringstream ss;
    ss << tn;
    return d_tproc.mkInternalSymbol(ss.str(), d_sortType);
  }
  // get the arguments
  std::vector<Node> asNode;
  for (size_t i = 0, nchild = tn.getNumChildren(); i < nchild; i++)
  {
    Node pt = process(tn[i]);
    asNode.push_back(pt);
  }
  return d_tproc.mkInternalApp(
      d_kindToName[tn.getKind()], {asNode}, d_sortType);
}
const std::vector<Node>& AlfAbstractTypeConverter::getFreeParameters() const
{
  return d_params;
}

}  // namespace proof
}  // namespace cvc5::internal
