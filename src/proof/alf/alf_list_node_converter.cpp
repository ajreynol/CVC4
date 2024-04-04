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
  switch (k)
  {
    case Kind::STRING_CONCAT:
    case Kind::BITVECTOR_ADD:
    case Kind::BITVECTOR_MULT:
    case Kind::BITVECTOR_AND:
    case Kind::BITVECTOR_OR:
    case Kind::BITVECTOR_XOR:
    case Kind::FINITE_FIELD_ADD:
    case Kind::FINITE_FIELD_MULT:
    case Kind::OR:
    case Kind::AND:
    case Kind::SEP_STAR:
    case Kind::ADD:
    case Kind::MULT:
    case Kind::NONLINEAR_MULT:
    case Kind::BITVECTOR_CONCAT:
    case Kind::REGEXP_CONCAT:
    case Kind::REGEXP_UNION:
    case Kind::REGEXP_INTER:
      // operators with a ground null terminator
      break;
    default:
      // not an n-ary kind
      return n;
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
