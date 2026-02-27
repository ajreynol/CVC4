/******************************************************************************
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2026 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * Implementation of ALF node conversion
 */

#include "proof/alf/logos_lean_node_converter.h"

#include "util/bitvector.h"
#include "util/iand.h"
#include "util/indexed_root_predicate.h"
#include "util/rational.h"
#include "util/regexp.h"
#include "util/string.h"
#include "theory/uf/theory_uf_rewriter.h"
#include "printer/smt2/smt2_printer.h"

namespace cvc5::internal {
namespace proof {

LogosLeanNodeConverter::LogosLeanNodeConverter(NodeManager* nm)
    : AlfNodeConverter(nm)
{
}
LogosLeanNodeConverter::~LogosLeanNodeConverter() {}

Node LogosLeanNodeConverter::postConvert(Node n)
{
  Kind k = n.getKind();
  if (k==Kind::CONST_INTEGER)
  {
    std::stringstream ss;
    ss << "(Term.Numeral " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::CONST_RATIONAL)
  {
    std::stringstream ss;
    ss << "(Term.Rational " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::CONST_STRING)
  {
    std::stringstream ss;
    ss << "(Term.String " << n << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::CONST_BITVECTOR)
  {
    BitVector b = n.getConst<BitVector>();;
    std::stringstream ss;
    ss << "(Term.Binary " << b.getSize() << " " << b.getValue() << ")";
    return mkInternalSymbol(ss.str(), n.getType());
  }
  else if (k==Kind::APPLY_UF)
  {
    // convert to curried apply
    return convert(theory::uf::TheoryUfRewriter::getHoApplyForApplyUf(n));
  }
  else if (k==Kind::HO_APPLY)
  {
    return mkInternalApp("Term.Apply", {n[0], n[1]}, n.getType());
  }
  else if (k==Kind::BOUND_VAR_LIST)
  {
    // TODO
  }
  else if (k==Kind::FORALL || k==Kind::EXISTS || k==Kind::LAMBDA)
  {
    // TODO
  }
  else if (k==Kind::APPLY_CONSTRUCTOR)
  {
  }
  else if (k==Kind::APPLY_TESTER)
  {
  }
  else if (k==Kind::APPLY_SELECTOR)
  {
  }
  else if (n.getNumChildren()>0)
  {
    // convert to curried apply
    std::stringstream ssOp;
    ssOp << printer::smt2::Smt2Printer::smtKindString(k);
    std::string id = cleanSmtId(ssOp.str());
    std::vector<Node> args(n.begin(), n.end());
    return mkInternalApp(id, args, n.getType());
  }
  
  return n;
}

std::string replace_all(std::string str,
                                   const std::string& from,
                                   const std::string& to)
{
  if (from.empty()) return str;  // avoid infinite loop

  std::size_t pos = 0;
  while ((pos = str.find(from, pos)) != std::string::npos)
  {
    str.replace(pos, from.length(), to);
    pos += to.length();  // move past the replacement
  }
  return str;
}

std::string LogosLeanNodeConverter::cleanSmtId(const std::string& id)
{
  std::string idc = id;
  idc = replace_all(idc, "++", "concat");
  idc = replace_all(idc, "+", "plus");
  idc = replace_all(idc, "-", "neg");
  idc = replace_all(idc, "*", "mult");
  idc = replace_all(idc, "=>", "imp");
  idc = replace_all(idc, "<=", "leq");
  idc = replace_all(idc, "<", "lt");
  idc = replace_all(idc, ">=", "geq");
  idc = replace_all(idc, ">", "gt");
  idc = replace_all(idc, "=", "eq");
  idc = replace_all(idc, "/", "qdiv");
  idc = replace_all(idc, "^", "exp");
  idc = replace_all(idc, ".", "_");
  idc = replace_all(idc, "@", "_at_");
  idc = replace_all(idc, "$", "__");
  return idc;
}
  
}  // namespace proof
}  // namespace cvc5::internal
