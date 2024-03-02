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

AlfListNodeConverter::AlfListNodeConverter(AlfNodeConverter& tproc)
    : d_tproc(tproc)
{
}

Node AlfListNodeConverter::postConvert(Node n)
{
  bool isNary = false;
  Node nullt;
  Kind k = n.getKind();
  if (NodeManager::isNAryKind(k))
  {
    nullt = d_tproc.getNullTerminator(k, n.getType());
    isNary = !nullt.isNull();
  }
  if (isNary)
  {
    size_t nlistChildren = 0;
    for (const Node& nc : n)
    {
      if (!expr::isListVar(nc))
      {
        nlistChildren++;
      }
    }
    if (nlistChildren < 2)
    {
      TypeNode tn = NodeManager::currentNM()->booleanType();
      Node op = d_tproc.mkInternalSymbol(
          printer::smt2::Smt2Printer::smtKindString(k), tn);
      std::vector<Node> children;
      children.push_back(op);
      children.push_back(n);
      return d_tproc.mkInternalApp("alf.from_list", children, n.getType());
    }
  }
  return n;
}

}  // namespace proof
}  // namespace cvc5::internal
