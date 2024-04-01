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

AlfListNodeConverter::AlfListNodeConverter(BaseAlfNodeConverter& tproc)
    : d_tproc(tproc)
{
}

Node AlfListNodeConverter::postConvert(Node n)
{
  Node alfNullt;
  Kind k = n.getKind();
  if (NodeManager::isNAryKind(k))
  {
    TypeNode tn = n.getType();
    alfNullt = d_tproc.getNullTerminator(k, tn);
  }
  if (!alfNullt.isNull())
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
      return d_tproc.mkInternalApp("$dsl.singleton_elim", {n}, n.getType());
    }
  }
  return n;
}

AlfAbstractTypeConverter::AlfAbstractTypeConverter(BaseAlfNodeConverter& tproc)
    : d_tproc(tproc)
{
}

TypeNode AlfAbstractTypeConverter::postConvertType(TypeNode tn)
{
  return tn;
}

}  // namespace proof
}  // namespace cvc5::internal
