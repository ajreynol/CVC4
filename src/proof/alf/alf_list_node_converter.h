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
 * Implementation of ALF node tprocersion for list variables in DSL rules
 */
#include "cvc5_private.h"

#ifndef CVC4__PROOF__ALF__ALF_LIST_NODE_CONVERTER_H
#define CVC4__PROOF__ALF__ALF_LIST_NODE_CONVERTER_H

#include "expr/node_converter.h"
#include "proof/alf/alf_node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 */
class AlfListNodeConverter : public NodeConverter
{
 public:
  AlfListNodeConverter(BaseAlfNodeConverter& tproc);
  /** tprocert to internal */
  Node postConvert(Node n) override;
 private:
  /** The parent tprocerter, used for getting internal symbols and utilities */
  BaseAlfNodeConverter& d_tproc;
};

class AlfAbstractTypeConverter : public NodeConverter
{
 public:
  AlfAbstractTypeConverter(BaseAlfNodeConverter& tproc);
  /** tprocert to internal */
  TypeNode postConvertType(TypeNode n) override;
 private:
  /** The parent tprocerter, used for getting internal symbols and utilities */
  BaseAlfNodeConverter& d_tproc;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
