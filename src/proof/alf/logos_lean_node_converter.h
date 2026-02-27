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
#include "cvc5_private.h"

#ifndef CVC5__PROOF__ALF__LOGOS_LEAN_NODE_CONVERTER_H
#define CVC5__PROOF__ALF__LOGOS_LEAN_NODE_CONVERTER_H

#include <iostream>
#include <map>

#include "expr/node.h"
#include "proof/alf/alf_node_converter.h"

namespace cvc5::internal {
namespace proof {

/**
 * This is a helper class for the ALF printer that converts nodes into
 * form that ALF expects. It should only be used by the ALF printer.
 */
class LogosLeanNodeConverter : public AlfNodeConverter
{
 public:
  LogosLeanNodeConverter(NodeManager* nm);
  ~LogosLeanNodeConverter();

  /** Convert at post-order traversal */
  Node postConvert(Node n) override;
  /** Should we traverse n? */
  bool shouldTraverse(Node n) override;
 private:
   std::string cleanSmtId(const std::string& str);
   size_t d_constIdCount;
   std::map<Node, size_t> d_constId;
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
