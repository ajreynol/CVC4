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

namespace cvc5::internal {
namespace proof {

  LogosLeanNodeConverter::LogosLeanNodeConverter(NodeManager* nm) : AlfNodeConverter(nm){}
  LogosLeanNodeConverter::~LogosLeanNodeConverter(){}


}  // namespace proof
}  // namespace cvc5::internal

