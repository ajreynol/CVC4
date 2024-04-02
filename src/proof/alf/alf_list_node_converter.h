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
  AlfListNodeConverter(NodeManager * nm, BaseAlfNodeConverter& tproc);
  /** convert */
  Node postConvert(Node n) override;
 private:
  /** The parent tprocerter, used for getting internal symbols and utilities */
  BaseAlfNodeConverter& d_tproc;
};

class AlfAbstractTypeConverter
{
 public:
  AlfAbstractTypeConverter(NodeManager * nm, BaseAlfNodeConverter& tproc);
  /** post-convert type */
  Node process(const TypeNode& tn);
  /** get free parameters */
  std::vector<Node> getFreeParameters() const;
 private:
  /** Pointer to node manager */
  NodeManager * d_nm;
  /** The parent tprocerter, used for getting internal symbols and utilities */
  BaseAlfNodeConverter& d_tproc;
  /** Get the free parameters */
  std::vector<Node> d_params;
  /** Counters */
  size_t d_typeCounter;
  size_t d_intCounter;
  /** The type of ALF sorts, which can appear in terms */
  TypeNode d_sortType;
  /** Kind to name */
  std::map<Kind, std::string> d_kindToName;  
};

}  // namespace proof
}  // namespace cvc5::internal

#endif
