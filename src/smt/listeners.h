/*********************                                                        */
/*! \file listeners.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Mathias Preiner
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Listener classes for SMT engine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__SMT__LISTENERS_H
#define CVC4__SMT__LISTENERS_H

#include <vector>

#include "base/listener.h"

namespace CVC4 {

class SmtEngine;

namespace smt {

/** A listener for resource outs */
class ResourceOutListener : public Listener
{
 public:
  ResourceOutListener(SmtEngine& smt);
  /** notify method, interupts SmtEngine */
  void notify() override;

 private:
  /** Reference to the SmtEngine */
  SmtEngine& d_smt;
};

}  // namespace smt
}  // namespace CVC4

#endif
