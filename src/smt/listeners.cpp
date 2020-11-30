/*********************                                                        */
/*! \file listeners.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds, Abdalrhman Mohamed
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Implements listener classes for SMT engine.
 **/

#include "smt/listeners.h"

#include "smt/smt_engine.h"
#include "smt/smt_engine_scope.h"

namespace CVC4 {
namespace smt {

ResourceOutListener::ResourceOutListener(SmtEngine& smt) : d_smt(smt) {}

void ResourceOutListener::notify()
{
  SmtScope scope(&d_smt);
  Assert(smt::smtEngineInScope());
  d_smt.interrupt();
}


}  // namespace smt
}  // namespace CVC4
