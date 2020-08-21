/*********************                                                        */
/*! \file model_manager_distributed.cpp
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Management of a distributed approach for model generation.
 **/

#include "theory/model_manager_distributed.h"

#include "theory/theory_engine.h"

namespace CVC4 {
namespace theory {

ModelManagerDistributed::ModelManagerDistributed(
    TheoryEngine& te, EqEngineManagerDistributed& eem)
    : ModelManager(te), d_eem(eem)
{
}

ModelManagerDistributed::~ModelManagerDistributed() {}

bool ModelManagerDistributed::buildModelInternal()
{
  Trace("model-builder") << "ModelManagerDistributed: reset model..."
                         << std::endl;
  // Reset model
  d_model->reset();

  // push/pop to clear the equality engine of the model
  context::Context* meec = d_eem.getModelEqualityEngineContext();
  meec->pop();
  meec->push();

  // Collect model info from the theories
  Trace("model-builder") << "ModelManagerDistributed: Collect model info..."
                         << std::endl;
  // Consult each active theory to get all relevant information concerning the
  // model, which includes both dump their equality information and assigning
  // values.
  for (TheoryId theoryId = theory::THEORY_FIRST; theoryId < theory::THEORY_LAST;
       ++theoryId)
  {
    if (!d_logicInfo.isTheoryEnabled(theoryId))
    {
      // theory not active, skip
      continue;
    }
    Theory* t = d_te.theoryOf(theoryId);
    Trace("model-builder") << "  CollectModelInfo on theory: " << theoryId
                           << std::endl;
    if (!t->collectModelInfo(d_model))
    {
      Trace("model-builder")
          << "ModelManagerDistributed: fail collect model info" << std::endl;
      return false;
    }
  }

  if (!collectModelBooleanVariables())
  {
    Trace("model-builder") << "ModelManagerDistributed: fail Boolean variables"
                           << std::endl;
    return false;
  }

  // success is determined by the model builder
  std::set<Node> emptyset;
  if (!d_modelBuilder->buildModel(d_model, false, emptyset))
  {
    Trace("model-builder") << "ModelManagerDistributed: fail build model"
                           << std::endl;
    return false;
  }
  return true;
}

}  // namespace theory
}  // namespace CVC4
