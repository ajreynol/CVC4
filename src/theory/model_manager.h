/*********************                                                        */
/*! \file model_manager.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Abstract management of models for TheoryEngine.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__MODEL_MANAGER__H
#define CVC4__THEORY__MODEL_MANAGER__H

#include <map>
#include <memory>

#include "theory/relevant_terms_database.h"
#include "theory/theory_model.h"
#include "theory/theory_model_builder.h"

namespace CVC4 {

class TheoryEngine;

namespace theory {

/**
 * A base class for managing models. Its main feature is to implement a
 * buildModel command, which can be specific e.g. to the kind of equality
 * engine management mode we are using.
 */
class ModelManager
{
 public:
  ModelManager(TheoryEngine& te, RelevantTermsDatabase& rtdb);
  virtual ~ModelManager();
  /** Finish initializing this class. */
  void finishInit();
  /** Reset model, called during full effort check before the model is built */
  void resetModel();
  /**
   * Build the model. If we have yet to build the model on this round, this
   * method calls the (manager-specific) prepareModel method and then calls
   * finishBuildModel.
   *
   * @return true if model building was successful.
   */
  bool buildModel();
  /**
   * Have we called buildModel this round? Note this returns true whether or
   * not the model building was successful.
   */
  bool isModelBuilt() const;
  /**
   * Post process model, which is used as a way of each theory adding additional
   * information to the model after successfully building a model.
   */
  void postProcessModel(bool incomplete);
  /** Get a pointer to model object maintained by this class. */
  theory::TheoryModel* getModel();
  //------------------------ finer grained control over model building
  /**
   * Prepare model, which the manager-specific method for setting up the
   * equality engine of the model. This should assert all relevant information
   * about the model into the equality engine of d_model.
   *
   * @return true if we successful (i.e. the equality engine of the model
   * equality engine is consistent).
   */
  virtual bool prepareModel() = 0;
  /** is using relevant terms? */
  virtual bool isUsingRelevantTerms() const;
  /**
   * Finish build model, which calls the theory model builder to assign values
   * to all equivalence classes. This should be run after prepareModel.
   *
   * @return true if model building was successful.
   */
  bool finishBuildModel() const;
  //------------------------ end finer grained control over model building
 protected:
  /**
   * Collect model Boolean variables.
   * This asserts the values of all boolean variables to the equality engine of
   * the model, based on their value in the prop engine.
   *
   * @return true if we are in conflict.
   */
  bool collectModelBooleanVariables();
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Reference to the relevant term database of the combination engine */
  RelevantTermsDatabase& d_rtdb;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** The model object we are using */
  theory::TheoryModel* d_model;
  /** The model object we have allocated (if one exists) */
  std::unique_ptr<theory::TheoryModel> d_alocModel;
  /** The model builder object we are using */
  theory::TheoryEngineModelBuilder* d_modelBuilder;
  /** The model builder object we have allocated (if one exists) */
  std::unique_ptr<theory::TheoryEngineModelBuilder> d_alocModelBuilder;
  /** whether we have tried to build this model in the current context */
  bool d_modelBuilt;
  /** whether this model has been built successfully */
  bool d_modelBuiltSuccess;
  /** Dummy vector for empty relevant terms */
  std::set<Node> d_emptyset;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__MODEL_MANAGER__H */
