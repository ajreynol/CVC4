/*********************                                                        */
/*! \file combination_engine.h
 ** \verbatim
 ** Top contributors (to current version):
 **   Andrew Reynolds
 ** This file is part of the CVC4 project.
 ** Copyright (c) 2009-2020 by the authors listed in the file AUTHORS
 ** in the top-level source directory) and their institutional affiliations.
 ** All rights reserved.  See the file COPYING in the top-level source
 ** directory for licensing information.\endverbatim
 **
 ** \brief Abstract interface for theory combination.
 **/

#include "cvc4_private.h"

#ifndef CVC4__THEORY__COMBINATION_ENGINE__H
#define CVC4__THEORY__COMBINATION_ENGINE__H

#include <map>
#include <memory>

#include "theory/ee_manager.h"
#include "theory/model_manager.h"
#include "theory/shared_solver.h"

namespace CVC4 {

class TheoryEngine;
class SharedTermsDatabase;
class SharedTermsVisitor;

namespace theory {

/**
 * Manager for doing theory combination. This class is responsible for:
 * (1) Initializing the various components of theory combination (equality
 * engine manager, model manager, shared solver) based on the equality engine
 * mode, and
 * (2) Implementing the main combination method (combineTheories).
 */
class CombinationEngine
{
 public:
  CombinationEngine(TheoryEngine& te, const std::vector<Theory*>& paraTheories);
  virtual ~CombinationEngine();

  /** Finish initialization */
  void finishInit();

  //-------------------------- equality engine
  /** Get the equality engine theory information. */
  const EeTheoryInfo* getEeTheoryInfo(TheoryId tid) const;
  /** get the master equality engine */
  eq::EqualityEngine* getCoreEqualityEngine();
  //-------------------------- end equality engine
  //-------------------------- model
  /** reset model */
  void resetModel();
  /** Build model */
  virtual bool buildModel() = 0;
  /** Post process model */
  void postProcessModel(bool incomplete);
  /** Get model */
  TheoryModel* getModel();
  //-------------------------- end model

  /**
   * Get the shared solver, which is the active component of theory combination
   * that TheoryEngine interacts with prior to calling combineTheories.
   */
  SharedSolver* getSharedSolver();
  /**
   * Called at the beginning of full effort
   */
  virtual void resetRound();
  /**
   * Combine theories, called after FULL effort passes with no lemmas
   * and before LAST_CALL effort is run. This adds necessary lemmas for
   * theory combination (e.g. splitting lemmas) to the parent TheoryEngine.
   */
  virtual void combineTheories() = 0;
  /**
   * Get representatives, available at full effort only.
   */
  const std::unordered_set<Node, NodeHashFunction>& getEqcRepresentatives()
      const;
  /**
   * Get representatives for type, available at full effort only.
   */
  const std::vector<Node>& getEqcRepresentativesForType(TypeNode t) const;

 protected:
  /**
   * Get model equality engine notify.
   */
  virtual eq::EqualityEngineNotify* getModelEqualityEngineNotify();
  /** Send lemma */
  void sendLemma(TNode node, TheoryId atomsTo);
  /** Is theory tid parametric? */
  bool isParametric(TheoryId tid) const;
  /** Reference to the theory engine */
  TheoryEngine& d_te;
  /** Logic info of theory engine (cached) */
  const LogicInfo& d_logicInfo;
  /** List of parametric theories of theory engine */
  const std::vector<Theory*> d_paraTheories;
  /** The set of TheoryId that are parametric */
  Theory::Set d_paraSet;
  /**
   * The equality engine manager we are using. This class is responsible for
   * configuring equality engines for each theory.
   */
  std::unique_ptr<EqEngineManager> d_eemanager;
  /**
   * The model manager we are using. This class is responsible for building the
   * model.
   */
  std::unique_ptr<ModelManager> d_mmanager;
  /**
   * The shared solver. This class is responsible for performing combination
   * tasks (e.g. preregistration) during solving.
   */
  std::unique_ptr<SharedSolver> d_sharedSolver;
};

}  // namespace theory
}  // namespace CVC4

#endif /* CVC4__THEORY__COMBINATION_DISTRIBUTED__H */
