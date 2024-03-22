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
 * Lemma saver for cvc5.
 */

#ifndef CVC5__LEMMA_SAVER_H
#define CVC5__LEMMA_SAVER_H

#include <cvc5/cvc5.h>

#include <fstream>

namespace cvc5 {
namespace main {

/**
 * The lemma saver plugin, for saving lemmas to disk.
 */
class LemmaSaver : public cvc5::Plugin
{
 public:
  LemmaSaver(TermManager& tm, std::string& filename, Solver* s);
  ~LemmaSaver();
  /** */
  void notifySatClause(const Term& t) override;
  /** */
  void notifyTheoryLemma(const Term& t) override;
  /** Get name, for debugging */
  std::string getName() override;
  /** The filename we are saving to */
  std::string getFileName();

 private:
  /** The filename to read from */
  std::string d_filename;
  /** The solver we are associated with */
  Solver* d_solver;
  /** File stream */
  std::fstream d_fs;
};

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__LEMMA_SAVER_H */
