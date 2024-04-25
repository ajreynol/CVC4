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
 * Lemma loader for cvc5.
 */

#ifndef CVC5__LEMMA_LOADER_H
#define CVC5__LEMMA_LOADER_H

#include <cvc5/cvc5.h>

namespace cvc5 {

namespace parser {
class SymbolManager;
}

namespace main {

/**
 * The lemma loader plugin, for sending lemmas by reading from disk.
 */
class LemmaLoader : public cvc5::Plugin
{
 public:
  LemmaLoader(TermManager& tm,
              std::string& filename,
              Solver* s,
              parser::SymbolManager* sm);
  ~LemmaLoader();
  /** Returns a list of formulas to be sent as lemmas to the internal solver */
  std::vector<Term> check() override;
  /** Get name, for debugging */
  std::string getName() override;
  /** The filename we are reading from */
  std::string getFileName();

 private:
  /** The filename to read from */
  std::string d_filename;
  /** The solver we are associated with */
  Solver* d_solver;
  /** The symbol manager (for parsing) */
  parser::SymbolManager* d_symman;
};

}  // namespace main
}  // namespace cvc5

#endif /* CVC5__LEMMA_LOADER_H */
