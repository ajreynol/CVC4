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

#include "main/lemma_loader.h"

#include <cvc5/cvc5_parser.h>
#include <cvc5/cvc5_types.h>

#include "base/check.h"
#include "base/output.h"
#include "parser/sym_manager.h"

namespace cvc5 {
namespace main {

LemmaLoader::LemmaLoader(std::string& filename,
                         Solver* s,
                         parser::SymbolManager* sm)
    : d_filename(filename), d_solver(s), d_symman(sm)
{
}
LemmaLoader::~LemmaLoader() {}

static bool alreadyReadFromFile = false;

std::vector<Term> LemmaLoader::check()
{
  std::vector<Term> lemmas;
  Trace("lemma-loader") << "LemmaLoader::check" << std::endl;
  // if applicable, read a list of formulas from disk, based on a time limit.
  bool readFromFile = !alreadyReadFromFile;
  if (readFromFile)
  {
    alreadyReadFromFile = true;
    parser::InputParser ip(d_solver, d_symman);
    // use the input language specified by the options
    ip.setFileInput(modes::InputLanguage::SMT_LIB_2_6, d_filename);
    // reads a list of formulas
    //   F1 .... Fn
    // each of which will be sent as a lemma
    Term lem;
    for (;;)
    {
      lem = ip.nextTerm();
      if (lem.isNull())
      {
        break;
      }
      Assert(lem.getSort().isBoolean());
      lemmas.push_back(lem);
      Trace("lemma-loader-lemma")
          << "(loader-lemma " << lem << ")" << std::endl;
    }
  }
  return lemmas;
}
std::string LemmaLoader::getName() { return "LemmaLoader"; }

std::string LemmaLoader::getFileName() { return d_filename; }

}  // namespace main
}  // namespace cvc5
