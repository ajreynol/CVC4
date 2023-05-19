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

#include "base/check.h"
#include "base/output.h"
#include "parser/api/cpp/input_parser.h"

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
    ip.setFileInput(d_solver->getOption("input-language"), d_filename);
    // set the logic
    // TODO: retreive logic string from solver? (not available currently)
    // For now, assume "ALL" logic.
    ip.setLogic("ALL");
    // reads a list of formulas
    //   F1 .... Fn
    // each of which will be sent as a lemma
    Term lem;
    for (;;)
    {
      lem = ip.nextExpression();
      if (lem.isNull())
      {
        break;
      }
      Assert(lem.getSort().isBoolean());
      lemmas.push_back(lem);
      Trace("lemma-loader") << "...read lemma " << lem << std::endl;
    }
  }
  return lemmas;
}
std::string LemmaLoader::getName() { return "LemmaLoader"; }

std::string LemmaLoader::getFileName() { return d_filename; }

}  // namespace main
}  // namespace cvc5
