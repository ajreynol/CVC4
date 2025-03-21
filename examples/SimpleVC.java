/******************************************************************************
 * Top contributors (to current version):
 *   Daniel Larraz, Mudathir Mohamed, Morgan Deters
 *
 * This file is part of the cvc5 project.
 *
 * Copyright (c) 2009-2025 by the authors listed in the file AUTHORS
 * in the top-level source directory and their institutional affiliations.
 * All rights reserved.  See the file COPYING in the top-level source
 * directory for licensing information.
 * ****************************************************************************
 *
 * A simple demonstration of the Java interface.
 *
 * To run the resulting class file, you need to do something like the
 * following:
 *   javac  "-cp" "../build/src/api/java/cvc5.jar" SimpleVC.java
 *   java \
 *     "-Djava.library.path=../build/src/api/java" "-cp" "../build/src/api/java/cvc5.jar:." \
 *     SimpleVC
 */

import static io.github.cvc5.Kind.*;

import io.github.cvc5.*;

public class SimpleVC
{
  public static void main(String[] args)
  {
    TermManager tm = new TermManager();
    Solver slv = new Solver(tm);
    {
      // Prove that for integers x and y:
      //   x > 0 AND y > 0  =>  2x + y >= 3

      Sort integer = tm.getIntegerSort();

      Term x = tm.mkConst(integer, "x");
      Term y = tm.mkConst(integer, "y");
      Term zero = tm.mkInteger(0);

      Term x_positive = tm.mkTerm(Kind.GT, x, zero);
      Term y_positive = tm.mkTerm(Kind.GT, y, zero);

      Term two = tm.mkInteger(2);
      Term twox = tm.mkTerm(Kind.MULT, two, x);
      Term twox_plus_y = tm.mkTerm(Kind.ADD, twox, y);

      Term three = tm.mkInteger(3);
      Term twox_plus_y_geq_3 = tm.mkTerm(Kind.GEQ, twox_plus_y, three);

      Term formula = tm.mkTerm(Kind.AND, x_positive, y_positive).impTerm(twox_plus_y_geq_3);

      System.out.println("Checking entailment of formula " + formula + " with cvc5.");
      System.out.println("cvc5 should report UNSAT.");
      System.out.println(
          "Result from cvc5 is: " + slv.checkSatAssuming(formula.notTerm()));
    }
  }
}
