package sudoku

import regolic.api.API._
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import regolic.sat.DPLL._
import regolic.sat.Literal

object Solver {

  def solver(sudoku: Array[Array[Option[Int]]]): Option[Array[Array[Int]]] = {
    val vars = sudoku.map(row => row.map(el => Array.fill(9)(boolVar())))
    val onePerEntry = vars.flatMap(row => row.map(vs => Or(vs:_*)))
    val uniqueInColumns = for(c <- 0 to 8; k <- 0 to 8; r1 <- 0 to 7; r2 <- r1+1 to 8)
      yield !vars(r1)(c)(k) || !vars(r2)(c)(k)
    val uniqueInRows = for(r <- 0 to 8; k <- 0 to 8; c1 <- 0 to 7; c2 <- c1+1 to 8)
      yield !vars(r)(c1)(k) || !vars(r)(c2)(k)
    val uniqueInGrid1 =
      for(k <- 0 to 8; i <- 0 to 2; j <- 0 to 2; r <- 0 to 2; c1 <- 0 to 1; c2 <- c1+1 to 2)
        yield !vars(3*i + r)(3*j + c1)(k) || !vars(3*i + r)(3*j + c2)(k)
    val uniqueInGrid2 =
      for(k <- 0 to 8; i <- 0 to 2; j <- 0 to 2; r1 <- 0 to 2; c1 <- 0 to 2; c2 <- 0 to 2; r2 <- r1+1 to 2)
        yield !vars(3*i + r1)(3*j + c1)(k) || !vars(3*i + r2)(3*j + c2)(k)
    val forcedEntries = for(r <- 0 to 8; c <- 0 to 8 if sudoku(r)(c) != None)
      yield Or(vars(r)(c)(sudoku(r)(c).get - 1))
    val allConstraints = onePerEntry ++ uniqueInColumns ++ uniqueInRows ++ uniqueInGrid1 ++ uniqueInGrid2 ++ forcedEntries
    solve(And(allConstraints:_*)) match {
      case None => None
      case Some(model) => Some(vars.map(row => row.map(vs => vs.indexWhere(v => model(v)) + 1)))
    }
  }

}
