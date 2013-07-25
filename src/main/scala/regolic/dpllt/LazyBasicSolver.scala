package regolic.dpllt

import regolic.sat.Literal
import regolic.sat.Solver
import regolic.sat.Solver.Results._
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._
import regolic.smt.qfeuf.CongruenceSolver
import regolic.smt.qfeuf.CongruenceClosure

class LazyBasicSolver() {

  def solve(phi: Formula): Boolean = {

    val (clauses, nbVars, idToEq) = PropositionalSkeleton(phi)
    val satSolver = new Solver(nbVars)
    clauses.foreach(satSolver.addClause(_))
    var done = false
    var retVal = false
    while(!done) {
      satSolver.solve() match {
        case Unsatisfiable(_) => {retVal = false; done = true}
        case Satisfiable(alpha) => {
          val thAlpha = idToEq.map{case (id, eq) => alpha(id) match {
            case true => eq
            case false => Not(eq)
          }}.toList

          //TODO use same pattern as with sat solver for return values
          val cg = new CongruenceClosure()
          cg.isSat(And(thAlpha)) match {
          //CongruenceSolver.isSat(thAlpha) match {
            case Some(_) => {
              //satSolver.addClause(t)
              retVal = true
              done = true
            }
            case None => {
              retVal = false
              done = true
            }
          }
        }
        case Unknown => sys.error("SAT solver returned unknown")
      }
    }
    retVal
  }
}

