package sudoku

object Main {

  def main(args: Array[String]) {
    val puzzleInput = args(0)

    val puzzle = Parser.parse(new java.io.FileInputStream(puzzleInput))

    println("Input sudoku is:")
    println(SudokuPrinter(puzzle))

    println("Solving ...")
    Solver.solver(puzzle) match {
      case None =>
        println("No solution !")
      case Some(sol) =>
        println("Solution is:")
        println(SudokuPrinter(sol))
    }
  }

}
