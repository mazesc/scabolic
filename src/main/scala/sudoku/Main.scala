package sudoku

object Main {

  def main(args: Array[String]) {
    val puzzleInput = args(0)

    val puzzle = Parser.parse(new java.io.FileInputStream(puzzleInput))

    println(SudokuPrinter(puzzle))

  }

}
