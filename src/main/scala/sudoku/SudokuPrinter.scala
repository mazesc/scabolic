package sudoku

object SudokuPrinter {

  def apply(sudoku: Array[Array[Option[Int]]]) =
    sudoku.map(row => row.map(opt => opt.getOrElse(" ")).mkString(" ")).mkString("\n")

}
