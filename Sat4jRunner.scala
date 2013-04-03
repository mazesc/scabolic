import org.sat4j._ 
import org.sat4j.core._ 
import org.sat4j.specs._ 
import org.sat4j.reader._ 
import org.sat4j.minisat.SolverFactory._
import org.sat4j.minisat._
import java.io.File

object Sat4jRunner {

  def main(args: Array[String]) {

    val dir = new File(args(0))
    val benchmarks = recursiveListFiles(dir)
    benchmarks.foreach(f => {
      val solver: ISolver = SolverFactory.newDefault()
      solver.setTimeout(3600)
      val reader: Reader = new DimacsReader(solver)
      val problem: IProblem = reader.parseInstance(f.getPath)
      if(problem.isSatisfiable()) {
        println(" Satisfiable ! ")
      } else {
        println("unsat")
      }
    })
  }

  private def recursiveListFiles(f: File): Array[File] = {
    val these = f.listFiles
    these ++ these.filter(_.isDirectory).flatMap(recursiveListFiles)
  }

}
