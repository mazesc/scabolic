package regolic.asts.core

import regolic.asts.core.Trees._

object PrettyPrinter {

  def apply(formula: Formula): String = formulaPrinter(formula, _ => None, _ => None) 
  def apply(term: Term): String = termPrinter(term, _ => None, _ => None)

  def formulaPrinter(formula: Formula, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): String = dfp(formula) match {
    case Some(s) => s
    case None => formula match {
      case PredicateApplication(PredicateSymbol(s, _), Nil) => s
      case PredicateApplication(PredicateSymbol(s, _), ts) => ts.map(t => termPrinter(t, dfp, dtp)).mkString(s + "(", ", ", ")")
      case ConnectiveApplication(ConnectiveSymbol(s, _), Nil) => s
      case ConnectiveApplication(ConnectiveSymbol(s, _), fs) => fs.map(f => formulaPrinter(f, dfp, dtp)).mkString(s + "(", ", ", ")")
      case QuantifierApplication(QuantifierSymbol(s), v, f) => s + " " + termPrinter(v, dfp, dtp) + "(" + formulaPrinter(f, dfp, dtp) + ")"
    }
  }
  def termPrinter(term: Term, dfp: (Formula) => Option[String], dtp: (Term) => Option[String]): String = dtp(term) match {
    case Some(s) => s
    case None => term match {
      case FunctionApplication(FunctionSymbol(s, _, _), Nil) => s
      case FunctionApplication(FunctionSymbol(s, _, _), ts) => ts.map(t => termPrinter(t, dfp, dtp)).mkString(s + "(", ", ", ")")
      case TermQuantifierApplication(TermQuantifierSymbol(s, _, _), v, ts) => 
        s + " " + termPrinter(v, dfp, dtp) + ts.map(t => termPrinter(t, dfp, dtp)).mkString("(", ", ", ")")
      case Variable(n, _) => n
      case ITE(c, t, e) => "ite(" + formulaPrinter(c, dfp, dtp) + ", " + termPrinter(t, dfp, dtp) + ", " + termPrinter(e, dfp, dtp) + ")"
    }
  }

}


object SmtLib2 {

  import regolic.sexpr.SExprs._

  def toSExpr(f: Formula): SExpr = f match {
    case ConnectiveApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
    case PredicateApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
    case QuantifierApplication(sym, v, f) => sys.error("unsupported: " + f)
  }

  def toSExpr(t: Term): SExpr = t match {
    case FunctionApplication(sym, args) => SList(SSymbol(sym.name) :: args.map(toSExpr))
    case ITE(c, t, e) => SList(SSymbol("ite"), toSExpr(c), toSExpr(t), toSExpr(e))
    case Variable(name, _) => SSymbol(name)
    case TermQuantifierApplication(sym, v, ts) => sys.error("unsupported: " + t)
  }

  def apply(f: Formula): String = {
    regolic.sexpr.PrettyPrinter(toSExpr(f))
  }

}
