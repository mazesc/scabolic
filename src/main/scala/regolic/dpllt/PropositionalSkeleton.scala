package regolic.dpllt

import regolic.sat.Literal
import regolic.sat.LiteralType
import regolic.sat.TLiteral
import regolic.sat.PropLiteral

import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import regolic.smt.qfeuf.Flattener
import regolic.smt.qfeuf.Currifier
import regolic.parsers.SmtLib2.Trees._

import scala.collection.mutable.ArrayBuffer

class Encoding {
  val id = collection.mutable.Map[Formula, Int]()
  // in cases where there are no transformations to the literals,
  // theory == theoryOrig
  val theory = new ArrayBuffer[Formula]()
  val theoryOrig = new ArrayBuffer[Formula]()

  val funEqs = collection.mutable.Set[Formula]()

  def setEquiv(id: Int, f: Formula, fOrig: Formula) {
    // Invariant, id is the amount of calls to setEquiv
    this.id += (f -> id)
    theory += f
    theoryOrig += fOrig
  }

  def get(f: Formula): Option[Int] = {
    this.id.get(f)
  }
}

object PropositionalSkeleton {

  def apply(formula: Formula): (Set[Set[Literal]], Encoding, Int,
    Map[LiteralType, Int]) = {
    import scala.collection.mutable.ListBuffer

    trait LiteralID {
      private var counter = -1
      def next = {
        counter += 1
        counter
      }

      def count = counter + 1

      def reset = {
        counter = -1
      }
    }
    object TLiteralID extends LiteralID
    object PropLiteralID extends LiteralID

    val constraints = new ListBuffer[Set[Literal]]

    val encoding = new Encoding

    // For each subformula, create a new representation and add the constraints
    // while returning the representation
    def rec(form: Formula): Literal = form match {
      case (f: PredicateApplication) => {
        val repr = f match {
          case Equals(_, _) => {
            val flat = Flattener(Currifier(f))
            val reprID = encoding.get(flat.head) match {
              case Some(reprID) => reprID
              case None => {
                val reprID = TLiteralID.next
                encoding.setEquiv(reprID, flat.head, f) 
                reprID
              }
            }
            encoding.funEqs ++= flat.tail
            new Literal(reprID, TLiteral)
          }
          case p@PropositionalVariable(_) => {
            val reprID = encoding.get(p) match {
              case Some(reprID) => reprID
              case None => {
                val reprID = PropLiteralID.next
                encoding.id(p) = reprID
                reprID 
              }
            }
            new Literal(reprID, PropLiteral)
          }
          case _ => throw new Exception("This type of literal hasn't been implemented yet: "+ f)
        }
        repr
      }
      case Not(f) => {
        val fRepr = rec(f)
        val repr = new Literal(PropLiteralID.next, PropLiteral)
        constraints += Set(repr.neg, fRepr.neg)
        constraints += Set(repr.pos, fRepr.pos)
        repr
      }
      case And(fs) => {
        val repr = new Literal(PropLiteralID.next, PropLiteral)
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(repr.neg, fRepr.pos)
        constraints += (repr.pos :: fsRepr.map(fRepr => fRepr.neg)).toSet
        repr
      }
      case Or(fs) => {
        val repr = new Literal(PropLiteralID.next, PropLiteral)
        val fsRepr = fs.map(f => rec(f))
        for(fRepr <- fsRepr)
          constraints += Set(repr.pos, fRepr.neg)
        constraints += (repr.neg :: fsRepr.map(fRepr => fRepr.pos)).toSet
        repr
      }
      case Implies(f1, f2) => {
        val repr = new Literal(PropLiteralID.next, PropLiteral)
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(repr.neg, f1Repr.neg, f2Repr.pos)
        constraints += Set(repr.pos, f1Repr.pos)
        constraints += Set(repr.pos, f2Repr.neg)
        repr
      }
      case Iff(f1, f2) => {
        val repr = new Literal(PropLiteralID.next, PropLiteral)
        val f1Repr = rec(f1)
        val f2Repr = rec(f2)
        constraints += Set(repr.neg, f1Repr.neg, f2Repr.pos)
        constraints += Set(repr.neg, f1Repr.pos, f2Repr.neg)
        constraints += Set(repr.pos, f1Repr.neg, f2Repr.neg)
        constraints += Set(repr.pos, f1Repr.pos, f2Repr.pos)
        repr
      }
      case _ => sys.error("Unhandled case in PropositionalSkeleton: " + form)
    }

    val repr = rec(formula)
    constraints += Set(repr.pos)

    for(c <- constraints)
      for(l <- c) {
        l.setOffset(l.actualType match {
          case TLiteral => 0
          case PropLiteral => TLiteralID.count
        })
      }

    val nbLitsPerType = Map[LiteralType,Int](
      TLiteral -> TLiteralID.count,
      PropLiteral -> PropLiteralID.count
    )
     
    (constraints.toSet, encoding, nbLitsPerType.values.sum, nbLitsPerType)
  }

}

