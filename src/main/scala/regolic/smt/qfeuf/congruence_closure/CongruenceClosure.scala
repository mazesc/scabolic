package regolic.smt.qfeuf 

import regolic.smt.Solver
import regolic.smt.TheorySolver
import regolic.asts.core.Trees._
import regolic.asts.fol.Trees._

import scala.collection.mutable.Queue
import scala.collection.mutable.Stack
import scala.collection.mutable.Map
import scala.collection.mutable.HashMap
import scala.collection.mutable.ListBuffer
import scala.collection.mutable.ArrayBuffer

import regolic.StopWatch

import java.io._

//object FastCongruenceSolver extends Solver {
  //val logic = regolic.parsers.SmtLib2.Trees.QF_UF

  //def isSat(f: Formula): Pair[Boolean, Option[collection.immutable.Map[Formula, Set[Formula]]]] = {
    //val And(fs) = f

    //val neqs = Map[Formula, Formula]()
    //val transformedToEq: collection.immutable.Map[Formula, Formula] = fs.flatMap{
      //case eq@Equals(_, _) => Flattener(Currifier(eq)).map(l => (l, eq))
      //case Not(eq@Equals(_, _)) => {
        //val eqs = Flattener(Currifier(eq))
        //neqs(eqs.head) = eq
        //eqs.tail.map(l => (l, eq))
      //}
      //case _ => None
    //}.toMap
      
    //val transformedEqs = transformedToEq.keySet
    //val congruenceClosure = new CongruenceClosure
    //congruenceClosure.initialize(transformedEqs)
    //transformedEqs.foreach(congruenceClosure.merge)

    //val unsatTerms = neqs.keys.filter{
      //// Are two variables, which shouldn't be equal congruent?
      //case Equals(t1, t2) if congruenceClosure.areCongruent(t1, t2) => true
      //case _ => false
    //}.toList

    //// For each such inequality, get the explanation why it must be an equality
    //val explanations: collection.immutable.Map[Formula, Set[Formula]] = unsatTerms.map{
      //case eq@Equals((t1: Variable), (t2: Variable)) => (neqs(eq),
        //congruenceClosure.explain(t1, t2).withFilter{
            /*
             * Only use equalities between variables
             */
            //case Equals((v1: Variable), (v2: Variable)) => true
            //case _ => false
          //}.map(transformedToEq(_)))
    //}.toMap

    //if(unsatTerms.isEmpty)
      //(true, None) // TODO what consequences to return for T-propagation?
    //else
      //(false, Some(explanations))
  //}

//}


/*
 * Algorithm as described in "Fast congruence closure and extensions" by
 * Nieuwenhuis and Oliveras
 */
class CongruenceClosure extends TheorySolver {

  class Node(var next: Node, var data: Tuple3[Timestamp,Int,Formula])

  class LinkedList {
    var first: Node = null
    def +=(data: Tuple3[Timestamp, Int, Formula]) {
      val node = new Node(null, data)
      node.next = first
      first = node
    }

    def exists(pred: Tuple3[Timestamp,Int,Formula] => Boolean): Boolean = {
      var node = first
      while(node != null) {
        if(pred(node.data))
          return true
        node = node.next
      }
      return false
    }
    
    def find(pred: Tuple3[Timestamp,Int,Formula] => Boolean): Tuple3[Timestamp,Int,Formula] = {
      var node = first
      while(node != null) {
        if(pred(node.data))
          return node.data
        node = node.next
      }
      return null
    }

    def size: Int = {
      var retVal = 0
      var node = first
      while(node != null) {
        retVal += 1
        node = node.next
      }
      retVal
    }

    override def toString = {
      var retVal = ""
      var node = first
      while(node != null) {
        retVal += node.data +" ("+ node.data._1.isValid +") -> "
        node = node.next
      }
      retVal += "null"
      retVal
    }
  
  }


  val logic = regolic.parsers.SmtLib2.Trees.QF_UF
  
  var time: Double = 0.0f
  var reason: Formula = null
    
  private[this] var posLitList: Array[Array[Formula]] = null
  private[this] var negLitList: Array[Array[Formula]] = null

  private[this] val termToId = Map[Term, Int]()
  private[this] var idToTerm: Array[Term] = null

  private[this] val pendingMerges: Queue[Pair[Formula, Formula]] = Queue()
  private[this] var repr: Array[Int] = null
  private[this] val lookup: Map[(Int, Int), Pair[Timestamp, Formula]] = Map()
  private[this] var useList: Array[ListBuffer[Formula]] = null
  private[this] var classList: Array[ArrayBuffer[Int]] = null

  val iStack = new Stack[Pair[Int, Formula]]
  //Diseq, a hash table containing all currently true disequalities between
  //representatives
  //Maybe try representing diseq with a map or a 2-dimensional array
  // ListBuffer allows for robust iteration, while removing elements
  //private[this] var diseq: Array[ListBuffer[Tuple3[Timestamp,Int,Formula]]] = null
  private[this] var diseq: Array[LinkedList] = null

  //var negReason = Map[Formula, Formula]()

  private[this] var trigger: Formula = null

  private[this] val undoReprChangeStack = new HashMap[Formula, Stack[Tuple3[Int, Int, Int]]] {
    override def default(k: Formula) = {
      val v = Stack[Tuple3[Int, Int, Int]]()
      this += (k -> v)
      v
    }
  }
  private[this] val undoUseListStack = new HashMap[Formula, Stack[Tuple3[Formula, Int, Int]]] {
    override def default(k: Formula) = {
      val v = Stack[Tuple3[Formula, Int, Int]]()
      this += (k -> v)
      v
    }
  }
  private[this] val undoEdgesStack = new HashMap[Formula, Stack[Pair[Int, Int]]] {
    override def default(k: Formula) = {
      val v = Stack[Pair[Int, Int]]()
      this += (k -> v)
      v
    }
  }

  class Timestamp(private val height: Int, private val ctr: Int) {
    // check for containment should be O(1)
    def isValid = !invalidTimestamps.contains(this)
    override def toString: String = "[height: "+ height +", ctr: "+ ctr +"]"

    override def equals(other: Any): Boolean = other match{
      case that: Timestamp =>
        (that canEqual this) &&
        this.height == that.height &&
        this.ctr == that.ctr
      case _ => false
    }

    def canEqual(other: Any) = other.isInstanceOf[Timestamp]

    override def hashCode: Int = 41 * ( 41 + height) + ctr
  }
  private[this] val invalidTimestamps = collection.mutable.Set[Timestamp]()
  private[this] var currentTimestamp: Timestamp = null
  private[this] var ctr: Int = 0

  private[this] val pendingProofs: Queue[Pair[Int,Int]] = Queue()
  private[this] var eqClass: Array[Int] = null
  private[this] var proofStructure: Array[Int] = null
  private[this] var proofLabels: Array[Pair[Formula, Formula]] = null
  
  private[this] val sw = StopWatch("ccStopwatch")
  
  def extractVariables(t: Term) = t match {
    case Apply((c1: Variable), (c2: Variable)) => List(c1, c2)
    case Variable(_, _) => List(t)
    case _ => throw new Exception("Unexpected term "+ t)
  }
    
  var unsatheader = ""
  var satheader = ""
  def initialize(ls: Set[Formula]) {//I.e. constructor
    val terms = collection.mutable.Set[Term]()

    val pos = new HashMap[Term, collection.mutable.Set[Formula]] {
      override def default(k: Term) = {
        val v = collection.mutable.Set[Formula]()
        this += (k -> v)
        v
      }
    }
    val neg = new HashMap[Term, collection.mutable.Set[Formula]] {
      override def default(k: Term) = {
        val v = collection.mutable.Set[Formula]()
        this += (k -> v)
        v
      }
    }
    
    for(l <- ls) {
      l match {
        case Equals(t1, t2) => {
          terms ++= extractVariables(t1)
          terms ++= extractVariables(t2)
          if(t1.isInstanceOf[Variable] && t2.isInstanceOf[Variable]) {
            pos(t1) += l
            pos(t2) += l
          }
        }
        case Not(eq@Equals((t1: Variable), (t2: Variable))) => {
          // TODO 
          // We shouldn't add terms, which just exist in inequalities. Maybe
          // remove them in a preprocessing step. Not much we can do about it at
          // this point
          terms ++= extractVariables(t1)
          terms ++= extractVariables(t2)
          neg(t1) += l
          neg(t2) += l
        }
        case _ => throw new Exception("Unsupported formula type: "+ l)
      }
    }

    val numTerms = terms.size
    repr = new Array(numTerms)
    classList = new Array(numTerms)
    useList = new Array(numTerms)
    diseq = new Array(numTerms)
    proofStructure = new Array(numTerms)
    proofLabels = new Array(numTerms)
    posLitList = new Array(numTerms)
    negLitList = new Array(numTerms)

    eqClass = new Array(numTerms)

    idToTerm = new Array(numTerms)

    var id = -1
    for(t <- terms) {
      id += 1

      termToId += (t -> id)
      idToTerm(id) = t

      posLitList(id) = pos(t).toArray
      negLitList(id) = neg(t).toArray

      repr(id) = id
      classList(id) = ArrayBuffer()
      classList(id) += id
      useList(id) = ListBuffer()
      //diseq(id) = ListBuffer()
      diseq(id) = new LinkedList()

      proofStructure(id) = -1
      eqClass(id) = id
    }

    unsatheader = scala.io.Source.fromFile("unsat_header.txt").mkString
    satheader = scala.io.Source.fromFile("sat_header.txt").mkString
  }

  var fcnt = 0
  // Every call to setTrue needs to push a literal to the iStack, so that
  // backtracking is possible for each T-literal enqueued in the DPLL engine
  def setTrue(l: Formula): Option[Set[Formula]] = {
    //if(iStack.size > 0 && !isTrue(iStack.top._2))
      //println("BUG")
    println("setTrue: "+ l)
    trigger = l
    ctr += 1
    iStack.push((ctr, l))
    currentTimestamp = new Timestamp(iStack.size, ctr)

    val retVal = l match {
      case Equals(_,_) => {
        //merge(eq)
        val tmp = merge(l)
        tmp match {
          case None => None
          case _ => Some(Set.empty[Formula])
        }
      }
      case Not(Equals(t1,t2)) => {
        if(!areCongruent(t1, t2)) {
        assert(repr(termToId(t1)) != repr(termToId(t2)))
          val t1Id = termToId(t1); val t2Id = termToId(t2)
          diseq(repr(t1Id)) += Tuple3(currentTimestamp, repr(t2Id), trigger)
          diseq(repr(t2Id)) += Tuple3(currentTimestamp, repr(t1Id), trigger)

          // Computing the T-consequences
          val (a, b) = (repr(t1Id), repr(t2Id))
          val (cla, clb) = (classList(a), classList(b))
          val cl = if(cla.size < clb.size) cla else clb
          val tConsequence = ListBuffer[Formula]()
          for(c <- cl) {
            var nLits = negLitList(c)
            var i = 0
            while(i < nLits.size) {
              nLits(i) match {
                case Not(Equals(s1, s2)) => {
                  val s1Id = termToId(s1); val s2Id = termToId(s2)
                  if((repr(s1Id) == a && repr(s2Id) == b) ||
                     (repr(s1Id) == b && repr(s2Id) == a))
                    tConsequence += nLits(i)
                }
                case _ => ()
              }
              i += 1
            }
          }

          //negReason ++= tConsequence.map(ineq => (ineq, l))
          //println("negReason: "+ negReason.mkString("\n", "\n", "\n"))
          //Some(tConsequence.toSet)
          Some(Set.empty[Formula])
        } else {
          reason = Equals(t1, t2)

          None // inconsistent
        }
      }
    }
    //import regolic.asts.core.SmtLib2
    //retVal match {
      //case None => {
        //fcnt += 1
        //val fw = new FileWriter("settrue/out"+ fcnt +".smt2")
        //val head = unsatheader + "(assert\n(and\n"
        //var assertString = iStack.map(x => SmtLib2(x._2)).mkString("\n")
        //fw.write(head + assertString + "))\n(check-sat)\n(exit)")
        //fw.close
        //println("CONFLICT")
      //}
      //case Some(_) =>
        //fcnt += 1
        //val fw = new FileWriter("settrue/out"+ fcnt +".smt2")
        //val head = satheader + "(assert\n(and\n"
        //var assertString = iStack.map(x => SmtLib2(x._2)).mkString("\n")
        //fw.write(head + assertString + "))\n(check-sat)\n(exit)")
        //fw.close
        //println("NO CONFLICT")
    //}

    
    retVal
  }

  private def merge(eq: Formula): Option[Set[Formula]] = {
    eq match {
      case Equals(a: Variable, b: Variable) => {
        pendingMerges.enqueue((eq, null))
        propagate()
      }
      case Equals(Apply(a1, a2), a: Variable) => {
        val a1Id = termToId(a1); val a2Id = termToId(a2)
        val lookedUp = lookup.getOrElse((repr(a1Id), repr(a2Id)), null)
        if(lookedUp != null && lookedUp._1.isValid) {
          pendingMerges.enqueue((eq, lookedUp._2))
          propagate()
        } else {
          lookup += ((repr(a1Id), repr(a2Id)) -> (currentTimestamp, eq))
          useList(repr(a1Id)).append(eq)
          useList(repr(a2Id)).append(eq)
          Some(Set.empty[Formula]) // no new unions, no T-consequences
        }
      }
    }
  }

  private def propagate(): Option[Set[Formula]] = {
    val tConsequence = ListBuffer[Formula]()
    while(pendingMerges.nonEmpty) {
      val e = pendingMerges.dequeue()
      
      val toMerge = e match {
        case (Equals(a: Variable, b: Variable), null) => (termToId(a), termToId(b))
        case (Equals(_, a: Variable), Equals(_, b: Variable)) => (termToId(a), termToId(b))
      }
      val (a, b) = if(classList(repr(toMerge._1)).size > classList(repr(toMerge._2)).size){
        toMerge.swap
      } else toMerge

      // merge classes of a and b (a => b)
      println("merging: "+ idToTerm(a) +", repr: "+ idToTerm(repr(a)))
      println("and "+ idToTerm(b) +", repr: "+ idToTerm(repr(b)))
      if(repr(a) != repr(b)) {

        // trying to merge classes, which are disequal
        if(diseq(repr(a)).exists{case (t,v,_) => {t.isValid && repr(v) == repr(b)}}) {
          // If for some reason, the trigger literal causing this inconsistency
          // is not pushed onto the I-stack, make sure to set the timestamp
          // invalid here.
          // As it stands now, it gets taken care of in backtrack.
          reason = Not(Equals(idToTerm(repr(toMerge._1)), idToTerm(repr(toMerge._2))))
          //println("reason: "+ reason)
          return None
        }

        val oldreprA = repr(a)

        // Extension for equality explanation
        insertEdge(a, b, e)

        var i = 0
        val clOldreprA = classList(oldreprA)
        while(i < clOldreprA.size) {
          val c = clOldreprA(i)

          var pLits = posLitList(c)
          var j = 0
          while(j < pLits.size) {
            pLits(j) match {
              case Equals(t1, t2) => {
                val t1Id = termToId(t1); val t2Id = termToId(t2)
                if((repr(t1Id) == oldreprA && repr(t2Id) == repr(b)) ||
                   (repr(t1Id) == repr(b) && repr(t2Id) == oldreprA))
                  tConsequence += pLits(j)
                else ()
              }
              case _ => ()
            }
            j += 1
          }
          undoReprChangeStack(trigger).push((c, oldreprA, repr(b)))
          repr(c) = repr(b)
          classList(repr(b)).append(c)
          i += 1
        }
        classList(oldreprA).clear()

        var p: Node = diseq(oldreprA).first
        var q: Node = null
        while(p != null) {
          p.data match {
            case (t,v,reason1) if t.isValid => {
              // v hasn't changed its repr, because repr(v) must be different
              // from oldreprA, as it's in disequal(oldreprA)
              diseq(repr(b)) += Tuple3(currentTimestamp, v, reason1)
              q = p
              q.next = p.next
            }
            case _ => if(q != null) q.next = p.next else diseq(oldreprA).first = p.next
          }
          p = p.next
        }
        //for(d <- diseq(oldreprA)) {
          //d match {
            //case (t,v,reason1) if t.isValid => {
              //diseq(repr(b)) += Tuple3(currentTimestamp, v, reason1)
            //}
            //// Removing while iterating possible with ListBuffer
            //case _ => ()
          //}
        //}
        //diseq(oldreprA) = diseq(oldreprA).filter{case (t,_,_) => t.isValid}

        /*
        // TODO classList is empty here
        for(aP <- classList(oldreprA)) {
          tConsequence ++= negLitList(aP).filter{ineq => ineq match {
            case Not(Equals(t1, t2)) => {
              val t1Id = termToId(t1); val t2Id = termToId(t2)
              diseq(oldreprA).exists{case (t,v,_) => t.isValid && (repr(v) == repr(t1Id) || repr(v) == repr(t2Id))}
            }
          }}
        }
        */
        // optimized: 
        //i = 0
        //while(i < clOldreprA.size) {
          //var nLits = negLitList(clOldreprA(i))
          //var j = 0
          //while(j < nLits.size) {
            //nLits(j) match {
              //case Not(Equals(t1, t2)) => {
                //val t1Id = termToId(t1); val t2Id = termToId(t2)
                //if(diseq(oldreprA).exists{case (t,v,_) => t.isValid && (repr(v) == repr(t1Id) || repr(v) == repr(t2Id))})
                  //tConsequence += nLits(j)
                //else ()
              //}
              //case _ => ()
            //}
            //j += 1
          //}
          //i += 1
        //}

        /*
        for(bP <- classList(repr(b))) {
          tConsequence ++= negLitList(bP).filter{ineq => ineq match {
            case Not(Equals(t1, t2)) => {
              val t1Id = termToId(t1); val t2Id = termToId(t2)
              diseq(repr(b)).exists{case (t,v,_) => t.isValid && (repr(v) == repr(t1Id) || repr(v) == repr(t2Id))}
            }
          }}
        }
        */

        for(f1 <- useList(oldreprA)) {
          val Equals(Apply(c1, c2),_) = f1

          val c1Id = termToId(c1); val c2Id = termToId(c2)
          val lookedUp = lookup.getOrElse((repr(c1Id), repr(c2Id)), null)
          if(lookedUp != null && lookedUp._1.isValid) {
            undoUseListStack(trigger).push(Tuple3(f1, oldreprA, -1))
            pendingMerges.enqueue((f1, lookedUp._2))
          } else {
            lookup += ((repr(c1Id), repr(c2Id)) -> (currentTimestamp, f1))

            undoUseListStack(trigger).push(Tuple3(f1, oldreprA, repr(b)))
            useList(repr(b)).append(f1)
          }
        }
        useList(oldreprA).clear()
      } // if
    } // while
    Some(tConsequence.toSet)
  }
  
  def isTrue(l: Formula) = {
    val retVal = l match {
      case Equals(t1, t2) => {
        areCongruent(t1, t2)
      }
      case Not(Equals(t1, t2)) => {
        !areCongruent(t1, t2)
      }
    }

    retVal   
  }

  private def areCongruent(t1: Term, t2: Term): Boolean = {
    normalize(t1) == normalize(t2)
  }

  private def normalize(t: Term): Term = {
    t match {
      case c@Variable(_, _) => {
        if(termToId.contains(c)) idToTerm(repr(termToId(c))) else c
      }
      case Apply(t1, t2) => {
        val u1 = normalize(t1)
        val u2 = normalize(t2)
        if(u1.isInstanceOf[Variable] && u2.isInstanceOf[Variable]) {
          val lookedUp = lookup.getOrElse((termToId(u1), termToId(u2)), null)
          if(lookedUp != null && lookedUp._1.isValid) {
            val Equals(_, a) = lookedUp._2
            if(termToId.contains(a)) idToTerm(repr(termToId(a))) else a
          } else {
            Apply(u1, u2)
          }
        }
        else
          Apply(u1, u2)
        }
    }
  }

  private def undoMerge(l: Formula) {
   /*
    * Example: 
    *   a -> b -> c -> d
    *   insert b -> e:
    *     a -> b <- c <- d
    *          '-> e
    *     from = b
    *     reversedTo = d
    *   undo b -> e:
    *     a -> b -> c -> d
    */
    while(!undoEdgesStack(l).isEmpty) {
      val (from, reversedTo) = undoEdgesStack(l).pop
      removeEdge(from, reversedTo)
    }

    while(!undoReprChangeStack(l).isEmpty) {
      val (elem, oldRepr, newRepr) = undoReprChangeStack(l).pop
      repr(elem) = oldRepr
      classList(newRepr) -= elem
      classList(oldRepr).append(elem)
    }
    
    while(!undoUseListStack(l).isEmpty) {
      val (f, oldRepr, newRepr) = undoUseListStack(l).pop
      useList(oldRepr).prepend(f)
      if(newRepr != -1) {
        val index = useList(newRepr).indexWhere(_ == f)
        useList(newRepr).remove(index)
      }
    }
  
  }
  
  def backtrack(n: Int) {
    if(n <= iStack.size) {
      1 to n foreach { _ => {
        val (topCtr, topTrigger) = iStack.pop
        val delTimestamp = new Timestamp(iStack.size + 1, topCtr)
        invalidTimestamps += delTimestamp

        undoMerge(topTrigger)
      }}

      pendingMerges.clear()

    } else {
      throw new Exception("Can't pop "+ n +" literals from I-stack.")
    }
  }

  // l is the last literal popped
  def backtrackTo(l: Formula) {
    if(l != null) {
      var poppedLiteral: Formula = null
      do {
        val (topCtr, topTrigger) = iStack.pop
        poppedLiteral = topTrigger
        println("popping: "+ poppedLiteral)
        val delTimestamp = new Timestamp(iStack.size + 1, topCtr)
        invalidTimestamps += delTimestamp

        undoMerge(topTrigger)
      } while(poppedLiteral != l) 

      pendingMerges.clear()
    }
  }
  
  private def reverseEdges(from: Int) = {
    var p = from
    var q = -1
    var r = -1
    //var q: ProofStructureNode = null
    //var r: ProofStructureNode = null
    var qEdge: Pair[Formula, Formula] = null
    var rEdge: Pair[Formula, Formula] = null

    while(p != -1) {
      r = q
      q = p
      p = proofStructure(q)

      rEdge = qEdge
      qEdge = proofLabels(q)

      proofStructure(q) = r
      proofLabels(q) = rEdge
    }
    proofStructure(from) = -1
    q
  }

  // removes the edge from to from.parent and reverses the edges in order to
  // restore the state before the edge was inserted (mind the order of edge insertions)
  private def removeEdge(from: Int, reversedTo: Int) {
    // not clearing edge label is fine as parent is null anyhow
    proofStructure(from) = -1
    reverseEdges(reversedTo)
  }
  
  private def makeEdge(from: Int, to: Int, label: Pair[Formula, Formula]): Int =  {
    val retVal = reverseEdges(from)
    proofStructure(from) = to
    proofLabels(from) = label
    retVal
  }
  
  private def insertEdge(a: Int, b: Int, label: Pair[Formula, Formula]) = {
    val from = a
    val reversedTo = makeEdge(a, b, label)

    //println(node.mkString("digraph g {\nnode [shape=plaintext];\n", "\n", "\n}"))
    undoEdgesStack(trigger).push((from, reversedTo))
  }
  
  private def findEqClass(x: Int): Int = {
    if(eqClass(x) == x)
      x
    else
      findEqClass(eqClass(x))
  }

  private def computeHighestNode(c: Int): Int = {
    @annotation.tailrec
    def nestedComputeHighestNode(x: Int): Int = {
      if(proofStructure(x) == -1 || findEqClass(proofStructure(x)) != findEqClass(c)) 
        x
      else
        nestedComputeHighestNode(proofStructure(x))
    }
    nestedComputeHighestNode(c)
  }

  private def nearestCommonAncestor(a: Int, b: Int): Int = {
    @annotation.tailrec
    def pathToRoot(n: Int, acc: List[Int] = Nil): List[Int] = {
      if(proofStructure(n) != -1)
        pathToRoot(proofStructure(n), n :: acc)
      else
        n :: acc // Include root
    }

    @annotation.tailrec
    def commonPath(l1: List[Int], l2: List[Int], prev: Int): Int = {
      l1 match {
        case x :: xs => {
          l2 match {
            case y :: ys if x == y => commonPath(xs, ys, x)
            case _ => prev
          }
        }
        case Nil => prev
      }
    }

sw.time {
}
time += sw.seconds
sw.reset
    commonPath(pathToRoot(a), pathToRoot(b), -1)
  }

  // l is t-consequence of setTrue(lPrime)
  def explain(l: Formula, lPrime: Formula = null): Set[Formula] = {
    val restoreIStack = Stack[Pair[Int, Formula]]()
    if(lPrime != null) {
      // undo all merges after lPrime was pushed onto the iStack
      var j = 0
      while(iStack(j)._2 != lPrime) {
        restoreIStack.push(iStack(j))

        j += 1
        if(j == iStack.size)
          throw new Exception("lPrime was not pushed to iStack")
      }
      backtrack(j)
    }

    // actual explain computation
    val retVal = l match{
      case Equals((e1: Variable), (d1: Variable)) => {
        explain(termToId(e1), termToId(d1))
      }
      case Not(Equals((d1: Variable), (e1: Variable))) => {
        //println("negReason: "+ negReason.mkString("\n", "\n", "\n"))
        //val cause = negReason(l)
        // if valid
        // TODO
        val cause = diseq(repr(termToId(d1))).find{case (t,elem,_) => t.isValid && repr(elem) == repr(termToId(e1))}._3
        //println("cause: "+ cause)

        val Not(Equals((d2: Variable), (e2: Variable))) = cause

        // Checking for 1 congruence is enough. If d1 congruent e2 as well, that
        // would mean that d1 = d2 AND d1 = e2 AND d2 != e2, which is
        // inconsistent
        val d1Id = termToId(d1); val d2Id = termToId(d2)
        val e1Id = termToId(e1); val e2Id = termToId(e2)
        if(areCongruent(d1,d2)) {
          (explain(d1Id, d2Id) union explain(e1Id, e2Id)) + cause
        } else {
          (explain(d1Id, e2Id) union explain(e1Id, d2Id)) + cause
        }
      }
      case _ => throw new Exception("explain called on unsupported formula type "+ l)
    }


    if(lPrime != null) {
      // restore state after computing the explanation
      while(!restoreIStack.isEmpty) {
        val top = restoreIStack.pop
        ctr = top._1 - 1

        val validTimestamp = new Timestamp(iStack.size + 1, ctr + 1)
        invalidTimestamps -= validTimestamp

        setTrue(top._2)
      }
    }

    retVal
  }

  private def explain(c1: Int, c2: Int): Set[Formula] = {
    var id = -1
    var i = 0
    while(i < eqClass.size) {
      eqClass(i) = i
      i += 1
    }
    var explanation = new ListBuffer[Formula]
    pendingProofs.enqueue((c1, c2))

    while(pendingProofs.nonEmpty) {
      val (a, b) = pendingProofs.dequeue()
      val c = computeHighestNode(findEqClass(
        nearestCommonAncestor(a, b) match {
          case -1 => throw new Exception("No common ancestor "+ (idToTerm(a),idToTerm(b)))
          case x => x
        }
      ))
      explanation ++= explainAlongPath(a, c)
      explanation ++= explainAlongPath(b, c)
    }
    explanation.toSet
  }

  private def explainAlongPath(aL: Int, c: Int): ListBuffer[Formula] = {
    var explanation = new ListBuffer[Formula]
    var a = computeHighestNode(aL)
    while(a != c) {
      val b = proofStructure(a)
      proofLabels(a) match {
        case (eq@Equals(a: Variable, b: Variable), null) => explanation += eq
        case (Equals(fa@Apply(a1, a2), a: Variable),
              Equals(fb@Apply(b1, b2), b: Variable)) => {
          
          // commented out, because all the functions are added to the instance
          // for good anyhow, so no need to reuse them.
          //explanation += Equals(fa, a)
          //explanation += Equals(fb, b)

          pendingProofs.enqueue((termToId(a1), termToId(b1)))
          pendingProofs.enqueue((termToId(a2), termToId(b2)))
        }
        case _ => throw new Exception("Can't match edgeLabel "+ proofLabels(a))
      }
      // UNION
      eqClass(findEqClass(a)) = findEqClass(b)

      a = computeHighestNode(b)
    }
    explanation
  }

}

