package regolic.sat

import regolic.asts.core.Trees._
import regolic.asts.core.Manip._
import regolic.asts.fol.Trees._
import regolic.asts.fol.Manip._

import regolic.Settings
import regolic.Stats

import scala.collection.mutable.HashSet

object DPLL extends Solver {

  /*
    This is a SAT solver, and I am trying to make it efficient, so don't expect nice functional code
    using immutable data and everything, this will be pure procedural code with many gloabl variables
    */

  def isSat(clauses: List[Formula]): Option[Map[PredicateApplication, Boolean]] = {
    null
  }
  
  //Statistics, should move them to the Stats object in some way
  private var nbConflicts = 0
  private var nbDecisions = 0
  private var nbPropagations = 0
  private var nbLearntClauseTotal = 0
  private var nbLearntLiteralTotal = 0
  private var nbRemovedClauses = 0
  private var nbRemovedLiteral = 0
  private var nbRestarts = 0

  private var decisionLevel = 0
  private var trail: FixedIntStack = null
  private var reasons: Array[Clause] = null
  private var levels: Array[Int] = null
  private var conflict: Clause = null
  private var unitClauses: List[(Clause, Literal)] = List()
  private var model: Array[Option[Boolean]] = null
  private var posWatched: Array[ClauseList] = null
  private var negWatched: Array[ClauseList] = null
  private var cnfFormula: CNFFormula = null
  private var status: Status = Unknown
  private var restartInterval = 32
  private var nextRestart = restartInterval
  private val restartFactor = 1.1

  def isSat(clauses: List[Clause], nbVars: Int): Option[Array[Boolean]] = {
    val (st, newClauses, forcedVars, oldVarToNewVar) = Stats.time("preprocess")(preprocess(clauses, nbVars))

    status = st
    if(status == Unknown) {
      //INITIALIZATION
      cnfFormula = newClauses
      trail = new FixedIntStack(cnfFormula.nbVar)
      model = Array.fill(cnfFormula.nbVar)(None)
      posWatched = Array.fill(cnfFormula.nbVar)(new ClauseList(20))
      negWatched = Array.fill(cnfFormula.nbVar)(new ClauseList(20))
      for(clause <- cnfFormula.originalClauses)
        recordClause(clause)
      restartInterval = 32
      nextRestart = restartInterval
      reasons = new Array(cnfFormula.nbVar)
      levels = Array.fill(cnfFormula.nbVar)(-1)

      //MAIN LOOP
      Stats.time("toplevelloop"){
        while(status == Unknown) {
          assertNoUnits
          assertWatchedInvariant
          assertTrailInvariant
          Stats.time("decide") {
            decide()
          }

          var cont = true
          while(cont) {
            assertWatchedInvariant
            assertTrailInvariant
            Stats.time("deduce") {
              deduce()
            }

            if(status == Conflict) {
              Stats.time("backtrack") {
                backtrack()
              }
            } else {
              cont = false
              assertNoUnits
            }
          }
        }
      }
    }

    val res = status match {
      case Unknown | Conflict => sys.error("unexpected")
      case Unsatisfiable => None
      case Satisfiable => {
        val completeModel: Array[Boolean] = new Array(nbVars)
        (0 until nbVars).foreach(i => forcedVars(i) match {
          case None => //then this is a new var
            val newId = oldVarToNewVar(i)
            completeModel(i) = model(newId).getOrElse(true)
          case Some(v) =>
            completeModel(i) = v
        })
        Some(completeModel)
      }
    }
    if(Settings.stats) {
      println("Conflicts: " + nbConflicts)
      println("Decisions: " + nbDecisions)
      println("Propagations: " + nbPropagations + " ( " + nbPropagations/Stats.getTime("deduce") + " / sec)")
      println("Restarts: " + nbRestarts)
      println("Learned Literals: " + nbLearntLiteralTotal + " (" + nbLearntClauseTotal + " clauses) --- " + nbLearntLiteralTotal.toDouble/nbLearntClauseTotal.toDouble + " per clause")
      println("Removed Literals: " + nbRemovedLiteral + "(" + nbRemovedClauses + " clauses) --- " + nbRemovedLiteral.toDouble/nbRemovedClauses.toDouble + " per clause")
      println("Active Literals: " + (nbLearntLiteralTotal - nbRemovedLiteral) + "(" + (nbLearntClauseTotal - nbRemovedClauses) + ") --- " + (nbLearntLiteralTotal - nbRemovedLiteral).toDouble/(nbLearntClauseTotal-nbRemovedClauses).toDouble + " per clause")

      println("Time spend in:\n")
      println("  preprocess:           " + Stats.getTime("preprocess") + " sec")
      println("  toplevelloop:         " + Stats.getTime("toplevelloop") + " sec")
      println("    decide:             " + Stats.getTime("decide") + " sec")
      println("    deduce:             " + Stats.getTime("deduce") + " sec")
      println("    backtrack:          " + Stats.getTime("backtrack") + " sec")
      println("      conflictAnalysis: " + Stats.getTime("backtrack.conflictAnalysis") + " sec")
    }
    res
  }
  def conflictAnalysis: (Clause, Int) = if(decisionLevel == 0) (null, -1) else {
    assert(conflict != null)

    import scala.collection.mutable.Queue

    //the algorithm augment the cut closest to the conflict node successively by doing
    //a BFS while only searching through the nodes of the current decision level
    //it stops when only one node of the current decision level (the UIP) remain in the cut
    val seen: Array[Boolean] = Array.fill(cnfFormula.nbVar)(false) // default value of false
    var learntClause: List[Literal] = Nil
    var p: Int = -1
    var c = 0
    var confl = conflict
    conflict = null

    //find 1-UIP
    do {
      cnfFormula.incVSIDSClause(confl)

      confl.lits.foreach(lit => {
        val id = lit.id
        val lvl = levels(id)
        val pol = !model(id).get
        if(!seen(id) && lvl > 0) {
          seen(id) = true
          if(lvl == decisionLevel)
            c += 1
          else
            learntClause ::= new Literal(id, pol)
        }
      })


      assert(learntClause.forall(lit => levels(lit.id) != decisionLevel))

      do { //we already start undo the trail here, probably not the cleanest approach but if we are careful this should work, and this is more efficient
        if(p != -1) //p must be undo, except for the last one which we will need its value in the end
          undo(p)
        p = trail.pop()
      } while(!seen(p))

      c = c - 1

      confl = reasons(p)
    } while(c > 0)
    seen(p) = true
    trail.push(p) //need to keep p in the trail
    //p is 1-UIP

    //clause minimalization
    var marked: Set[Int] = learntClause.map(_.id).toSet
    val levelsInClause: Set[Int] = marked.map(levels(_)) //we can optimize the search, if we see a node of a level not in the set, then for sure there will be a decision node of the same level
    def isDominated(lit: Int): Boolean = {
      val res = if(marked.contains(lit) || levels(lit) == 0) true else if(reasons(lit) == null || !levelsInClause.contains(lit)) false else {
        val reasonClause = reasons(lit)
        reasonClause.lits.forall(l => l.id == lit || isDominated(l.id))
      }
      if(res)
        marked += lit //for caching
      res
    }

    learntClause = learntClause.filterNot(lit => {
      val reasonClause = reasons(lit.id) 
      reasonClause != null && reasonClause.lits.forall(pre => isDominated(pre.id))
    })

    //compute backtrack level
    val backtrackLevel = if(learntClause.isEmpty) 0 else learntClause.map((lit: Literal) => levels(lit.id)).max
    learntClause ::= new Literal(p, !model(p).get)  //don't forget to add p in the clause !

    (new Clause(learntClause), backtrackLevel)
  }


  private sealed trait Status
  private case object Satisfiable extends Status
  private case object Unsatisfiable extends Status
  private case object Conflict extends Status
  private case object Unknown extends Status

  class Literal(val id: Int, val polarity: Boolean) {
    require(id >= 0)
    def value: Option[Boolean] = model(id)
    def isAssigned: Boolean = value != None
    def isUnassigned: Boolean = value == None
    def isSat: Boolean = isAssigned && !(value.get ^ polarity)
    def isUnsat: Boolean = isAssigned && (value.get ^ polarity)
    override def toString: String = (if(!polarity) "-" else "") + "v" + id
  }

  class Clause(val lits: List[Literal]) {
    var activity: Double = 0.
    var locked = false
    val size = lits.size

    //ignore size 1 for watched literal, they are never kept in the db

    var wl1: Literal = lits.head
    var wl2: Literal = if(size == 1) wl1 else lits(1)
    private var uwl: Literal = if(size == 3) lits(2) else null
    private var arrayLits: Array[Literal] = if(size > 3) lits.toArray else null
    private var wli1: Int = 0
    private var wli2: Int = 1

    //one of the watched lit is negated
    def watchedLitNeg(id: Int, node: ClauseList#Iterator) {
      val lit = if(id == wl1.id) wl1 else wl2
      assert(wl1 == lit || wl2 == lit)

      if(size == 2) {
        if(wl1.isUnsat && wl2.isUnsat) {
          status = Conflict
          conflict = this
        } else if(wl2.isUnassigned) {
          unitClauses ::= (this, wl2)
        } else if(wl1.isUnassigned) {
          unitClauses ::= (this, wl1)
        }
      } else if(size == 3) {
        if((uwl.isUnassigned || uwl.isSat) && lit == wl1) {
          val tmp = uwl
          uwl = wl1
          wl1 = tmp
          changedWatched(uwl, wl1, node)
        } else if((uwl.isUnassigned || uwl.isSat) && lit == wl2) {
          val tmp = uwl
          uwl = wl2
          wl2 = tmp
          changedWatched(uwl, wl2, node)
        } else if(wl1.isUnassigned) { 
          unitClauses ::= (this, wl1)
        } else if(wl2.isUnassigned) {
          unitClauses ::= (this, wl2)
        } else if(wl1.isUnsat && wl2.isUnsat) {
          status = Conflict
          conflict = this
        }
      } else {
        var newWatchedIndex = 0
        var found = false
        while(!found && newWatchedIndex < size) {
          val l = arrayLits(newWatchedIndex)
          if(newWatchedIndex != wli1 && newWatchedIndex != wli2 && !l.isUnsat)
            found = true
          else
            newWatchedIndex += 1
        }

        if(found) {
          if(wl1 == lit) {
            wl1 = arrayLits(newWatchedIndex) 
            wli1 = newWatchedIndex
          } else {
            wl2 = arrayLits(newWatchedIndex) 
            wli2 = newWatchedIndex
          }
          changedWatched(lit, arrayLits(newWatchedIndex), node)
        } else {
          val owl = if(wl1 == lit) wl2 else wl1
          if(owl.isUnassigned)
            unitClauses ::= (this, owl)
          else if(owl.isUnsat && status != Conflict) {
            status = Conflict
            conflict = this
          }
        }
      }
    }

    private def changedWatched(oldLit: Literal, newLit: Literal, node: ClauseList#Iterator) {
      node.remove()
    
      if(newLit.polarity)
        posWatched(newLit.id).prepend(this)
      else
        negWatched(newLit.id).prepend(this)
    }

    override def toString: String = lits.mkString(", ") + " | wl1: " + wl1 + ", wl2: " + wl2
  }

  class CNFFormula(val originalClauses: List[Clause], val nbVar: Int) {
    require(originalClauses.forall(cl => cl.lits.forall(lit => lit.id >= 0 && lit.id < nbVar)))
    require(originalClauses.forall(cl => cl.lits.size >= 2))
    require(originalClauses.forall(cl => cl.lits.forall(lit => cl.lits.count(_.id == lit.id) == 1)))

    private val nbProblemClauses: Int = originalClauses.size
    var nbClauses: Int = nbProblemClauses

    var learntClauses: List[Clause] = Nil
    var nbLearntClauses = 0

    private var maxLearnt: Int = nbClauses / 3
    private val maxLearntFactor: Double = 1.1

    def augmentMaxLearnt() {
      maxLearnt = (maxLearnt*maxLearntFactor + 1).toInt
    }

    /*
     * Next comes a bunch of stuff to maintain VSIDS scores for all variable.
     * we use two arrays, one for the score, sorted from highest to lowest and
     * associated with the corresponding id and polarity.
     * The second array is used as an index, to be able to find in constant time in
     * the vsids array the current score for a literal.
     * We decided to use an encoding from literal to index taking 2*id + pol, which
     * seems to be not optimal in scala because pol needs to be translated to an int
     * with an if-then-else anyway.
     *
     * I think this is better than using a heap/priority queue because there is no
     * insert during the actual execution, the inserts only comes at the beginning
     * when building the array, then the only two needed operations are incrementKey
     * and findMax, which can be both completed in O(1) (actually there is a loop in the
     * increment, but it should only swap sums locally).
     *
     * The initial construction is done without mainting the order and index, and once all
     * variables are counted, we apply a sort algorithm and then update the index with
     * one sweep. I believe this is more efficient than using the incrementKey.
     *
     * Finally the decay mechanism is from MiniSAT, instead of periodically scaling down
     * each variable, it is equivalent to just augment the value of the increment, since
     * the scale down will not change any order and only the relative value are important.
     * We use doubles and we use the upper bound of 1e100 before scaling down everything, to
     * avoid reaching the limits of floating points.
     */

    private val VSIDS_DECAY: Double = 0.95
    private val VSIDS_CLAUSE_DECAY: Double = 0.999

    private var vsidsInc: Double = 1.
    private val vsidsDecay: Double = 1./VSIDS_DECAY

    private var vsidsClauseInc: Double = 1.
    private val vsidsClauseDecay: Double = 1./VSIDS_CLAUSE_DECAY

    //we only wants to init the VSIDS sum to 0, the (Int, Boolean) literal will get
    //update in the following
    val vsids: Array[(Int, Boolean, Double)] = Array.fill(2*nbVar)(0, false, 0)
    //init the VSIDS array
    originalClauses.foreach(cl => cl.lits.foreach(lit => {
      val index = litToIndex(lit.id, lit.polarity)
      vsids(index) = (lit.id, lit.polarity, vsids(index)._3 + vsidsInc)
    }))
    //and now sort it, we only do that for the initial preprocessing
    scala.util.Sorting.quickSort(vsids)(new Ordering[(Int, Boolean, Double)] { 
      def compare(e1: (Int, Boolean, Double), e2: (Int, Boolean, Double)): Int = (e2._3 - e1._3).toInt
    })
    //now create an index for these variables
    private val vsidsIndex: Array[Int] = new Array(2*nbVar)
    vsids.zipWithIndex.foreach{
      case ((id, pol, _), i) =>
        val index = litToIndex(id, pol)
        vsidsIndex(index) = i
    }

    //invariant is true initially
    assert(invariantVSIDS)

    private def invariantVSIDS: Boolean = {
      vsids.zipWithIndex.zip(vsids.tail).forall{
        case (((id, pol, sum1), i), (_, _, sum2)) => 
          val b = sum1 >= sum2 && i == vsidsIndex(litToIndex(id, pol))
          if(!b) println((id, pol, sum1, sum2, i, litToIndex(id, pol)))
          b
      }
    }

    private def litToIndex(id: Int, pol: Boolean): Int = 2*id + (if(pol) 1 else 0)

    //this gets called for each learned literal, need to maintain the index and the ordered array
    def incVSIDS(id: Int, pol: Boolean) {
      val index = litToIndex(id, pol)
      val indexInSorted = vsidsIndex(index)
      val (id2, pol2, sum) = vsids(indexInSorted)
      assert(id2 == id)
      assert(pol2 == pol)
      val newSum = sum + vsidsInc

      if(indexInSorted == 0) vsids(indexInSorted) = (id, pol, newSum) else {
        var newIndex = indexInSorted
        var t = vsids(newIndex-1)
        while(newIndex != 0 && t._3 < newSum) {
          vsids(newIndex) = t
          vsidsIndex(litToIndex(t._1, t._2)) = newIndex
          newIndex -= 1
          if(newIndex != 0)
            t = vsids(newIndex-1)
        }
        vsids(newIndex) = (id, pol, newSum)
        vsidsIndex(index) = newIndex
      }

      if(newSum > 1e100) {
        rescaleVSIDS()
      }

    }

    def rescaleVSIDS() {
      var i = 0
      val size = vsids.size
      while(i < size) {
        val (id, pol, v) = vsids(i)
        vsids(i) = (id, pol, v*1e-100)
        i += 1
      }
      vsidsInc *= 1e-100
    }
    def decayVSIDS() {
      vsidsInc *= vsidsDecay
    }


    def incVSIDSClause(cl: Clause) {
      cl.activity = cl.activity + vsidsClauseInc
      if(cl.activity > 1e100)
        rescaleVSIDSClause()
    }
    def rescaleVSIDSClause() {
      for(cl <- learntClauses)
        cl.activity = cl.activity*1e-100
      vsidsClauseInc *= 1e-100
    }
    def decayVSIDSClause() {
      vsidsClauseInc *= vsidsClauseDecay
    }

    def learn(clause: Clause) {
      println("learning: " + clause)
      assert(clause.size > 1)
      learntClauses ::= clause
      nbClauses += 1
      nbLearntClauses += 1
      for(lit <- clause.lits)
        incVSIDS(lit.id, lit.polarity)
      incVSIDSClause(clause)
      if(!clause.lits.tail.isEmpty)//only record if not unit
        recordClause(clause)
      nbLearntClauseTotal += 1
      nbLearntLiteralTotal += clause.lits.size
      if(nbLearntClauses > maxLearnt)
        reduceLearntClauses()
    }

    def reduceLearntClauses() {
      val sortedLearntClauses = learntClauses.sortWith((cl1, cl2) => cl1.activity < cl2.activity)
      val (forgotenClauses, keptClauses) = sortedLearntClauses.splitAt(maxLearnt/2)
      learntClauses = keptClauses
      for(cl <- forgotenClauses) {
        if(!cl.locked) {
          unrecordClause(cl)
          nbClauses -= 1
          nbLearntClauses -= 1
          nbRemovedClauses += 1
          for(lit <- cl.lits)
            nbRemovedLiteral += 1
        } else {
          learntClauses ::= cl
        }
      }
    }

    override def toString: String = (learntClauses ++ originalClauses).mkString("{\n", "\n", "\n}")
  }

  def recordClause(cl: Clause) {
    if(cl.wl1.polarity)
      posWatched(cl.wl1.id).prepend(cl)
    else
      negWatched(cl.wl1.id).prepend(cl)

    if(cl.wl2.polarity)
      posWatched(cl.wl2.id).prepend(cl)
    else
      negWatched(cl.wl2.id).prepend(cl)
  }

  def unrecordClause(cl: Clause) {
    if(cl.wl1.polarity)
      posWatched(cl.wl1.id).remove(cl)
    else
      negWatched(cl.wl1.id).remove(cl)

    if(cl.wl2.polarity)
      posWatched(cl.wl2.id).remove(cl)
    else
      negWatched(cl.wl2.id).remove(cl)
  }


  def set(id: Int, b: Boolean) {
    assert(model(id) == None)
    model(id) = Some(b)

    if(b) {
      val it = negWatched(id).iterator
      while(it.hasNext()) {
        val head = it.next()
        head.watchedLitNeg(id, it)
      }
    } else {
      var it = posWatched(id).iterator
      while(it.hasNext()) {
        val head = it.next()
        head.watchedLitNeg(id, it)
      }
    }
  }


  def decide() {
    nbDecisions += 1

    var lit: Option[(Int, Boolean)] = None
    var i = 0
    val size = cnfFormula.vsids.size
    while(lit == None && i < size) {
      val (id, pol, top) = cnfFormula.vsids(i)
      if(model(id) == None)
        lit = Some((id, pol))
      i += 1
    }

    if(lit == None) {
      status = Satisfiable
    } else {
      val fLit = lit.get
      decisionLevel += 1
      trail.push(fLit._1)
      assert(levels(fLit._1) == -1)
      levels(fLit._1) = decisionLevel
      set(fLit._1, fLit._2)
    }
  }

  def backtrack() {
    nbConflicts += 1
    cnfFormula.decayVSIDS()
    cnfFormula.decayVSIDSClause()
    val (learnedClause, backtrackLevel) = Stats.time("backtrack.conflictAnalysis")(conflictAnalysis)
    if(backtrackLevel == -1)
      status = Unsatisfiable
    else {
      if(nbConflicts == nextRestart) {
        if(Settings.stats) {
          println("restart after " + nbConflicts + " nb conflicts")
        }
        restartInterval = (restartInterval*restartFactor).toInt
        nextRestart = nbConflicts + restartInterval
        nbRestarts += 1
        backtrackTo(0)
        if(learnedClause.size == 1) //since we do not learn the clause
          unitClauses ::= ((learnedClause, learnedClause.lits.head))
        cnfFormula.augmentMaxLearnt()
      } else {
        assert(decisionLevel > backtrackLevel)
        backtrackTo(backtrackLevel)
        unitClauses ::= ((learnedClause, learnedClause.lits.find(_.isUnassigned).get)) //only on non restart
        //note that if the unitClause is of size 1, there will be an auto-reset to backtrack level 0 so this is correct as well
      }
      if(learnedClause.size > 1) //we only learn if it is not unit, if it is unit, then it is processed via the unitClauses and its consequences is added at level 0 which is never forgot
        cnfFormula.learn(learnedClause)
      status = Unknown
    }
  }


  def backtrackTo(lvl: Int) {
    while(decisionLevel > lvl && !trail.isEmpty) {
      val head = trail.pop()
      decisionLevel = levels(head)
      if(decisionLevel > lvl)
        undo(head)
      else
        trail.push(head)
    }
    if(trail.isEmpty)
      decisionLevel = 0
  }

  def undo(id: Int) {
    assert(model(id) != None)
    model(id) = None
    levels(id) = -1
    val reasonClause = reasons(id)
    if(reasonClause != null) {
      reasonClause.locked = false
      reasons(id) = null
    }
  }

  def deduce() {
    while(unitClauses != Nil && status != Conflict) {
      val (unitClause, forcedLit) = unitClauses.head
      unitClauses = unitClauses.tail
      if(forcedLit.isUnassigned) { //could no longer be true since many variables are forwarded
        println("forcing: " + forcedLit + " from clause: " + unitClause)
        assert(unitClause.lits.forall(lit => (lit == forcedLit) || lit.isUnsat))
        assert(unitClause.lits.forall(lit => (lit == forcedLit) || (trail.contains(lit.id))))

        trail.push(forcedLit.id)
        reasons(forcedLit.id) = unitClause
        levels(forcedLit.id) = decisionLevel
        unitClause.locked = true

        set(forcedLit.id, forcedLit.polarity)
        nbPropagations += 1
      }
    }
    unitClauses = Nil //if we stopped because of a conflict, we clear the list of unit clauses
  }


  //if a var only appear with the same polarity then set it to be true
  //all unit clause are eliminated and the corresponding variables deleted
  //keep a map from original var id to new ones
  //must also ensure that in each clause at most one occurence of the same variable can occur
  private def preprocess(clauses: List[Clause], nbVars: Int): (Status, CNFFormula, Array[Option[Boolean]], Array[Int]) = {
    var conflictDetected = false
    var forcedVars: Array[Option[Boolean]] = Array.fill(nbVars)(None) //list of variable that are forced to some value
    //force a var to a pol, record the information into the forcedVars array, may detect a conflict
    def force(id: Int, pol: Boolean) {
      forcedVars(id) match {
        case None => forcedVars(id) = Some(pol)
        case Some(p) if(p != pol) => conflictDetected = true
        case _ => //here it was already forced at the same polarity
      }
    }
    def isForced(id: Int): Boolean = forcedVars(id) != None

    var oldClauses: List[List[Literal]] = clauses.map(_.lits)
    var newClauses: List[List[Literal]] = Nil

    //first we eliminate duplicate in the same clause as well as clauses containing both polarity
    //of same variable. This is only needed once
    for(clause <- oldClauses) {
      val varOccurences: Array[Option[Boolean]] = Array.fill(nbVars)(None)
      var newLits: List[Literal] = Nil
      var ignoreClause = false
      for(lit <- clause) {
        varOccurences(lit.id) match {
          case None => 
            varOccurences(lit.id) = Some(lit.polarity)
            newLits ::= lit
          case Some(p) if(p != lit.polarity) => ignoreClause = true
          case _ => //ignore lit
        }
      }
      if(!ignoreClause)
        newClauses ::= newLits
    }


    oldClauses = newClauses
    newClauses = Nil
    var needRecheck = true
    while(needRecheck && !conflictDetected) {
      needRecheck = false //this flag is only set to true when a change really require to redo the counting and everything

      //first we count all occurence in the current situation and the unit clauses
      val varsCounters: Array[(Int, Int)] = Array.fill(nbVars)((0, 0))
      for(clause <- oldClauses) {
        var nbLits = 0
        for(lit <- clause) {
          nbLits += 1
          val counters = varsCounters(lit.id)
          if(lit.polarity)
            varsCounters(lit.id) = (counters._1 + 1, counters._2)
          else
            varsCounters(lit.id) = (counters._1, counters._2 + 1)
        }
        if(nbLits == 1)
          force(clause.head.id, clause.head.polarity)
      }

      //here we detect the same polarity occurence and fill forcedVariables
      varsCounters.zipWithIndex.foreach(arg => {
        val ((posCount, negCount), id) = arg
        if(posCount == 0 && negCount == 0)
          forcedVars(id) = Some(forcedVars(id).getOrElse(true))
        else if(negCount == 0)
          force(id, true)
        else if(posCount == 0)
          force(id, false)
      })

      //finally we apply all forced variables
      for(clause <- oldClauses) {
        var newLits: List[Literal] = Nil
        var ignoreClause = false
        for(lit <- clause) {
          forcedVars(lit.id) match {
            case None => newLits ::= lit
            case Some(p) if(p == lit.polarity) => ignoreClause = true
            case _ => //just ignore the literal
          }
        }
        if(ignoreClause) {
          //the clause can be remove, we will need to recheck for global effects
          needRecheck = true
        } else {
          newLits match {
            case Nil => conflictDetected = true //each literal of the clause were set to false
            case lit::Nil => //we identified a new unit clause, we need to redo the loop
              needRecheck = true
              newClauses ::= newLits
            case _ => newClauses ::= newLits
          }
        }
      }

      oldClauses = newClauses
      newClauses = Nil
    }

    if(conflictDetected)
      (Unsatisfiable, null, null, null)
    else if(oldClauses.isEmpty)
      (Satisfiable, null, forcedVars, null)
    else {
      val oldVarToNewVar: Array[Int] = new Array(nbVars)
      val newVarToOldVar = new scala.collection.mutable.ArrayBuffer[Int]
      var nbVarsRemoved = 0 //will be used as a shifter for the variable id
      (0 until nbVars).foreach(i => if(isForced(i)) nbVarsRemoved += 1 else {
        oldVarToNewVar(i) = i - nbVarsRemoved
        newVarToOldVar += i
      })
      val finalClauses: List[Clause] = oldClauses.map(clause => new Clause(clause.map(lit => new Literal(oldVarToNewVar(lit.id), lit.polarity))))
      val newNbVars = nbVars - nbVarsRemoved
      (Unknown, new CNFFormula(finalClauses, newNbVars), forcedVars, oldVarToNewVar)
    }
  }


  private class FixedIntStack(size: Int) {
    private val stack: Array[Int] = new Array(size)
    private var topIndex: Int = -1

    def push(el: Int) {
      topIndex += 1
      stack(topIndex) = el
    }
    def pop(): Int = {
      val res = stack(topIndex)
      topIndex -= 1
      res
    }
    def top: Int = stack(topIndex)
    def isEmpty: Boolean = topIndex == -1
    def contains(el: Int): Boolean = {
      var i = topIndex
      while(i >= 0) {
        if(stack(i) == el)
          return true
        i -= 1
      }
      false
    }
  }

  

  //some debugging assertions that can be introduced in the code to check for correctness

  //assert that there is no unit clauses in the database
  def assertNoUnits() {

    assert(unitClauses.isEmpty) //we assume that all unit clauses queued have been processed

    for(clause <- cnfFormula.originalClauses ::: cnfFormula.learntClauses) {
      if(clause.lits.count(_.isUnassigned) == 1 && clause.lits.forall(lit => lit.isUnassigned || lit.isUnsat)) {
        println("clause " + clause + " should be unit !")
        assert(false)
      }
    }

  }

  //assert the invariant of watched literal is correct
  def assertWatchedInvariant() {
    for(cl <- (cnfFormula.originalClauses ::: cnfFormula.learntClauses)) {
      if(cl.wl1.polarity) {
        if(!posWatched(cl.wl1.id).contains(cl)) {
          println("clause " + cl + " is not correctly watched on " + cl.wl1)
          println(posWatched(cl.wl1.id))
          assert(false)
        }
      } else {
        assert(negWatched(cl.wl1.id).contains(cl))
      }

      if(cl.wl2.polarity)
        assert(posWatched(cl.wl2.id).contains(cl))
      else
        assert(negWatched(cl.wl2.id).contains(cl))
    }

    for(v <- 0 until cnfFormula.nbVar) {
      var it = posWatched(v).iterator
      while(it.hasNext()) {
        val cl = it.next()
        assert((cl.wl1.id == v && cl.wl1.polarity) || (cl.wl2.id == v && cl.wl2.polarity))
      }

      it = negWatched(v).iterator
      while(it.hasNext()) {
        val cl = it.next()
        assert((cl.wl1.id == v && !cl.wl1.polarity) || (cl.wl2.id == v && !cl.wl2.polarity))
      }

    }
  }

  def assertTrailInvariant() {
    val seen: Array[Boolean] = Array.fill(cnfFormula.nbVar)(false) // default value of false
    var lst: List[Int] = Nil
    var currentLevel = decisionLevel

    while(!trail.isEmpty) {
      val head = trail.pop()
      if(levels(head) == currentLevel - 1)
        currentLevel -= 1
      else {
       assert(levels(head) == currentLevel)
      }
      assert(model(head) != None)
      lst ::= head
      
      if(reasons(head) != null)
        assert(reasons(head).lits.forall(lit => !seen(lit.id)))

      seen(head) = true
    }
    assert(currentLevel == 1 || currentLevel == 0)

    lst.foreach(i => trail.push(i))

  }

    //def toDotString: String = {
    //  var res = "digraph {\n"

    //  res += nodes.map(n => if(n==null) "" else n match {
    //    case DecisionNode(id, pol, level) => id + " [label=\"" + (if(pol) "" else "-") + id + " @" + level + "\" color=blue];"
    //    case ConsequenceNode(id, pol, level) => id + " [label=\"" + (if(pol) "" else "-") + id + " @" + level + "\" color=green];"
    //    case ConflictNode(_) => "C"
    //  }).mkString("\n")
    //  res += "\n"

    //  def printNode(n: Node): String = n match {
    //    case DecisionNode(id, _, _) => id.toString
    //    case ConsequenceNode(id, _, _) => id.toString
    //    case ConflictNode(_) => "C"
    //  }
    //  
    //  res += nodes.map(n => if(n == null) "" else {
    //    n.outs.map(out => printNode(n) + " -> " + printNode(out) + ";").mkString("\n")
    //  }).mkString("\n")

    //  res += "\n}"
    //  res
    //}

}
