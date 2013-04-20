package regolic.sat

import regolic.Settings
import regolic.StopWatch

object Solver {

  /*
    This is a SAT solver, and I am trying to make it efficient, so don't expect nice functional code
    using immutable data and everything, this will be pure procedural code with many gloabl variables.
  */

  //Enumeration for the different status of the algorithm
  private sealed trait Status
  private case object Satisfiable extends Status
  private case object Unsatisfiable extends Status
  private case object Conflict extends Status
  private case object Unknown extends Status
  private case object Timeout extends Status

  /* The results, unknown means timeout */
  object Results {
    sealed trait Result
    case class Satisfiable(model: Array[Boolean]) extends Result
    case object Unsatisfiable extends Result
    case object Unknown extends Result
  }
  
  private[this] var nbConflicts = 0
  private[this] var nbDecisions = 0
  private[this] var nbPropagations = 0
  private[this] var nbLearntClauseTotal = 0
  private[this] var nbLearntLiteralTotal = 0
  private[this] var nbRemovedClauses = 0
  private[this] var nbRemovedLiteral = 0
  private[this] var nbRestarts = 0
         
  private[this] var decisionLevel = 0
  private[this] var trail: FixedIntStack = null
  private[this] var qHead = 0
  private[this] var reasons: Array[Clause] = null
  private[this] var levels: Array[Int] = null
  private[this] var conflict: Clause = null
  private[this] var model: Array[Int] = null
  private[this] var watched: Array[ClauseList] = null
  private[this] var cnfFormula: CNFFormula = null
  private[this] var status: Status = Unknown
  private[this] var restartInterval = Settings.restartInterval
  private[this] var nextRestart = restartInterval
  private[this] val restartFactor = Settings.restartFactor

  def solve(clauses: List[Clause], nbVars: Int): Results.Result = {

    val preprocessStopWatch = StopWatch("preprocess")
    val deduceStopWatch = StopWatch("deduce")
    val decideStopWatch = StopWatch("decide")
    val backtrackStopWatch = StopWatch("backtrack")
    val topLevelStopWatch = StopWatch("toplevelloop")
    
    nbConflicts = 0
    nbDecisions = 0
    nbPropagations = 0
    nbLearntClauseTotal = 0
    nbLearntLiteralTotal = 0
    nbRemovedClauses = 0
    nbRemovedLiteral = 0
    nbRestarts = 0

    status = Unknown
    conflict = null
    trail = new FixedIntStack(nbVars)
    qHead = 0
    model = Array.fill(nbVars)(-1)
    watched = Array.fill(2*nbVars)(new ClauseList(20))
    restartInterval = Settings.restartInterval
    nextRestart = restartInterval
    reasons = new Array(nbVars)
    levels = Array.fill(nbVars)(-1)
    decisionLevel = 0

    var newClauses: List[Clause] = Nil
    clauses.foreach(cl => {
      val litsUnique = cl.lits.toSet
      if(litsUnique.size == 1) {
        val id = litsUnique.head >> 1
        if(model(id) == -1)
          enqueueLiteral(litsUnique.head)
        else if(model(id) == (litsUnique.head & 1))
          status = Unsatisfiable
      }
      else if(!litsUnique.exists(l1 => litsUnique.count(l2 => (l2 >> 1) == (l1 >> 1)) > 1)) {
        val newLits = new Clause(litsUnique.toArray)
        newClauses ::= newLits
      }
    })
    cnfFormula = new CNFFormula(newClauses, nbVars)
    for(clause <- newClauses)
      recordClause(clause)
    deduceStopWatch.time {
      deduce()
    }
    if(status == Conflict)
      status = Unsatisfiable

    val timeout: Option[Int] = Settings.timeout
    var elapsedTime: Long = 0 //in ms
    //assertWatchedInvariant
    //assertTrailInvariant
    //MAIN LOOP
    topLevelStopWatch.time {
      while(status == Unknown) {
        val startTime = System.currentTimeMillis
        //assertWatchedInvariant
        //assertTrailInvariant
        decideStopWatch.time {
          decide()
        }

        var cont = true
        while(cont) {
          //assertWatchedInvariant
          //assertTrailInvariant
          deduceStopWatch.time {
            deduce()
          }

          if(status == Conflict) {
            backtrackStopWatch.time {
              backtrack()
            }
          } else {
            cont = false
          }
        }
        val endTime = System.currentTimeMillis
        elapsedTime += (endTime - startTime)
        timeout.foreach(timeout => if(elapsedTime > 1000*timeout) status = Timeout)
      }
    }

    if(Settings.stats) {
      println("Conflicts: " + nbConflicts)
      println("Decisions: " + nbDecisions)
      println("Propagations: " + nbPropagations + " ( " + nbPropagations/deduceStopWatch.seconds + " / sec)")
      println("Restarts: " + nbRestarts)
      println("Learned Literals: " + nbLearntLiteralTotal + " (" + nbLearntClauseTotal + " clauses) --- " + nbLearntLiteralTotal.toDouble/nbLearntClauseTotal.toDouble + " per clause")
      println("Removed Literals: " + nbRemovedLiteral + "(" + nbRemovedClauses + " clauses) --- " + nbRemovedLiteral.toDouble/nbRemovedClauses.toDouble + " per clause")
      println("Active Literals: " + (nbLearntLiteralTotal - nbRemovedLiteral) + "(" + (nbLearntClauseTotal - nbRemovedClauses) + ") --- " + (nbLearntLiteralTotal - nbRemovedLiteral).toDouble/(nbLearntClauseTotal-nbRemovedClauses).toDouble + " per clause")

      println("Time spend in:\n")
      println("  preprocess:           " + preprocessStopWatch.seconds + " sec")
      println("  toplevelloop:         " + topLevelStopWatch.seconds + " sec")
      println("    decide:             " + decideStopWatch.seconds + " sec")
      println("    deduce:             " + deduceStopWatch.seconds + " sec")
      println("    backtrack:          " + backtrackStopWatch.seconds + " sec")
    }

    status match {
      case Unknown | Conflict => sys.error("unexpected")
      case Timeout => Results.Unknown
      case Unsatisfiable => Results.Unsatisfiable
      case Satisfiable => Results.Satisfiable(model.map(pol => pol == 1))
    }
  }

  private[this] def conflictAnalysis: (Clause, Int) = if(decisionLevel == 0) (null, -1) else {
    assert(conflict != null)

    import scala.collection.mutable.Queue

    //the algorithm augment the cut closest to the conflict node successively by doing
    //a BFS while only searching through the nodes of the current decision level
    //it stops when only one node of the current decision level (the UIP) remain in the cut
    val seen: Array[Boolean] = Array.fill(cnfFormula.nbVar)(false) // default value of false
    var learntClause: List[Int] = Nil
    var p: Int = -1
    var c = 0
    var confl = conflict
    conflict = null

    //find 1-UIP
    do {
      if(p != -1)
        assert(p == (confl.lits(0) >> 1))
      cnfFormula.incVSIDSClause(confl)

      val lits = confl.lits
      var i = if(p == -1) 0 else 1
      while(i < lits.size) {
        //assert(isUnsat(lits(i)))
        val id = lits(i) >> 1
        val lvl = levels(id)
        if(!seen(id) && lvl > 0) {
          seen(id) = true
          if(lvl == decisionLevel)
            c += 1
          else
            learntClause ::= lits(i)
        }
        i += 1
      }

      assert(learntClause.forall(lit => levels(lit >> 1) != decisionLevel))

      do { //we already start undo the trail here, probably not the cleanest approach but if we are careful this should work, and this is more efficient
        if(p != -1) //p must be undo, except for the last one which we will need its value in the end
          undo(p)
        p = trail.pop()
      } while(!seen(p))

      c = c - 1

      confl = reasons(p)
      if(confl != null) {
        assert(confl.lits(0) >> 1 == p)
        assert(isSat(confl.lits(0)))
        assert(confl.lits.tail.forall(lit => isUnsat(lit)))
      }
    } while(c > 0)
    seen(p) = true
    trail.push(p) //need to keep p in the trail
    assert(model(p) != -1)
    //p is 1-UIP
    assert(learntClause.forall(lit => isUnsat(lit)))

    def getAbstractLevel(id: Int) = 1 << (levels(id) & 31)
    //clause minimalization
    var marked: Set[Int] = learntClause.map(_ >> 1).toSet
    val levelsInClause: Set[Int] = marked.map(levels(_)) //we can optimize the search, if we see a node of a level not in the set, then for sure there will be a decision node of the same level

    def litRedundant(id: Int, abstractLevel: Int): Boolean = {
      var stack = List(id)
      var analyzeToclear: List[Int] = Nil
      var res = true
      while(!stack.isEmpty && res) {
        val reasonClause = reasons(stack.head)
        stack = stack.tail

        reasonClause.lits.foreach(l => if((l>>1) != id && res) {
          val id = l>>1

          if(!seen(id) && levels(id) > 0) {
            if(reasons(id) != null && (getAbstractLevel(id) & abstractLevel) != 0) {
              seen(id) = true
              stack ::= id
              analyzeToclear ::= id
            } else {
              while(!analyzeToclear.isEmpty) {
                seen(analyzeToclear.head) = false;
                analyzeToclear = analyzeToclear.tail
              }
              res = false
            }
          }
        })
      }
      res
    }

    var absLevel: Int = 0
    learntClause.foreach(lit => absLevel |= getAbstractLevel(lit >> 1)) //maintain an abstract level

    learntClause = learntClause.filterNot(lit => {
      val reasonClause = reasons(lit >> 1) 
      reasonClause != null && litRedundant(lit >> 1, absLevel)
    })

    //compute backtrack level
    val backtrackLevel = if(learntClause.isEmpty) 0 else learntClause.map(lit => levels(lit >> 1)).max
    learntClause ::= (p + p + model(p))  //don't forget to add p in the clause !

    //TODO: why am I sorting this already ?
    (new Clause(learntClause.sortWith((lit1, lit2) => levels(lit1 >> 1) > levels(lit2 >> 1)).toArray), backtrackLevel)
  }

  def litToVar(lit: Int): Int = lit >> 1
  def litPolarity(lit: Int): Boolean = (lit & 1) == 0
  def isAssigned(lit: Int): Boolean = model(lit >> 1) != -1
  def isUnassigned(lit: Int): Boolean = model(lit >> 1) == -1
  def isSat(lit: Int): Boolean = (model(lit >> 1) ^ (lit & 1)) == 1
  def isUnsat(lit: Int): Boolean = (model(lit >> 1) ^ (lit & 1)) == 0


  //ignore size 1 for watched literal, they are never kept in the db
  class Clause(val lits: Array[Int]) {
    var activity: Double = 0d
    var locked = false
    def this(listLits: List[Literal]) = this(listLits.map(lit => lit.id + lit.id + (1 - lit.polInt)).toArray)
    val size = lits.size

    override def toString = lits.map(lit => (if(lit % 2 == 0) "" else "-") + (lit >> 1)).mkString("[", ", ", "]")
  }

  class CNFFormula(val originalClauses: List[Clause], val nbVar: Int) {
    require(originalClauses.forall(cl => cl.lits.forall(lit => lit >= 0 && lit < 2*nbVar)))
    require(originalClauses.forall(cl => cl.lits.size >= 2))
    require(originalClauses.forall(cl => cl.lits.forall(lit => cl.lits.count(l2 => (l2 >> 1) == (lit >> 1)) == 1)))

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
     * The decay mechanism is from MiniSAT, instead of periodically scaling down
     * each variable, it is equivalent to just augment the value of the increment, since
     * the scale down will not change any order and only the relative value are important.
     * We use doubles and we use the upper bound of 1e100 before scaling down everything, to
     * avoid reaching the limits of floating points.
     */

    private val VSIDS_DECAY: Double = 0.95
    private val VSIDS_CLAUSE_DECAY: Double = 0.999

    private var vsidsInc: Double = 1d
    private val vsidsDecay: Double = 1d/VSIDS_DECAY

    private var vsidsClauseInc: Double = 1d
    private val vsidsClauseDecay: Double = 1d/VSIDS_CLAUSE_DECAY

    val vsidsQueue = new FixedIntDoublePriorityQueue(nbVar)
    originalClauses.foreach(cl => cl.lits.foreach(lit => {
      vsidsQueue.incScore(lit >> 1, vsidsInc)
    }))

    def incVSIDS(id: Int) {
      val newScore = vsidsQueue.incScore(id, vsidsInc)
      if(newScore > 1e100)
        rescaleVSIDS()
    }

    def rescaleVSIDS() {
      vsidsQueue.rescaleScores(1e-100)
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
      assert(clause.size > 1)
      learntClauses ::= clause
      nbClauses += 1
      nbLearntClauses += 1
      for(lit <- clause.lits)
        incVSIDS(lit >> 1)
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

  private[this] def recordClause(cl: Clause) {
    watched(cl.lits(0)).prepend(cl)
    watched(cl.lits(1)).prepend(cl)
  }

  private[this] def unrecordClause(cl: Clause) {
    watched(cl.lits(0)).remove(cl)
    watched(cl.lits(1)).remove(cl)
  }


  private[this] def enqueueLiteral(lit: Int, from: Clause = null) {
    val id = lit >> 1
    val pol = (lit & 1) ^ 1
    assert(model(id) == -1)
    model(id) = pol
    trail.push(id)
    assert(model(id) != -1)
    reasons(id) = from
    if(from != null) {
      //assert(from.lits.head == lit)
      //assert(from.lits.tail.forall(lit => isAssigned(lit)))
      //assert(from.lits.tail.forall(lit => isUnsat(lit)))
      //assert(from.lits.tail.forall(lit => trail.contains(lit>>1)))
      from.locked = true
    }
    levels(id) = decisionLevel
  }

  private[this] def decide() {
    if(cnfFormula.vsidsQueue.isEmpty)
      status = Satisfiable
    else {
      var next = cnfFormula.vsidsQueue.deleteMax
      while(model(next) != -1 && !cnfFormula.vsidsQueue.isEmpty)
        next = cnfFormula.vsidsQueue.deleteMax
      if(model(next) == -1) {
        nbDecisions += 1
        decisionLevel += 1
        enqueueLiteral(2*next + (nbDecisions & 1))
      } else
        status = Satisfiable
    }
  }

  private[this] def backtrack() {
    nbConflicts += 1
    cnfFormula.decayVSIDS()
    cnfFormula.decayVSIDSClause()
    val (learntClause, backtrackLevel) = conflictAnalysis
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
        if(learntClause.size == 1) //since we do not learn the clause
          enqueueLiteral(learntClause.lits(0), learntClause)
        cnfFormula.augmentMaxLearnt()
      } else {
        assert(decisionLevel > backtrackLevel)
        backtrackTo(backtrackLevel)
        val lit = learntClause.lits.find(isUnassigned).get
        enqueueLiteral(lit, learntClause) //only on non restart
        //note that if the unitClause is of size 1, there will be an auto-reset to backtrack level 0 so this is correct as well
      }
      if(learntClause.size > 1) //we only learn if it is not unit, if it is unit, then it is processed via the unitClauses and its consequences is added at level 0 which is never forgot
        cnfFormula.learn(learntClause)
      status = Unknown
    }
  }


  private[this] def backtrackTo(lvl: Int) {
    while(decisionLevel > lvl && !trail.isEmpty) {
      val head = trail.pop()
      decisionLevel = levels(head)
      if(decisionLevel > lvl)
        undo(head)
      else {
        trail.push(head)
        assert(model(head) != -1)
      }
    }
    qHead = trail.size
    if(trail.isEmpty)
      decisionLevel = 0
  }

  private[this] def undo(id: Int) {
    assert(model(id) != -1)
    cnfFormula.vsidsQueue.insert(id)
    model(id) = -1
    levels(id) = -1
    val reasonClause = reasons(id)
    if(reasonClause != null) {
      reasonClause.locked = false
      reasons(id) = null
    }
  }

  private[this] def deduce() {

    while(qHead < trail.size && status != Conflict) {

      val forcedVar = trail(qHead)
      //negatedLit is the literals that are made false and need updating of watchers
      val negatedLit = forcedVar + forcedVar + model(forcedVar)
      assert(isAssigned(negatedLit))
      qHead += 1

      val ws = watched(negatedLit).iterator
      while(ws.hasNext() && status != Conflict) {
        val clause = ws.next()
        val lits = clause.lits

        if(!isAssigned(lits(0)) || isUnsat(lits(0))) {

          assert(lits(0) == negatedLit || lits(1) == negatedLit)
          if(lits(1) != negatedLit) {
            val tmp = lits(1)
            lits(1) = negatedLit
            lits(0) = tmp
          }
          assert(lits(1) == negatedLit)

          var i = 2
          var found = false
          while(!found && i < lits.size) {
            val l = lits(i)
            if(isUnassigned(l) || isSat(l))
              found = true
            else
              i += 1
          }
          if(found) {
            val tmp = lits(1)
            lits(1) = lits(i)
            lits(i) = tmp
            watched(lits(1)).prepend(clause)
            ws.remove()
          } else {
            if(isUnassigned(lits(0))) {
              nbPropagations += 1
              enqueueLiteral(lits(0), clause)
            } else if(isUnsat(lits(0))) { //TODO: we should be able to move this block before the inspection of the clause
              status = Conflict
              qHead == trail.size
              conflict = clause
              assert(conflict.lits.forall(lit => isUnsat(lit)))
            }
          }
        }
      }

    }

  }

  //some debugging assertions that can be introduced in the code to check for correctness

  //assert that there is no unit clauses in the database
  def assertNoUnits() {

    assert(qHead == trail.size) //we assume that all unit clauses queued have been processed

    for(clause <- cnfFormula.originalClauses ::: cnfFormula.learntClauses) {
      if(clause.lits.count(isUnassigned) == 1 && clause.lits.forall(lit => isUnassigned(lit) || isUnsat(lit))) {
        println("clause " + clause + " should be unit !")
        assert(false)
      }
    }

  }

  //assert the invariant of watched literal is correct
  def assertWatchedInvariant() {
    for(cl <- (cnfFormula.originalClauses ::: cnfFormula.learntClauses)) {
      if(!watched(cl.lits(0)).contains(cl)) {
        println("clause " + cl + " is not correctly watched on " + cl.lits(0))
        assert(false)
      }
      if(!watched(cl.lits(1)).contains(cl)) {
        println("clause " + cl + " is not correctly watched on " + cl.lits(1))
        assert(false)
      }
    }

    for(v <- 0 until cnfFormula.nbVar) {
      val posLit = 2*v + 0
      var it = watched(posLit).iterator
      while(it.hasNext()) {
        val cl = it.next()
        assert(cl.lits(0) == posLit || cl.lits(1) == posLit)
      }

      val negLit = 2*v + 1
      it = watched(negLit).iterator
      while(it.hasNext()) {
        val cl = it.next()
        assert(cl.lits(0) == negLit || cl.lits(1) == negLit)
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
      assert(model(head) != -1)
      lst ::= head
      
      if(reasons(head) != null) {
        assert(reasons(head).lits.forall(lit => 
          model(lit >> 1) != -1 ))
        assert(reasons(head).lits.tail.forall(lit => 
          trail.contains(lit>>1) ))
        assert(reasons(head).lits.forall(lit => 
          !seen(lit >> 1) ))
      }

      seen(head) = true
    }
    assert(currentLevel == 1 || currentLevel == 0)

    lst.foreach(i => trail.push(i))

  }

}
