package regolic.sat

import org.scalatest.FunSuite

class FixedIntDoublePriorityQueueSuite extends FunSuite {


  test("incScore and max") {
    val q1 = new FixedIntDoublePriorityQueue(7)
    assert(q1.size == 7)
    q1.incScore(3, 1.25)
    q1.incScore(2, 1.)
    q1.incScore(6, 2.)
    q1.incScore(3, 1.)
    q1.incScore(0, 0.5)
    q1.incScore(1, 1.5)
    q1.incScore(4, 0.7)
    assert(q1.invariant)
    assert(q1.max == 3)
    assert(q1.size == 7)

    val q2 = new FixedIntDoublePriorityQueue(8)
    assert(q1.size == 7)
    q2.incScore(7, 1.25)
    q2.incScore(0, 0.5)
    q2.incScore(2, 1.)
    q2.incScore(6, 2.)
    q2.incScore(3, 1.)
    q2.incScore(1, 1.5)
    q2.incScore(4, 0.7)
    q2.incScore(0, 1.7)
    q2.incScore(2, 1.6)
    q2.incScore(3, 1.7)
    assert(q1.size == 7)
    assert(q2.invariant)
    assert(q2.max == 3)
  }

  test("deleteMax") {
    val q1 = new FixedIntDoublePriorityQueue(7)
    assert(q1.size == 7)
    q1.incScore(3, 1.25)
    q1.incScore(2, 1.)
    q1.incScore(6, 2.)
    q1.incScore(3, 1.)
    q1.incScore(0, 0.5)
    q1.incScore(1, 1.5)
    q1.incScore(4, 0.7)
    assert(q1.invariant)
    assert(q1.size == 7)
    assert(q1.deleteMax == 3)
    assert(q1.invariant)
    assert(q1.size == 6)
    assert(q1.deleteMax == 6)
    assert(q1.invariant)
    assert(q1.size == 5)

    val q2 = new FixedIntDoublePriorityQueue(8)
    assert(q2.size == 8)
    q2.incScore(7, 1.25)
    q2.incScore(0, 0.5)
    q2.incScore(2, 1.)
    q2.incScore(6, 2.)
    q2.incScore(3, 1.)
    q2.incScore(1, 1.5)
    q2.incScore(4, 0.7)
    q2.incScore(0, 1.7)
    q2.incScore(2, 1.6)
    q2.incScore(3, 1.7)
    assert(q2.size == 8)
    assert(q2.invariant)
    assert(q2.deleteMax === 3)
    assert(q2.size === 7)
    assert(q2.invariant)
    assert(q2.deleteMax === 2)
    assert(q2.size === 6)
    assert(q2.invariant)
    assert(q2.deleteMax === 0)
    assert(q2.size === 5)
    assert(q2.invariant)

    val q3 = new FixedIntDoublePriorityQueue(8)
    assert(q3.size == 8)
    q3.incScore(7, 1.25)
    q3.incScore(0, 0.5)
    q3.incScore(2, 1.)
    q3.incScore(6, 2.)
    q3.incScore(3, 1.)
    q3.incScore(1, 1.5)
    q3.incScore(4, 0.7)
    q3.incScore(0, 1.7)
    q3.incScore(2, 1.6)
    q3.incScore(3, 1.7)
    assert(q3.size == 8)
    assert(q3.invariant)
    assert(q3.deleteMax === 3)
    assert(q3.size === 7)
    assert(q3.invariant)
    assert(q3.deleteMax === 2)
    assert(q3.size === 6)
    assert(q3.invariant)
    assert(q3.deleteMax === 0)
    assert(q3.size === 5)
    assert(q3.invariant)
    q3.incScore(1, 1.4)
    q3.incScore(2, 2.2)
    assert(q3.invariant)
    assert(q3.size === 5)
    assert(q3.deleteMax === 1)
    assert(q3.size === 4)
    assert(q3.invariant)
  }

  test("empty queue") {
    val q1 = new FixedIntDoublePriorityQueue(4)
    q1.incScore(3, 1.25)
    q1.incScore(2, 1.)
    q1.incScore(0, 0.5)
    q1.incScore(1, 1.5)
    assert(!q1.isEmpty)
    assert(q1.invariant)
    assert(q1.deleteMax === 1)
    assert(!q1.isEmpty)
    assert(q1.invariant)
    assert(q1.deleteMax === 3)
    assert(!q1.isEmpty)
    assert(q1.invariant)
    assert(q1.deleteMax === 2)
    assert(!q1.isEmpty)
    assert(q1.invariant)
    assert(q1.deleteMax === 0)
    assert(q1.isEmpty)
  }


  test("deleteMax-insert") {
    val q3 = new FixedIntDoublePriorityQueue(8)
    assert(q3.size == 8)
    q3.incScore(7, 1.25)
    q3.incScore(0, 0.5)
    q3.incScore(2, 1.)
    q3.incScore(6, 2.)
    q3.incScore(3, 1.)
    q3.incScore(1, 1.5)
    q3.incScore(4, 0.7)
    q3.incScore(0, 1.7)
    q3.incScore(2, 1.6)
    q3.incScore(3, 1.7)
    assert(q3.size == 8)
    assert(q3.invariant)
    assert(q3.deleteMax === 3)
    assert(q3.size === 7)
    assert(q3.invariant)
    assert(q3.deleteMax === 2)
    assert(q3.size === 6)
    assert(q3.invariant)
    assert(q3.deleteMax === 0)
    assert(q3.size === 5)
    assert(q3.invariant)
    q3.incScore(1, 1.4)
    q3.incScore(2, 2.2)
    assert(q3.invariant)
    assert(q3.size === 5)
    assert(q3.deleteMax === 1)
    assert(q3.size === 4)
    assert(q3.invariant)
    q3.insert(2)
    assert(q3.max === 2)
    assert(q3.invariant)
    q3.insert(3)
    assert(q3.max === 2)
    assert(q3.invariant)
    assert(q3.deleteMax == 2)
    assert(q3.deleteMax == 3)
  }

  test("remove arbitrary") {
    val q1 = new FixedIntDoublePriorityQueue(7)
    q1.incScore(3, 1.25)
    q1.incScore(2, 1.)
    q1.incScore(6, 2.)
    q1.incScore(3, 1.)
    q1.incScore(0, 0.5)
    q1.incScore(1, 1.5)
    q1.incScore(4, 0.7)
    assert(q1.size == 7)
    q1.remove(6)
    assert(q1.size == 6)
    assert(q1.invariant)
    assert(q1.deleteMax == 3)
    assert(q1.invariant)
  }
}
