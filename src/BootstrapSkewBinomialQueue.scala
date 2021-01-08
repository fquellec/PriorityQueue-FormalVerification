package main

import stainless.collection._
import stainless.lang._
import stainless.equations._
import stainless.annotation._
import stainless.lang.StaticChecks._


object PriorityQueue{

  /*
  **   Ordering definition and methods, to be able to sort and verify 
  **   findMin and deleteMin on our PQs
  **/
  trait Ordering[T]{
    def compare(x:T,y:T) : Int
    
    @law def inverse(x:T,y:T) : Boolean = 
      sign(compare(x,y)) == -sign(compare(y,x))
    @law def transitive(x:T,y:T,z:T) : Boolean = 
      (compare(x,y) > 0 && compare(y,z) > 0) ==> (compare(x,z) > 0)
    @law def consistent(x:T,y:T,z:T) : Boolean =(
      compare(x,y)==0)==>(sign(compare(x,z))==sign(compare(y,z)))

    private final def sign(i:Int) : Int = if (i>0) 1 else (if(i<0) -1 else 0)
  }

  def isSorted[T](l : List[T])(implicit comparator:Ordering[T]) : Boolean = {
    decreases(l)
    l match {
      case x::(xs@(y::ys)) => comparator.compare(x,y) <= 0 && isSorted(xs) 
      case _ => true
    }
  }

  def SInsert[T](x: T, l: List[T])(implicit comparator: Ordering[T]) : List[T] = {
    require(isSorted(l))
    decreases(l)
    l match{
      case Nil() => x::Nil()
      case y::ys if comparator.compare(x,y) <= 0 => x::l 
      case y::ys => comparator.inverse(x, y); y::SInsert(x,ys)
    }
  }.ensuring(isSorted(_))

  def sort[T](l: List[T])(implicit comparator: Ordering[T]) : List[T] = {
    decreases(l)
    l match{
      case Nil() => Nil[T]()
      case x::xs => SInsert(x,sort(xs))
    }
  }.ensuring(isSorted(_))
  

  /*
  **   PQs abstract class, methods and verifications definition
  */
  sealed abstract class PriorityQueue[T]{

    def comp: Ordering[T]

    def isEmpty = (??? : Boolean)
      .ensuring(res => res == this.toList.isEmpty)

    def findMin = {
      require(!this.toList.isEmpty)
      (??? : T)
    }.ensuring(res => res == this.toList.head)

    def insert(x: T) = (??? : PriorityQueue[T])
      .ensuring(res => res.toList == sort(x::this.toList)(this.comp))
    
    def meld(that: PriorityQueue[T]) = (??? : PriorityQueue[T])
      .ensuring(res => res.toList == sort(this.toList ++ that.toList)(this.comp))

    def deleteMin = {
      require(!this.toList.isEmpty)
      (??? : PriorityQueue[T])
    }.ensuring(res => !res.toList.contains(this.findMin) && this.toList.size - 1 == (this.toList & res.toList).size)
    
    def toList = (??? : List[T])
      .ensuring(res => isSorted(res)(this.comp))
  }

  /*
  **   Node definition for BINOMIAL QUEUES
  **/
  case class Node[+T](value: T, rank: BigInt = 0, childrens: Heap[T]){
    require(childrens match {
      case Empty => rank == 0
      case Nodes(n, ns) => rank == n.rank+1
    })
  }

  sealed abstract class Heap[+T]
  private case class  Nodes[+T](head : Node[T], tail : Heap[T]) extends Heap[T]
  private case object Empty extends Heap[Nothing]

  def size[T](@induct h: Heap[T]): BigInt = {
    h match {
      case Empty => 0
      case Nodes(n, ns) => size(n) + size(ns)
    }
  }

  def size[T](@induct n: Node[T]): BigInt = {
    1 + size(n.childrens)
  }

  def heapToList[T](h : Heap[T]) : List[T] = {
    decreases(size(h))
    h match {
      case Empty => Nil()
      case Nodes(n, ns) => nodeToList(n) ++ heapToList(ns)
    }
  }
    
  def nodeToList[T](n : Node[T]) : List[T] = {
    decreases(size(n))
    n match {
      case Node(v, _, h) => List(v) ++ heapToList(h)
    }
  }

 /*
  **   SKEW BINOMIAL QUEUES 
  **/
  case class SkewBinomialQueue[T](elems: Heap[T], comparator: Ordering[T]) extends PriorityQueue[T]{
    def comp: Ordering[T] = this.comparator

    def isEmpty: Boolean = elems == Empty

    def  link(node1: Node[T], that: Node[T]): Node[T] = {
      if (comparator.compare(node1.value,that.value) <= 0) {
        Node(node1.value, node1.rank + 1, Nodes(that, node1.childrens))
      }
      else 
        Node(that.value, node1.rank + 1, Nodes(node1, that.childrens))
    }

    def skewLink(q0: Node[T], q1: Node[T], q2: Node[T]): Node[T] = {
      if (comparator.compare(q0.value, q1.value) > 0 && comparator.compare(q2.value, q1.value) > 0)
        Node(q1.value, q1.rank + 1, Nodes(q0, Nodes(q2, q1.childrens)))
      else if (comparator.compare(q0.value, q2.value) > 0 && comparator.compare(q1.value, q2.value) > 0)
        Node(q2.value, q2.rank + 1, Nodes(q0, Nodes(q1, q2.childrens)))
      else 
        Node(q0.value, q1.rank + 1, Nodes(q1, Nodes(q2, Empty)))
    }

    def findMin: T = {
      require(!isEmpty)
      findMin_(this.elems).value
    }

    def findMin_(node: Heap[T]): Node[T] = {
      require(node != Empty)

      node match {
        case Nodes(n, Empty) => n
        case Nodes(n, ns) => val n_min = findMin_(ns); if(comparator.compare(n.value, n_min.value) <= 0) n else n_min
      }
    }

    def insert(x: T): SkewBinomialQueue[T] = this.elems match {
      case Nodes(q1, Nodes(q2, qs)) if q1.rank == q2.rank => SkewBinomialQueue(Nodes(skewLink(Node(x, 0, Empty), q1, q2), qs), this.comp)
      case Nodes(q1, Empty) => SkewBinomialQueue(Nodes(Node(x, 0, Empty), Nodes(q1, Empty)), this.comp)
      case Empty => SkewBinomialQueue(Nodes(Node(x, 0, Empty), Empty), this.comp)
    }

    def insert_(y: Node[T], nodes: Heap[T]): Heap[T] = {
      decreases(nodes)
      nodes match {
        case Empty => Nodes(y, Empty)
        case Nodes(n, ns) => {  
          if (y.rank < n.rank) Nodes(y, Nodes(n, ns)) 
          else {
          insert_(link(n, y), ns)
          }
        }
      } 
    }

    def meld(that: PriorityQueue[T]): PriorityQueue[T] = {
      require(that.isInstanceOf[SkewBinomialQueue[T]])
      that match {
        case SkewBinomialQueue(el, _) => SkewBinomialQueue(meld_(uniqify(elems), uniqify(el)), comparator)
      }
    }

    def meld_(q1: Heap[T], q2: Heap[T]): Heap[T] = {      
      (q1, q2) match {
        case (Empty, _) => q2
        case (_, Empty) => q1
        case (Nodes(n1, ns1), Nodes(n2, ns2)) => {
          if (n1.rank < n2.rank) {
            Nodes(n1, meld_(ns1, q2))
          }
          else if (n1.rank > n2.rank) {
            Nodes(n2, meld_(q1, ns2))
          }
          else {
            insert_(link(n1, n2), meld_(ns1, ns2))
          }
        }
      }
    }

    def uniqify(nodes: Heap[T]): Heap[T] = (nodes) match {
        case Empty => Empty
        case Nodes(q, qs) => insert_(q, qs)
    }

    def getMin(nodes: Heap[T]): (Node[T], Heap[T]) = {
      require(nodes != Empty)
      nodes match {
        case Nodes(n, Empty) => (n, Empty)
        case Nodes(n, ns) => {
          val (m, n2) = getMin(ns);
          if (comparator.compare(n.value, m.value) <= 0) {
            (n, ns)
          } else {
            (m, Nodes(n, n2))
          }
        }
      }
    }

    def foldInsert(acc: Heap[T], heap: Heap[T]): Heap[T] = heap match {
      case Empty => acc
      case Nodes(n, ns) => foldInsert(insert_(n, acc), ns)
    }

    def deleteMin: PriorityQueue[T] = {
      require(this.elems != Empty)
      val (min, rest) = getMin(this.elems)
      val (ts0, xs0) = split(Empty, Empty, min.childrens)
      SkewBinomialQueue(foldInsert(xs0, meld_(rest,ts0)), this.comp)
    }

    def split(q1: Heap[T], q2: Heap[T], q3: Heap[T]): (Heap[T], Heap[T]) = (q1, q2, q3) match {
      case(xs, ys, Empty) => (xs ,ys)
      case(xs, ys, Nodes(t, c)) => 
        if (t.rank == 0) 
          split(xs, Nodes(t, ys), c)
        else 
          split(Nodes(t, xs), ys, c)
    }

    def toList = sort(heapToList(this.elems))(this.comp)
  
  }


  /**
   *  BOOTSTRAP QUEUE
   */
  sealed abstract class BSBQ[T] extends PriorityQueue[T]{
    val root: Node[T] 
    val queue: PriorityQueue[BSBQ[T]]
  }

  case class BoostrappedSBQ[T](root: Node[T], queue: PriorityQueue[BSBQ[T]], comparator: Ordering[T], comp2: Ordering[BSBQ[T]]) extends BSBQ[T]{
    def comp: Ordering[T] = this.comparator

    def isEmpty: Boolean = false

    def findMin: T = this.root.value

    def insert(x: T): BoostrappedSBQ[T] = meld(BoostrappedSBQ(Node(x, 0, Empty), SkewBinomialQueue(Empty, comp2), comp, comp2))

    def meld(that: PriorityQueue[T]): BoostrappedSBQ[T] = {
      require(that.isInstanceOf[BSBQ[T]])
      that match {
      case EmptyBSBQ(_, _) => this
      case b@BoostrappedSBQ(r, q, c, c2) => 
        if(comp.compare(this.root.value, r.value) <= 0)
          BoostrappedSBQ(this.root, this.queue.insert(b), c, c2)
        else 
          BoostrappedSBQ(r, b.queue.insert(this), c, c2)
      }
    } 

    def deleteMin: PriorityQueue[T] = {
      if(this.queue.isEmpty)
        EmptyBSBQ(this.comp, comp2)
      else {
        val min_ = this.queue.findMin
        val rest = this.queue.deleteMin
        BoostrappedSBQ(min_.root, min_.queue.meld(rest), comp, comp2)
      }
    }

    def toList: List[T] = sort(nodeToList(root)++queue.toList)
  }

  case class EmptyBSBQ[T](comparator: Ordering[T], comp2: Ordering[BSBQ[T]]) extends PriorityQueue[T]{
    def comp: Ordering[T] = this.comparator
    def isEmpty: Boolean = true
    def findMin: T = ???
    
    def insert(x: T): BoostrappedSBQ[T] = BoostrappedSBQ(Node(x, 0, Empty), SkewBinomialQueue(Empty, comp2), comp, comp2)
    def meld(that: PriorityQueue[T]): PriorityQueue[T] = that
    def deleteMin: EmptyBSBQ[T] = ???
    def toList: List[T] = List()
  }
}