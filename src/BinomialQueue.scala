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

  def heapToList[T](h : Heap[T]) : List[T] = h match {
    case Empty => Nil()
    case Nodes(n, ns) => nodeToList(n) ++ heapToList(ns)
  }
    
  def nodeToList[T](n : Node[T]) : List[T] = n match {
    case Node(v, _, h) => List(v) ++ heapToList(h)
  }


  /*
  **   BINOMIAL QUEUES 
  **/
  case class BinomialQueue[T](elems: Heap[T], comparator: Ordering[T]) extends PriorityQueue[T]{
    def comp: Ordering[T] = this.comparator

    def isEmpty: Boolean = {elems == Empty}.ensuring(res => res == this.toList.isEmpty)

    def reverse(h : Heap[T]): Heap[T] = reverse_(h, Empty)

    def reverse_(h: Heap[T], hs: Heap[T]): Heap[T] = {h match {
        case Empty => hs
        case Nodes(n, ns) => reverse_(ns, Nodes(n, hs))
      }
    }

    def  link_(node1: Node[T], that: Node[T]): Node[T] = {
      if (comparator.compare(node1.value,that.value) <= 0) {
        Node(node1.value, node1.rank + 1, Nodes(that, node1.childrens))
      }
      else 
        Node(that.value, node1.rank + 1, Nodes(node1, that.childrens))
    }

    def findMin: T = {
      require(!isEmpty)
      findMin_(this.elems).value
    }.ensuring(res => res == this.toList.head)

    def findMin_(node: Heap[T]): Node[T] = {
      require(node != Empty)

      node match {
        case Nodes(n, Empty) => n
        case Nodes(n, ns) => val n_min = findMin_(ns); if(comparator.compare(n.value, n_min.value) <= 0) n else n_min
      }
    }

    def insert(x: T): PriorityQueue[T] ={
      BinomialQueue(insert_(Node(x, 0, Empty), elems), comparator)    
    }.ensuring(res => res.toList == sort(x::this.toList)(this.comp))

    def insert_(y: Node[T], nodes: Heap[T]): Heap[T] = {
      decreases(nodes)
      nodes match {
        case Empty => 
          assert(heapToList[T](Empty).isEmpty)
          assert(heapToList(Nodes(y, Empty)) == nodeToList(y) ++ heapToList(Empty))
          Nodes(y, Empty)
        case Nodes(n, ns) => {  
          if (y.rank < n.rank) 
            Nodes(y, Nodes(n, ns)) 
          else {
            val newNode = link_(n, y)
            assert(heapToList(Nodes(newNode, ns)) == nodeToList(newNode) ++ heapToList(ns))
            insert_(newNode, ns)
          }
        }
      } 
    }

    def meld(that: PriorityQueue[T]): PriorityQueue[T] = {
      that match {
        case BinomialQueue(el, _) => BinomialQueue(meld_(elems, el), comparator)
      }
    }.ensuring(res => res.toList == sort(this.toList ++ that.toList)(this.comp))


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
            insert_(link_(n1, n2), meld_(ns1, ns2))
          }
        }
      }
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

    def deleteMin: PriorityQueue[T] = {
      require(!this.isEmpty)
      val (min, rest) = getMin(this.elems)
      BinomialQueue(meld_(rest, reverse(min.childrens)), comparator)
    }.ensuring(res => !res.toList.contains(this.findMin) && this.toList.size - 1 == (this.toList & res.toList).size)

    def toList = {sort(heapToList(this.elems))(this.comp)}.ensuring(res => isSorted(res)(this.comp))
  }
}