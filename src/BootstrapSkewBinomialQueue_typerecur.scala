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
  trait Ordering[+T]{
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
  sealed abstract class PriorityQueue[+T]{

    def comp: Ordering[T]

    def isEmpty = (??? : Boolean)
      .ensuring(res => res == this.toList.isEmpty)

    def findMin = {
      require(!this.toList.isEmpty)
      (??? : T)
    }.ensuring(res => res == this.toList.head)

    def insert(x: T) = (??? : PriorityQueue[T])
      
    def meld(that: PriorityQueue[T]) = (??? : PriorityQueue[T])
      .ensuring(res => (this.toList.size + that.toList.size) == ((this.toList ++ that.toList) & res.toList).size)
    
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
  private case class BootstrappNodes[+T](root: Node[T], queue: Heap[BootstrappNodes[T]]) extends Heap[T]
  private case object Empty extends Heap[Nothing]

  def heapToList[T](h : Heap[T]) : List[T] = h match {
    case Empty => Nil()
    case Nodes(n, ns) => nodeToList(n) ++ heapToList(ns)
  }
    
  def nodeToList[T](n : Node[T]) : List[T] = n match {
    case Node(v, _, h) => List(v) ++ heapToList(h)
  }


  /*
  **   SKEW BINOMIAL QUEUES 
  **/
  case class SkewBinomialQueue[T](elems: Heap[T], comparator: Ordering[T]) extends PriorityQueue[T]{
    def comp: Ordering[T] = this.comparator

    

    def isEmpty: Boolean = {elems == Empty}.ensuring(res => res == this.toList.isEmpty)

    /**
     * We need to implement a function to link two nodes and creates a new tree
     */
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
    }.ensuring(res => res == this.toList.head)

    def findMin_(node: Heap[T]): Node[T] = {
      require(node != Empty)

      node match {
        case Nodes(n, Empty) => n
        case Nodes(n, ns) => val n_min = findMin_(ns); if(comparator.compare(n.value, n_min.value) <= 0) n else n_min
      }
    }

    def insert(x: T): SkewBinomialQueue[T] = {
      this.elems match {
          case Nodes(q1, Nodes(q2, qs)) if q1.rank == q2.rank => 
            SkewBinomialQueue(Nodes(skewLink(Node(x, 0, Empty), q1, q2), qs), this.comp)
          case Nodes(q1, Empty) => 
            SkewBinomialQueue(Nodes(Node(x, 0, Empty), Nodes(q1, Empty)), this.comp)
          case Empty => 
            SkewBinomialQueue(Nodes(Node(x, 0, Empty), Empty), this.comp)
        } 
    }.ensuring(res => res.toList == sort(x::this.toList)(this.comp))
    

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

    // TODO: Support cases when that is BoostrappedSBQ
    def meld(that: PriorityQueue[T]): PriorityQueue[T] = {
      that match {
        case SkewBinomialQueue(el, _) => SkewBinomialQueue(meld_(uniqify(elems), uniqify(el)), comparator)
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
    }.ensuring(res => !res.toList.contains(this.findMin) && this.toList.size - 1 == (this.toList & res.toList).size)


    
    def split(q1: Heap[T], q2: Heap[T], q3: Heap[T]): (Heap[T], Heap[T]) = (q1, q2, q3) match {
      case(xs, ys, Empty) => (xs ,ys)
      case(xs, ys, Nodes(t, c)) => 
        if (t.rank == 0) 
          split(xs, Nodes(t, ys), c)
        else 
          split(Nodes(t, xs), ys, c)
    }

    def toList = heapToList(this.elems).ensuring(res => isSorted(res)(this.comp))
  }

  /*
  **   Boostrapped Skew Rooted Binomial queue 
  **/
  //sealed abstract class BSRBQ[T](root: Node[T], queue: SkewBinomialQueue[BoostrappedSBQ[T]], comparator: Ordering[T])
  case class BoostrappedSBQ[T](elems: Heap[T], comparator: Ordering[T]) extends PriorityQueue[T]{
    def comp: Ordering[T] = this.comparator

    def comp2: Ordering[BoostrappedSBQ[T]] = new Ordering[BoostrappedSBQ[T]]{
        def compare(x:BoostrappedSBQ[T],y:BoostrappedSBQ[T]) : Int = (x.elems, y.elems) match {
          case (_, Empty) => 1
          case (BootstrappNodes(r1, _), BootstrappNodes(r2, _)) => comparator.compare(r1.value, r2.value)
        }  
    }

    def isEmpty: Boolean = {elems == Empty}.ensuring(res => res == this.toList.isEmpty)


    def findMin: T = {
      require(!this.isEmpty)
      this.elems match {
        case BootstrappNodes(r, q) => r.value
      }
    }.ensuring(res => res == this.toList.head)

    def insert(x: T): BoostrappedSBQ[T] = {
        this.elems match {
          case Empty => BoostrappedSBQ(BootstrappNodes(Node(x, 0, Empty), Empty), this.comp)
          case BootstrappNodes(r, q) => {
            meld(BoostrappedSBQ(BootstrappNodes(Node(x, 0, Empty), Empty), this.comp))
          }
        }
      }.ensuring(res => res.toList == sort(x::this.toList)(this.comp))

    // TODO: Support cases when that is SkewBinomialQueue
    def meld(that: PriorityQueue[T]): BoostrappedSBQ[T] = {
      that match {
        case b@BoostrappedSBQ(e, c) => {
        (this.elems, e) match {
          case (_ , Empty) => this
          case (BootstrappNodes(r1, q1), BootstrappNodes(r2, q2)) => 
            if(comp.compare(r1.value, r2.value) <= 0)
              BoostrappedSBQ(BootstrappNodes(r1, SkewBinomialQueue(q1, this.comp2).insert(b).elems.asInstanceOf[Heap[BootstrappNodes[T]]]), comp)
            else 
              BoostrappedSBQ(BootstrappNodes(r2, SkewBinomialQueue(q2, this.comp2).insert(this).elems.asInstanceOf[Heap[BootstrappNodes[T]]]), comp)
          }
        }

      }
    }.ensuring(res => res.toList == sort(this.toList ++ that.toList)(this.comp))
        

    def deleteMin: PriorityQueue[T] = {
      require(!this.isEmpty)
      this.elems match {
        case BootstrappNodes(r, q) => {
          q match {
            case Empty => BoostrappedSBQ(Empty, this.comp)
            case Nodes(n,ns) => 
              val min_ = SkewBinomialQueue(q, this.comp2).findMin.asInstanceOf[BoostrappedSBQ[T]]
              val rest = SkewBinomialQueue(q, this.comp2).deleteMin
              min_ match {
               case BoostrappedSBQ(BootstrappNodes(r, q), _) => 
                val temp = SkewBinomialQueue(q,this.comp2).meld(rest).asInstanceOf[SkewBinomialQueue[BootstrappNodes[T]]]
                BoostrappedSBQ(BootstrappNodes(r, temp.elems), this.comp)
            }
          }
        }
      } 
    }.ensuring(res => !res.toList.contains(this.findMin) && this.toList.size - 1 == (this.toList & res.toList).size)

    
    def toList: List[T] = { this.elems match {
      case Empty => List[T]()
      case BootstrappNodes(n, ns) => sort(n.value::this.deleteMin.toList)(this.comp)
    }
  }.ensuring(res => isSorted(res)(this.comp))

  }

 
}
