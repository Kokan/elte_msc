// Original source: http://www.familie-kneissl.org/Members/martin/blog/family-polymorphism-in-scala
// Obtained from: https://web.archive.org/web/20150827115928/http://www.familie-kneissl.org:80/Members/martin/blog/family-polymorphism-in-scala 
// As of 2019-11-12 the original site is down.

abstract class Graph {
	type Node <: AbstractNode
	type Edge <: AbstractEdge

	def mkNode() : Node
	def connect(n1: Node, n2: Node) : Edge

	abstract class AbstractEdge(val n1: Node, val n2: Node)

	trait AbstractNode {
		def touches(edge: Edge): Boolean = edge.n1 == this || edge.n2 == this
	}
}

class BasicGraph extends Graph {
	type Node = BasicNode
	type Edge = BasicEdge
	protected class BasicNode extends AbstractNode
	protected class BasicEdge(n1:Node, n2:Node) extends AbstractEdge(n1, n2)

	def mkNode() = new BasicNode
	def connect(n1: Node, n2: Node) : BasicEdge = new BasicEdge(n1, n2)
}


class OnOffGraph extends Graph {
	type Node = OnOffNode
	type Edge = OnOffEdge
	protected class OnOffNode extends AbstractNode {
		override def touches(edge: Edge): Boolean = edge.enabled && super.touches(edge)
	}
	protected class OnOffEdge(n1:Node, n2:Node, var enabled: Boolean) extends AbstractEdge(n1, n2)

	def mkNode() = new OnOffNode
	def connect(n1: Node, n2: Node) : OnOffEdge = new OnOffEdge(n1, n2, true)
}

//def addSome(graph: Graph): Graph#Edge = {
//  val n1, n2 = graph.mkNode()
//  graph.connect(n1, n2)
//}

//def addSome2[G <: Graph](graph: G): G#Edge = {
//  val n1, n2 = graph.mkNode()
//  graph.connect(n1, n2)
//}

def extMkNode[G <: Graph](g: G): Graph#Node = g.mkNode()
def extConnect[G <: Graph](g: G)(n1: g.Node, n2: g.Node): g.Edge = g.connect(n1, n2)

def addSome(graph: Graph): Graph#Edge = {
  val n1, n2 = graph.mkNode()
  extConnect(graph)(n1, n2)
}

def addSome2[G <: Graph](graph: G): graph.Edge = {
  val n1, n2 = graph.mkNode()
  extConnect(graph)(n1, n2)
}


    val g = new BasicGraph
    val n1 = g.mkNode()
    val n2 = g.mkNode()
    val e = g.connect(n1, n2)
    assert(n1 touches e)
    assert(n2 touches e)
    val g2 = new BasicGraph
    //g2.connect(n1, n2) // Does not compile

    val og = new OnOffGraph
    val on1 = og.mkNode()
    val on2 = og.mkNode()
    val oe = og.connect(on1, on2)
    // val mixed = og.connect(n1, n2) // ERROR: og.connect not applicable to g.Node

    assert(on1 touches oe)
    assert(on2 touches oe)
    // println(on2 touches e) // ERROR: on2.touches not applicable to g.Edge
    oe.enabled = false;
    assert (! (on2 touches oe), "After disabling, edge virtually has gone")
    assert (! (on1 touches oe), "After disabling, edge virtually has gone")

    val e2 = addSome(g)
    val oe2 = addSome(og)
    // oe2.enabled = false // type OnOffGraph not retained, graph.Edge not possible

    val e22 = addSome2(g)
    val oe22 = addSome2(og)
    oe22.enabled = false // now OK.

