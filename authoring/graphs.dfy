module GT {
    trait Node {}

    trait Edge {
        var from: Node;
        var to: Node;
    }

    trait Graph {
        var nodes: set<Node>;
        var edges: set<Edge>;
    }

    class DAG extends Graph {
        constructor(nodes: set<Node>, edges: set<Edge>)
        requires forall i :: i in edges ==> i.from in nodes && i.to in nodes;
        // Not recursive.
        requires forall e :: e in edges ==> !exists j :: j == e.from && j == e.to
        {
            this.nodes := nodes;
            this.edges := edges;
        }
    }

    class WeightedEdge extends Edge {
        var weight :int;
        constructor(from: Node, to: Node, weight: int) {
            this.from := from;
            this.to := to;
            this.weight := weight;
        }
    }
}