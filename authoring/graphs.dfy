module GT {
    trait Node {}

    trait Edge {
        var from: Node;
        var to: Node;
    }

    trait Graph {
        var nodes: set<Node>;
        var edges: set<Edge>;
        var paths: set<seq<Edge>>;
    }

    class WeightedDAG extends Graph {
        constructor(nodes: set<Node>, edges: set<WeightedEdge>, paths: set<seq<WeightedEdge>>)
        requires forall i :: i in edges ==> i.from in nodes && i.to in nodes;
        //requires forall i :: i in paths ==> forall j :: 0 <= j < |i| ==> isPath(edges, i[j])
        {
            this.nodes := nodes;
            this.edges := edges;
            this.paths := paths;
        }
    }

    class WeightedEdge extends Edge {
        var weight :nat;
        constructor(from: Node, to: Node, weight: nat) {
            this.from := from;
            this.to := to;
            this.weight := weight;
        }
    }

    predicate isPath(edges: set<WeightedEdge>, subEdges: seq<WeightedEdge>) 
    reads subEdges
    requires forall i :: i in subEdges ==> i in edges
    {
        forall i :: 0 <= i < |subEdges|-1 ==>
                subEdges[i].to == subEdges[i+1].from
    }
}