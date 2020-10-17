interface GRAPH =

  class Edge {
    strv: int;                     /*start vertex*/
    endv: int;                     /*end vertex*/
    wght: int;                     /*weight*/
  }

  predicate edgeWeightInv (edg: Edge, k: int) =
    edg <> null ->
    let weight = edg.wght in
    0 <= weight /\ weight < k

  class EdgeArray { eLength: int; eSlots: Edge array; }

  predicate edgeArrayWeightInv (edgs: EdgeArray, k: int) =
    edgs <> null ->
    let len = edgs.eLength in
    forall i:int. 0 <= i -> i < len ->
      let edg = edgs[i] in
      edgeWeightInv(edg, k)

  class Bag { bagNode: int; bagEdges: EdgeArray; }

  predicate bagWeightsInv (b: Bag, k: int) =
    b <> null ->
    let edges = b.bagEdges in
    edgeArrayWeightInv(edges, k)

  predicate bagInv (b: Bag) =
    b <> null ->
    let bNode = b.bagNode in
    let edges = b.bagEdges in
    let len = edges.eLength in
    forall i:int. 0 <= i -> i < len ->
      let edg = edges[i] in
      edg.strv = bNode \/ edg.endv = bNode

  class BagArray { bLength: int; bSlots: Bag array; }

  class Graph { numVerts: int; adjList: BagArray; }

  predicate inRange (e: Edge, k: int) =
    e <> null ->
    let src = e.strv in
    let trgt = e.endv in
    0 <= src /\ src < k /\ 0 <= trgt /\ trgt < k

  predicate edgesInRange (edgs: EdgeArray, k: int) = 
    edgs <> null ->
    let len = edgs.eLength in
    forall i:int. 0 <= i -> i < len ->
      let edg = edgs[i] in
      inRange(edg, k)

  predicate bagInRange (b: Bag, k: int) =
    b <> null ->
    let edgs = b.bagEdges in
    edgesInRange(edgs, k)

  predicate graphInv (g: Graph) =
    g <> null ->
    let adjLs = g.adjList in
    let numVs = g.numVerts in
    adjLs.bLength = numVs /\
    (forall i:int. 0 <= i -> i < numVs -> let v = adjLs[i] in v <> null) /\
    (forall i:int. 0 <= i -> i < numVs -> let bag = adjLs[i] in
       bagInRange (bag, numVs) /\
       bagInv (bag) /\
       bag.bagNode = i /\
       bagWeightsInv (bag, 100))

  predicate hasVertex (g: Graph, v: int) =
    g <> null ->
    let numVerts = g.numVerts in
    0 <= v /\ v < numVerts

  meth getEdges (g: Graph+) : EdgeArray+
    requires { graphInv(g) }
    ensures  { graphInv(g) }
    ensures  { let numVs = g.numVerts in edgesInRange(result, numVs) }
    ensures  { let len = result.eLength in
               forall i:int. 0 <= i -> i < len ->
                 let edg = result[i] in
                 edg <> null /\ edgeWeightInv(edg, 100) }
    ensures  { let oa = old(alloc) in alloc diff oa = {result} }
    effects  { rd g, {g}`any, {g}`adjList`any; rw alloc }

end


interface CLIENT = end

module Client : CLIENT =
  import PQUEUE
  import GRAPH

  class DistArray { dLength: int; dSlots: int array; }

  meth initDistances (d: DistArray+, k: int) : unit
    ensures { let len = d.dLength in forall i:int. 0 <= i -> i < len -> d[i] = k }
    effects { wr {d}`dSlots }

  meth dijkstra_NODEC (g: Graph+, source: int) : DistArray+
    requires { pool = {} }
    requires { graphInv(g) }
    requires { hasVertex(g, source) }
    effects  { wr alloc, pool, pool`any, pool`rep, pool`rep`any;
               rd alloc, pool, pool`any, pool`rep, pool`rep`any,
                  g, {g}`any, {g}`adjList`any, {g}`adjList`bSlots`any }
  = var dist : DistArray in
    var queue : Pqueue in
    var min : Node in
    var minTag : int in
    var minKey : int in
    var numVs : int in
    var ins : Node in
    var isEmp : bool in

    numVs := g.numVerts;
    queue := new Pqueue;
    Pqueue (queue);
    dist := new DistArray[numVs];
    initDistances (dist, 100);
    { let len = dist.dLength in forall k:int. 0 <= k -> k < len -> dist[k] = 100 };
    
    ins := insert(queue, 0, source);
    isEmp := isEmpty (queue);

    assume { graphInv(g) };

    min := ins;
    while (not isEmp) do
      invariant { isEmp <-> queue.size = 0 }
      invariant { graphInv(g) }
      invariant { pqueuePub(pool) }
      invariant { numVs = g.numVerts /\ dist.dLength = numVs }
      invariant { let len = dist.dLength in
                  forall k:int. 0 <= k -> k < len -> let v = dist[k] in 0 <= v }
      invariant { let rep = queue.rep in min in rep }
      invariant { let rep = queue.rep in forall n:Node in rep. let key = n.key in key >= 0 }
      invariant { let rep = queue.rep in
                  let len = dist.dLength in
                  forall n:Node in rep.
                    let tag = n.tag in
                    tag >= 0 /\ tag < len }
      invariant { Type({queue}`rep, Node) }
      invariant { Type({queue},Pqueue) /\ Type({g},Graph) /\ Type({dist},DistArray) /\ Type({min},Node) }
      invariant { dist <> null }
      
      min := deleteMin (queue);
      { Type({min},Node) /\ let rep = queue.rep in min in rep };
      minTag := min.tag;
      { minTag >= 0 /\ let len = dist.dLength in minTag < len };
      minKey := min.key;

      var i : int in
      i := dist[minTag];

      if (minKey < i) then
          dist[minTag] := minKey;

          var eLen : int in
          var edges : EdgeArray in

          isEmp := isEmpty(queue);

          assume { graphInv(g) };
          edges := getEdges(g);
          eLen := edges.eLength;

          var edge : Edge in
          edge := null;

          i := 0;
          while (0 <= i and i < eLen) do
              invariant { isEmp <-> queue.size = 0 }
              invariant { eLen = edges.eLength }
              invariant { 0 <= i /\ i <= eLen }
              invariant { numVs = g.numVerts /\ dist.dLength = numVs }
              invariant { graphInv(g) }
              invariant { edgesInRange (edges, numVs) }
              invariant { pqueuePub(pool) }
              invariant { let len = dist.dLength in
                          forall k:int. 0 <= k -> k < len -> let v = dist[k] in 0 <= v }
              invariant { let rep = queue.rep in min in rep }
              invariant { let rep = queue.rep in forall n:Node in rep. let key = n.key in key >= 0 }
              invariant { let rep = queue.rep in
                          let len = dist.dLength in
                          forall n:Node in rep.
                            let tag = n.tag in
                            tag >= 0 /\ tag < len }
              invariant { Type({queue}`rep, Node) }
              invariant { Type({queue},Pqueue) /\
                          Type({g},Graph) /\
                          Type({dist},DistArray) /\
                          Type({edges},EdgeArray) }
              invariant { Type({edge},Edge) }
              invariant { forall k:int. 0 <= k -> k < eLen ->
                            let v = edges[k] in
                            v <> null /\
                            Type({v},Edge) /\
                            edgeWeightInv(v, 100) }
              invariant { dist <> null }

              var startVertex : int in
              var endVertex : int in
              var weight : int in

              edge := edges[i];
              startVertex := edge.strv;
              endVertex := edge.endv;
              weight := edge.wght;
              { weight >= 0 };

              var d : int in
              var candidateDist : int in

              d := dist[startVertex];
              candidateDist := d + weight;

              d := dist[endVertex];
              if (candidateDist < d) then
                  { candidateDist >= 0 };
                  { endVertex >= 0 };
                  { numVs = g.numVerts };

                  { let num = dist.dLength in endVertex < num };
                  { let rep = queue.rep in edges notin rep };
                  ins := insert(queue, candidateDist, endVertex);

                  { ins.tag = endVertex /\ ins.key = candidateDist };
                  { edgesInRange (edges, numVs) };

                  dist[endVertex] := candidateDist;
              end;

              i := i + 1;
              isEmp := isEmpty(queue);

              { numVs = g.numVerts };
              assume { graphInv(g) };
          done;
      end;                      /*end if (minKey < i)*/

      isEmp := isEmpty(queue);
      assume { graphInv(g) };
    done;
    result := dist;

end
