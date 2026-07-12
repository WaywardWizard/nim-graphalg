import std/[unittest, sequtils, sugar]
include graphalg
include graphalg/dsl

var
  g0 = graph:
    A - B - C("Desc")
  g1 = graph:
    A - B - H - {I, J}
    A - C - {D, E} - F - G - I
  g2 = graph:
    A - B - H - {I, J}
    {L, M, N} # singletons, note must be in set notation
    A - C - {D, E} - F - G - I
    I - E # loop
  g3 = graph:
    A - A # self edge

  g4 = graph:
    #     v---^
    # A - B - C - D
    #     ^_______v
    A - B - C
    C - B
    C - D - B

  g5 = graph:
    Z

var
  bases = [(g0,@["A"]),(g1,@["A"]), (g2,@["A","L","M","N"]), (g3, @["A"]), (g4,@["A"]), (g5, @["Z"])]
  scc = [(g0,3), (g1,10), (g2, 10), (g3,1), (g4,2)]
  isolatedSccs = [(g0, 0), (g1, 0), (g2,3), (g3, 1), (g4,0)]
  singletonSccs = [(g0, 3), (g1,10), (g2,9), (g3, 1), (g4,1)]
  # Note that a mFAS is not unique, consider a simple SCC loop, any edge breaks it
  minFas = [(g2,@[("G","I")]),(g0,@[]), (g1,@[]),  (g3,@[("A","A")]), (g4,@[("B","C")]), (g5,@[])]
  gsinks = [(g0,1),(g1,2),(g2,1),(g3,0), (g4,0)]
  gsources = [(g0,1),(g1,1),(g2,1),(g3,0),(g4,1)]
  sourceLabels = [(g0,@["A"]),(g1,@["A"]),(g2,@["A"]),(g3,@[]),(g4,@["A"])]
  sinkLabels = [(g0,@["C"]),(g1,@["I","J"]),(g2,@["J"]),(g3,@[]),(g4,@[])]
  elsOrderAndFas = [(g3,("A",@[("A","A")])),(g0,("ABC",@[])),(g1,("ACEDFBHGIJ",@[])),(g2,("ACDBHIEFGLMNJ",@[("G","I")])),(g4,("ACDB",@[("B","C")])),(g5,("Z",@[]))]


for (g,b) in bases: g.basis = b

template listVisits[V: Vertex](itr: iterable[V]): string =
  let tmp = collect:
    for v in itr:
      v.label
  tmp.foldl(a & " " & b)

proc checkFas(
    edges: HashSet[Edge], matchEdges: openArray[tuple[mfrom, mto: char]]
): bool =
  var refset: HashSet[string]
  for (mfrom, mto) in matchEdges:
    refset.incl [mfrom, mto].map(x => x.toUpperAscii).join(" -> ")
  edges.map(x => $x) == refset

proc checkFas(graph: Graph, matchEdges: openArray[tuple[mfrom, mto: char]]): bool =
  graph.fasEadesLinSmith().checkFas(matchEdges)

proc fasElsOrderString(graph: Graph): string =
  ## return concatenation of vertex labels in order els order
  for v in graph.eadesLinSmith():
    result &= $v

func countIsolatedScc(g: Graph): int =
  for c in g.sccs:
    if c.isolated():
      result += 1

func countSingletonScc(g: Graph): int =
  for c in g.sccs:
    if c.singleton():
      result += 1

suite "Unit":
  let
    a = Vertex[NoData, NoData](label: "A")
    b = Vertex[NoData, NoData](label: "B")
    c = Vertex[NoData, NoData](label: "C")

  test "connectTo":
    check a.outbound.len == 0
    check b.inbound.len == 0
    a.connectTo b
    check a.outbound.len == 1
    check b.inbound.len == 1
    check b.inbound[0].outbound.label == "A"
    check a.outbound[0].inbound.label == "B"

  test "connectFrom":
    check c.outbound.len == 0
    check b.inbound.len == 1
    b.connectFrom c
    check c.outbound.len == 1
    check b.inbound.len == 2
    check b.inbound[1].outbound.label == "C"
    check c.outbound[0].inbound.label == "B"

  test "edges iterator":
    check b.edges(dInbound).toseq.len == 2
    check b.edges(dOutbound).toseq.len == 0
    check b.edges(dAll).toseq.len == 2

    check c.edges(dOutbound).toseq.len == 1
    check c.edges(dInbound).toseq.len == 0
    check c.edges(dAll).toseq.len == 1

    # A - A, self edge, neither outbound or inbound
    let selfA = g3.vertices.toseq()[0]
    check selfA.outbound.toseq.len == 0
    check selfA.inbound.toseq.len == 0
    check selfA.selfedges.len == 1

  test "Isolated vertex count":
    check g2.isolated.toseq.len == 3

  test "neighbors iterator":
    check b.neighbours(dOutbound).toSeq.len == 0
    check b.neighbours(dInbound).toSeq.len == 2
    check c.neighbours(dAll).toSeq.len == 1

  test "Set basis manually":
    expect ValueError:
      g2.`basis=` @["Z"] # unknown label

    g2.`basis=` @["A"]
    check len(g2.thebasis) == 1
    check g2.basis.toSeq.len == 1
    
    # iterator uses set basis appropriately
    g2.`basis=` @["A", "L", "M", "N"]
    check g2.basis.toSeq.len == 4
    check len(g2.thebasis) == 4

  test "Sources":
    for (g,n) in gsources:
      check g.sources().toSeq.len == n
  test "Sinks":
    for (g,n) in gsinks:
      check g.sinks.toSeq.len == n

  test "DFS":
    ## vertex children traversed in reverse order of their declaration
    check listVisits(g0.dfs) == "A B C"
    check listVisits(g1.dfs) == "A C E F G I D B H J"
    check listVisits(g2.dfs) == "A C E F G I D B H J L M N"
    check listVisits(g3.dfs) == "A"
    check listVisits(g4.dfs) == "A B C D"
    check listVisits(g5.dfs) == "Z"

  test "BFS":
    check listVisits(g1.bfs) == "A B C H D E I J F G"
    check listVisits(g2.bfs) == "A B C H D E I J F G L M N"

  test "Walk DFS":
    var cx: int = 0
    for (entry, edge) in walkDfs(
      iterator (): Vertex[string, NoData] =
        for b in g1.basis:
          yield b
    ):
      cx += 1
    check cx == 18
    cx = 0
    for (entry, edge) in walkDfs(
      iterator (): Vertex[string, NoData] =
        for b in g2.basis:
          yield b

    ):
      cx += 1
    check cx == 18

  test "Sources iterator":
    for (g,s) in sourceLabels:
      var slabels = collect(for s in g.sources: s.label)
      check (s.toHashSet() -+- slabels.toHashSet).card == 0
  test "Sinks iterator":
    for (g,s) in sinkLabels:
      var slabels = collect(for s in g.sinks: s.label)
      check (s.toHashSet() -+- slabels.toHashSet).card == 0


suite "Integration":
  test "Cycles":
    for (g,n) in scc:
      check g.sccs.toseq.len == n

  test "Condensation":
    for (g,n) in scc:
      var
        byCondensation = collect:
          for v in g.condensation().vertices: {$v}
        byCycle = collect:
          for c in g.sccs: {$c}

      # cycle returns same list of grouped labels that condensation does
      check (byCondensation -+- byCycle).len() == 0
      check g.condensation().edges(dOutbound).toSeq.len == g.condensation().edges(dInbound).toSeq.len

    # spot check the condensation outbound and inbound edge derivations
    check g2.condensation().edges(dOutbound).toSeq.len == 8
    check g2.condensation().edges(dInbound).toSeq.len == 8
    check g4.condensation().edges(dOutbound).toSeq.len == 1
    check g4.condensation().edges(dInbound).toSeq.len == 1

  test "Basis is calculated correctly":
    # not using the manual basis override, can we derive a basis
    for (g,b) in bases:
      g.basis = @[] # wipe manual
      var derivedBasis = collect:
        for v in g.basis: v

      # derived basis can differ the set basis since any one member of an SCC may
      # be selected as a member of the basis set however the basis cardinality is
      # invariant
      check derivedBasis.len == b.len
      g.basis = b # reset

  test "Add to vertex ordering":
    var vo: VertexOrdering[Vertex[NoData, NoData]]
    let
      a = Vertex[NoData, NoData](label: "A")
      b = Vertex[NoData, NoData](label: "B")
      c = Vertex[NoData, NoData](label: "C")
    vo[0] = a # seed index 0 so subsequent adds land contiguously
    vo.add b # biggest+1 == 1
    vo.add c # biggest+1 == 2
    check vo.biggest == 2
    check vo[a] == 0
    check vo[b] == 1
    check vo[c] == 2
    check vo[0] == a
    check vo[1] == b
    check vo[2] == c

  test "Swap entries in vertex ordering":
    var vo: VertexOrdering[Vertex[NoData, NoData]]
    let
      a = Vertex[NoData, NoData](label: "A")
      b = Vertex[NoData, NoData](label: "B")
      c = Vertex[NoData, NoData](label: "C")
    vo[0] = a
    vo[1] = b
    vo[2] = c
    vo.swap(0, 2)
    check vo[0] == c
    check vo[2] == a
    check vo[a] == 2
    check vo[c] == 0
    # the middle entry is untouched
    check vo[1] == b
    check vo[b] == 1

  test "Move entry in vertex ordering":
    var vo: VertexOrdering[Vertex[NoData, NoData]]
    let
      a = Vertex[NoData, NoData](label: "A")
      b = Vertex[NoData, NoData](label: "B")
      c = Vertex[NoData, NoData](label: "C")
      d = Vertex[NoData, NoData](label: "D")
    vo[0] = a
    vo[1] = b
    vo[2] = c
    vo[3] = d

    # forwards: move a from index 0 to index 2; (0,2] shifts down
    vo.moveto(0, 2)
    check vo[0] == b
    check vo[1] == c
    check vo[2] == a
    check vo[3] == d
    check vo[a] == 2
    check vo[b] == 0
    check vo[c] == 1

    # backwards: move a from index 2 back to index 0; [0,2) shifts up
    vo.moveto(2, 0)
    check vo[0] == a
    check vo[1] == b
    check vo[2] == c
    check vo[3] == d
    check vo[a] == 0
    check vo[b] == 1
    check vo[c] == 2

  test "FAS Eades-Lin-Smith":
    # g2 has cycles. ELS produces a vertex ordering whose backedge set (FAS)
    # makes the graph acyclic when pruned.
    # var v = g2.vertices.toSeq()
    for (g,orderfas) in elsOrderAndFas:
      let (order,fas) = orderfas
      var ordering = initVertexOrdering[Vertex[string, NoData]](g.vertices)
      ordering.eadesLinSmith()
      check ordering.foldl(a&b.label,"") == order
      var thefas = ordering.fas
      check (thefas -+- g.fasEadesLinSmith()).card == 0
      check thefas.card == fas.len

  test "Vertex Ordering Reorder pass":
    var ordering = initVertexOrdering[Vertex[string, NoData]](g2.vertices)
    var order = ordering.printLabels.replace(" ","")
    check ordering.fas.len == 6 # Vertices in order of insertion
    ordering.reorderPass()
    # Reorder pass gets ELS output here...
    check ordering.fas.len == 1 # F-G

  test "Isolated SCC count":
    for (g,n) in isolatedSccs:
      check g.countIsolatedScc == n

  test "Singleton SCC count":
    for (g,n) in singletonSccs:
      check g.countSingletonScc == n

  test "Brute Vertex Ordering":
    # test strategy is to find the total backedge count after brute forcing an order
    # across all SCC
    for (g,thefas) in minfas: # 2 0 1 3 4
      var
        pre, post: int
        n=thefas.len
      for c in g.sccs:
        if c.singleton():
          var nself = c.vertices.chooseAny.selfEdges.len
          pre += nself
          post += nself
          continue
        var order = initVertexOrdering[Vertex[string,NoData]](c.vertices)
        pre+=order.fas.len
        # invariant: ordering exists for unconstrained
        post+=c.bruteVertexOrdering[:Vertex[string,NoData]]().get().fas.len

      check pre>=post and post==n

  test "FAS brute edge set":
    for (g,thefas) in minfas: # 2 0 1 3 4
      var
        post: int
        n=thefas.len
      for c in g.sccs:
        if c.singleton():
          var nself = c.vertices.chooseAny.selfEdges.len
          post += nself
          continue
        # invariant that unconstrained minimal edgeset exists
        var es = c.fasBruteEdgeSet.get()
        var order = initVertexOrdering[Vertex[string,NoData]](c.vertices)
        post += es.card

      check post==n
      
  test "Fas for a graph":
    var ix=0
    for (g,fas) in minfas:
      check g.fas.card == fas.len
    