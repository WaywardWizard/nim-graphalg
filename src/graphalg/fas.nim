## # Finding feedback arc sets
##
## Acyclic: No backedges
## SCC: Every vertex within may reach every other vertex, and be reached from
##      any other
## Strongly Connected: As per SCC
## Weakly connected: There exists a vertex from which every other may be reached
## Feedback Arc Set: A set of edges which if removed will make the graph acyclic
## MFAS: Minimum possible set of edges to make graph acyclic
##
## Finding the MFAS is NP-Hard. To get a good FAS, where this means that the
## FAS cardinality is close to that of MFAS use Eades-Lin-Smith algorithm
##
## We want to preserve weakly connected property of our graph(s).
##
## One approach is to find a L-R vertex sort that
##  * The set of forward edges preserves weak connectivity
##  * The set of back edges is the MFAS or close to it
##
## Tarjans SCC given an acyclic condensed graph with SCCs as nodes. It also
## returns every backedge for each SCC. The condensed graph is a DAG. If we prune
## the Tarjans SCC backedge set for every SCC we are left with a forest where
## all trees retain their weakly connected property and are DAG. This is good
## enough.
##
## Another approach is brute forcing. SCCs are a graph property not an algorithm
## artifact of Tarjans SCC. This means that no matter the vertice ordering passed
## to Tarjans SCC we will find the same SCC are produced. This means the vertices
## of the condensed graph are fixed, and so are their edges.
##
## Order SCCs per topological sort, find a MFAS for each SCC small enough, find
## a good FAS using ELS for each SCC not small enough for rough handling. Then
## improve on FAS.
##
## ELS solutions improved by
##    1) Making pass(es) swapping adjacent vertices if yields backedge reduction
##    2) Making pass(es) looking for optimal placement for each vertice
##    3) Iterative Local Search. Perturb. Use some combination of the above. Iterate

import std/[options, sets, algorithm, sequtils, enumerate, lists]
import datastructures

type
  ConnectivityConstraint = enum
    ## Connectivity constraints place restriction on state of a graph (set of
    ## vertices). Their purpose is to add requirements to feedback arc setsv
    ccAcyclic ## No cycles exist in group of vertice
    ccWeak ## Any given node may reach another if edges are considered bidirectional.
    ccTraversible
    ## Post pruning a single source node exists from which all other nodes may
    ## be reached. Test with DFS. O(V+E)

    # ccThoroughfare ## Any vertex with incoming edge may reach

  FasStrategy = enum
    fsBruteVertexOrder ## brute force FAS with vertex ordering
    fsBruteEdgeset ## brute force FAS with edge sets
    fsEls ## Eades lin smith ordering
    fsElsReorder ## Eades lin smith with best gap positioning

const BRUTE_EDGES* = 20 ## dont brute for more edges
const BRUTE_VERTICES* = 10 ## dont brute for more vertices
const JUST_ELS* = 3000 ## node count before we stop doing reorder passes

type VertexOrdering[V: Vertex] = object ## Vertices indexed 1..N and vice versa
  m: BiMap[V, int] # vertex to index, index to vertex
  biggest: int = -1 #

proc `[]`(x: VertexOrdering, v: VertexOrdering.V | int): int | VertexOrdering.V =
  ## Forward/reverse lookup on ordering
  x.m[v]

proc `[]=`(x: var VertexOrdering, u: int, v: VertexOrdering.V) {.inline.} =
  ## add vertex to ordering at indice
  if u > x.biggest:
    x.biggest = u
  x.m[u] = v

proc `[]=`(x: var VertexOrdering, u: VertexOrdering.V, v: int) {.inline.} =
  if v > x.biggest:
    x.biggest = v
  x.m.ab[u] = v
  x.m.ba[v] = u

proc add(x: var VertexOrdering, u: VertexOrdering.V) {.inline.} =
  ## Add vertex to end of ordering
  x[x.biggest + 1] = u

proc contains(x: VertexOrdering, val: VertexOrdering.V | int): bool =
  ## Contains supports in and notin on vertex ordering
  val in x.m

proc printLabels[T](x: VertexOrdering[Vertex[string, T]]): string =
  ##  Labels of vertices in order for inspection
  x.toSeq.join(" ")

proc initVertexOrdering[T: Vertex](vertices: Iterable[T]): VertexOrdering[T] =
  for v in vertices:
    result.add v

proc `swap`(x: var VertexOrdering, p, q: int) {.inline.} = # 6x hash, lookup
  ## Swap two vertices in the ordering
  x.m.swap(p, q)

iterator items(x: VertexOrdering): VertexOrdering.V =
  ## Iterate items of ordering in order
  # dont add/rm vertices while iterating
  for ix in 1 .. x.biggest:
    yield x.m[ix]

iterator pairs(x: VertexOrdering): (int, Vertex) =
  ## Enumerated vertices of ordering in order
  for ix in 1 .. x.biggest:
    yield (ix, x.ba[ix])

proc moveto(x: var VertexOrdering, p, q: int) =
  ## For p<q, remove element at p, backshift elements (p,q], and insert at q
  ## For p>q, remove element at p, forwardshift elements [q,p), insert at q
  ##
  ## After a move, our P vertex will be at position q. A gap will be created at
  ## q by removal of item at p, which is then filled with that item.
  if p == q:
    return # noop
  if p > x.biggest or q > x.biggest:
    raise ValueError.newException("Move to contiguous index")

  let movee = x[p]

  if p > q: # O(N) move forwards one
    for ix in countdown(p - 1, q):
      x[ix + 1] = x[ix]
  else: # p<q move backwards
    for ix in (p + 1) .. q:
      x[ix - 1] = x[ix]

  x[q] = movee

proc fas(
    ordering: VertexOrdering
): HashSet[Edge[VertexOrdering.V.D, VertexOrdering.V.M]] =
  ## Extract feedback arc set from ordering
  ##
  ## The feedback arc set shall be defined as all edges that lead to a vertex
  ## earlier in the ordering than the vertex from which the arc departs, and, all
  ## self edges. That is, edges that lead from the current vertex back to itself
  for ix, el in enumerate(ordering):
    for edge in el.outbound:
      # ignore edges to vertices not contained in ordering
      if edge.inbound notin ordering:
        continue
      if ordering[edge.inbound] < ix + 1: # orderings are one based
        result.incl edge
    # selfedges
    for e in el.selfedges:
      result.incl e

proc eadesLinSmith(ordering: var VertexOrdering) =
  ## Find a vertex ordering producing a minimal-ish FAS with ELS heuristic
  ##
  ## Such orderings produce a FAS guaranteed acyclic, however they do not
  ## guarantee weakly connected, traversible or other conditions
  var
    sources, pendingSources, sinks, pendingSinks: seq[VertexOrdering.V]
    pending: Table[int, IndexedList[DoublyLinkedList[VertexOrdering.V]]]
      # vertices mapped by flux

    # delta will be the outdeg - indeg, delta will increase if incoming edge
    # is lost or decrease if outgoing edge is lost
    delta: Table[VertexOrdering.V, int] # track ignored edges

    transferred: HashSet[VertexOrdering.V]
    pendingSourceOrSink: HashSet[VertexOrdering.V]

    remaining = ordering.biggest

  var maxDelta: int

  proc getMaxDelta(): int =
    while maxDelta notin pending:
      maxDelta -= 1
    maxDelta

  # Prepare queues and bins
  for v in ordering:
    let
      flux = v.flux
      dlt = flux.o - flux.i
    delta[v] = dlt
    if (dlt) > maxDelta:
      maxDelta = dlt

    if v.source:
      pendingSources.add v
      pendingSourceOrSink.incl v
    elif v.sink:
      pendingSinks.add v
      pendingSourceOrSink.incl v
    else:
      pending.mgetOrPut(dlt).add v

  proc shiftPendingBin(deltaOld, deltaNew: int, z: Vertex) =
    ## transfer vertex across bins, update delta tracker
    var found = false

    for el in pending[deltaOld]:
      if el == z:
        pending[deltaOld].del el
        found = true
        break
    assert found # wont shift a vertex if it isnt where it was claimed to be

    if pending[deltaOld].len == 0: # delete bin if now empty
      pending.del deltaOld

    pending.mgetOrPut(deltaNew).add z

    delta[z] = deltaNew
    if deltaNew > maxDelta:
      maxDelta = deltaNew

  # remove a vertex and its edges from graph, transferring neighbours to next bin
  proc remove(x: Vertex) =
    ## Remov vertex and edges from graph
    ##
    ## - Shift neighbour bins
    ## - Remove vertex from bin
    ## - Mark as transferred
    ## - Reduce remaining
    var deltaOld, deltaNew: int
    for e in x.outbound: # neighbour loses an incoming edge
      if e.inbound in transferred or e.inbound in pendingSourceOrSink:
        continue
      deltaOld = delta[e.inbound]
      shiftPendingBin(deltaOld, deltaOld + 1, e.inbound)

    for e in x.inbound: # neighbour loses an outgoing edge
      if e.outbound in transferred or e.outbound in pendingSourceOrSink:
        continue
      deltaOld = delta[e.outbound]
      shiftPendingBin(deltaOld, deltaOld - 1, e.outbound)

    transferred.incl x
    remaining -= 1

  template processGreedy() = # hotpath
    ## get item with next biggest delta and move it to sinks. Only one item.
    let maxd = getMaxDelta()
    #let v = pending[maxd].popLast()
    let v = pending[maxd].popLast()
    if pending[maxd].len == 0:
      pending.del maxd

    remove(v) # edges/flux updated, this can change the bin size
    sources.add v

  template processSources() =
    while pendingSources.len > 0:
      let s = pendingSources.pop()
      remove s
      sources.add s

  template processSinks() =
    while pendingSinks.len > 0:
      let s = pendingSinks.pop()
      remove s
      sinks.add s

  # Process queues/bins
  processSources
  processSinks
  while remaining > 0:
    processGreedy

  # write vertex ordering
  for ix in 0 .. (sources.len - 1):
    ordering[ix + 1] = sources[ix]
  for ix in 1 .. sinks.len:
    ordering[sources.len + ix] = sinks[^ix]

proc fasEadesLinSmith[T: Vertex](vertices: Iterable[T]): HashSet[Edge[T.D, T.M]] =
  ## Find ordering with ELS and convert to FAS
  var ordering = initVertexOrdering[T](vertices) # O(V+E) refs
  ordering.eadesLinSmith() # O(V+E)
  return ordering.fas()

proc fasEadesLinSmith*(graph: Graph): HashSet[Edge[Graph.D, Graph.M]] =
  fasEadesLinSmith[Vertex[Graph.D, Graph.M]](graph.vertices)

proc eadesLinSmith(graph: Graph): VertexOrdering[Vertex[Graph.D, Graph.M]] =
  var r = initVertexOrdering[VertexOrdering.V](graph.vertices)
  r.eadesLinSmith
  result = r

proc reorderPass[T: VertexOrdering](x: var T) =
  ## Make a pass of vertex ordering shifting vertices for backedge reduction
  ##
  ## Check all insertion gaps between neighbours of a given vertex and insert
  ## vertex into the gap with the least backedges
  type
    Nio = object # neighbour indices
      edgeto, edgefrom: seq[int] # edgeto leads to neighbour

    V = T.V

  # track vertices processed then moved forward (which scanner will revisit)
  # dont track all processed nodes, just ones forwarded into path of scan
  var preprocessed: HashSet[V]
  proc process(vo: var T, scanIndex: int, preprocessed: var HashSet[V] = preprocessed) =
    ## check gaps for vertex at scanIndex position of ordering and move to best
    ##
    ## Where forwarding the vertex;
    ##  * mark it as seen so when scan crosses it later it wont be reprocessed.
    ##  * process vertex bought into scan position by forwarding operation.
    if vo[scanIndex] in preprocessed:
      return # done
    let v = vo[scanIndex]
    var
      n: Nio
      bestCount: int # backedge count
      bestGap: int = -1 # Indice of gaps that contains best gap demarcation
      backedges = 0
      # values are indices of elements demarcating gap boundaries, when placing
      # the vertex in processing it should be
      #
      gaps: seq[int]

    # edge directed to neighbour
    for e in v.outbound:
      n.edgeto.add vo[e.inbound]
    # edge directed from neighbour
    for e in v.inbound:
      n.edgefrom.add vo[e.outbound]

    bestCount = n.edgeto.countIt(it < scanIndex) + n.edgefrom.countIt(it > scanIndex)

    # Best gap neighbour is last, or first element in ordering
    # 1) Last. move(scanIndex, ^1) will backshift the last element leaving space
    #    for placement.
    # 2) First. move(scanIndex, 0) will forwardshift 0th element, leaving space
    gaps = @[0] & n.edgeto & n.edgefrom # indices
    gaps.sort(order = Ascending) # O(ElogE)
    gaps = gaps.deduplicate(isSorted = true) # O(E), dont double check both i/o nei

    let
      # index of first gap bigger or last, O(log(N))
      postGapX = gaps.upperBound(scanIndex)
      currentGap =
        if postGapX == gaps.len:
          gaps[^1]
        else:
          gaps[postGapX - 1] # scanIndex >= 0 -> postGapX > 0

    # Check insertion positions. Insertion will be immediately after demarcator
    for g in gaps: # neighbour gaps
      if g == currentGap:
        continue # already here
      backedges = n.edgeto.countit(it <= g) + n.edgefrom.countit(it > g)
      if backedges < bestCount:
        bestCount = backedges
        bestGap = g
        if backedges == 0:
          break # best we can do

    # found a swap improvement
    if bestGap != -1:
      # Current vertex at position scanIndex, bestGap < scanIndex -1 or otherwise
      # bestGap will be the current gap, and similarly bestGap > scanIndex
      assert (bestGap < scanIndex - 1) or (bestGap > scanIndex)

      # moving backwards, we are forward shifting vertex at current destination
      # moving forwards, we are pulling vertex at bestgap back a position
      if scanIndex > bestGap:
        vo.moveto(scanIndex, bestGap + 1) # backwards
      else: # forwards may bring unprocessed vertex to scanIndex slot
        vo.moveto(scanIndex, bestGap)
        preprocessed.incl vo[bestGap] # processed forwarded vertex in this call
        process(vo, scanIndex) # process pulled in node, will skip if seen

  # check gaps and swap to best position
  for scanIndex in 1 .. x.biggest:
    x.process(scanIndex)

proc fasOptimizedEadesLinSmith[T: Vertex](
    vertices: Iterable[T], passes = 3, # Optimization passes
): HashSet[Edge[T.D, T.M]] =
  var ordering: VertexOrdering[T] = initVertexOrdering[T](vertices) # O(V+E) refs
  ordering.eadesLinSmith() # O(V+E)
  for ix in 1 .. passes:
    ordering.reorderPass()
  return ordering.fas()

proc fasOptimizedEadesLinSmith*(
    graph: Graph, passes = 3
): HashSet[Edge[Graph.D, Graph.M]] =
  ## Use ELS to generate ordering and then optimize it by making relocation passes
  ## to shift vertices to optimal gap. AKA iterative local search.
  graph.vertices.fasOptimizedEadesLinSmith(passes)

proc test[D, M](
    constraint: ConnectivityConstraint,
    g: Graph[D, M],
    fas: HashSet[Edge[D, M]] = initHashSet[Edge[D, M]](),
): bool =
  ## Test if graph satisfies constraint where given FAS applied
  ##
  ## ccAcyclic will leverage cached SCC computation
  ##
  case constraint
  of ccAcyclic:
    let efilter: EdgeFilter[D, M] = EdgeFilter[D, M](
      semanticHash: fas.hash,
      predicate: some(
        proc(x: Edge[D, M]): bool {.closure, nosideeffect, gcsafe.} =
          x in fas
      ),
    )
    # Acyclic every SCC is a singleton (no multi-vertex SCC => no cycle) and no
    # singleton has a self edge
    for c in g.sccs(efilter = efilter):
      if c.vertices.len > 1:
        return false # more than one vertex in an scc is a cycle
      if c.vertices.chooseAny.selfEdges.len > 0:
        # filterIt keeps items *fulfilling* the predicate, the filter is the opposite
        if c.vertices.chooseAny.selfEdges.filterIt(not efilter(it)).len > 0:
          return false # self edge
    return true # all sccs acyclic
  else: # all others unimplemented
    return false

proc test[D, M](
    constraint: ConnectivityConstraint, s: SCC[D, M], fas: HashSet[Edge[D, M]]
): bool =
  ## Test the given (scc) feedback arc set meets the constraint
  ##
  ## Edgeset constraints:
  ##   Acyclic: No cycles or self edges exist
  ##   Local Traversibility: There exists a root node in the component from which
  ##   all other nodes may be reached. One source node.
  ##   Weak Connectivity: There exists an undirected path to all other nodes in
  ##    from any given node. Weak connectivity ensures weak global connectivity.
  ##   ThoroughfarePreservation: Given an SCC B, if SCC A feed into B and B feeds
  ##    into SCC C, the A infeed vertex may reach the C outfeed vertex via a
  ##    directed path after pruning.
  ##
  ## To check local traversibility is O(N+M), a directed DFS or BFS search
  ##
  ## Weak connectivity is O(N+M), an undirected BFS or DFS
  ##
  ## Thoroughfare preservation requires checking that each entry vertex can reach
  ## any exit vertex. This is the most restrictive constraint. The brute force
  ## search space can be restricted by identifying forced edges. These are the
  ## edges that must exist for vertex A to reach B regardless of the path taken
  let efilter = EdgeFilter[D, M](
    semanticHash: hash(fas),
    predicate: some(
      proc(x: Edge[D, M]): bool =
        x in fas
    ),
  )
  case constraint
  of ccAcyclic: # O(V+E)
    # Acyclic iff every SCC is a singleton (no multi-vertex SCC => no cycle)
    # and no singleton has a self edge
    for c in sccs[Vertex[D, M]](s.vertices, efilter):
      if c.vertices.len > 1:
        return false
      if c.vertices.chooseAny.selfEdges.filterIt(not efilter(it)).len > 0:
        return false
    return true
  of ccWeak: # O(V+E)
    var length = 0
    for vscc in s:
      for v in vscc.dfs(undirected = true, edgefilter = efilter):
        length += 1
      break # all vertices reachable from any vertex in an SCC
    if length == s.vertices.len:
      return true
  of ccTraversible: # O(V+E)
    var root: Vertex[D, M]
    for vx in sources[Vertex[D, M]](s.vertices, efilter):
      if not root.isnil: # only one root allowed
        return false
      root = vx
      var length = 0
      for dfsv in vx.dfs:
        length += 1
      return length == s.vertices.len() # DFS should find all nodes
  # of ccThoroughfare:
  #   ## For SCC A, B, C, if the condensed graph has A -> B -> C then post pruning
  #   ## edges of B, A can still reach a vertex of C via the vertices of C.
  #   # 1) Mark inbound vertices. 2) Mark outbound vertices. 3) Locate forced edges
  #   # 4) See if any backedge is a forced edge. If so, constraint fails.
  #   # 5) Check that entry nodes may reach all exit nodes
  #   return false

proc bruteVertexOrdering[T: Vertex](
    s: SCC[T.D, T.M], constraints: set[ConnectivityConstraint] = {}
): Option[VertexOrdering[T]] =
  if s.singleton(): # base case
    return some(initVertexOrdering[T](s.vertices))
  var
    usage = fac(len(s.vertices))
    seen: HashSet[T]
    minimum: int = int.high
    bestOrder: VertexOrdering[T]
    backEdges: HashSet[Edge[T.D, T.M]]

  # permutor modifies the seq in place; operate on a local copy to avoid
  # mutating s.vertices during iteration
  var vertices = s.vertices.toSeq

  for ordering in permutor(vertices): # O(V!)
    for v in ordering: # backedge set O(E), scan all edges
      for e in v.outbound:
        if e.inbound in seen:
          backedges.incl e
      seen.incl v

    if card(backedges) < minimum: # new possible best
      var allPass = true
      for c in constraints:
        if not c.test(s, backedges):
          allPass = false
          break
      if allPass:
        minimum = card(backedges)
        bestOrder = VertexOrdering[T]()
        for (ix, e) in enumerate(ordering):
          bestOrder[ix + 1] = e # vertex orderings are 1 indexed not 0

    seen.clear
    backedges.clear

  if minimum < int.high:
    return some(bestOrder) # FAS matching constraints found
  else:
    return none(VertexOrdering[T]) # No FAS located

proc fasBruteVertexOrdering*(
    scc: SCC, constraints: set[ConnectivityConstraint] = {}
): Option[HashSet[Edge[SCC.D, SCC.M]]] =
  ## Brute force MFAS through left to right vertex ordering for all vertex O(V!)
  ## orderings, enumerate back edges.
  ##
  ## Excepting singletons it is invariant that a SCC has at least one cycle. Any
  ## ordering shall have at least one back edge and meet the weakly connected
  ## criteria since any vertex is reachable from any other by definition.
  ##
  ## Note weakly connected does not account for edge direction.
  var order = bruteVertexOrdering[Vertex[SCC.D, SCC.M]](scc, constraints)
  if order.issome():
    result = order.get().fas.some()
  else:
    result = none[HashSet[Edge[SCC.D, SCC.M]]]()

proc fasBruteEdgeset*(
    s: SCC, constraints: set[ConnectivityConstraint] = {}
): Option[HashSet[Edge[SCC.D, SCC.M]]] =
  ## Brute force MFAS through trying edge set combinations O(2^E).
  ##
  ## Additional conditions for the FAS can be imposed
  ##
  ## No iterator return for efficiency here as we must find the full edgeset
  ##
  ## A none() return represents that no edge set was found meeting the constraints
  ##
  ## Any fas will include all self edges
  # combinator expects an openArray; collect edges into a seq first
  var edges: seq[Edge[SCC.D, SCC.M]]
  var selfedges: HashSet[Edge[SCC.D, SCC.M]]
  var thisEdgeset: HashSet[Edge[SCC.D, SCC.M]]
  for v in s.vertices:
    for e in v.outbound:
      edges.add e
    for e in v.selfedges:
      selfedges.incl e

  for edgeset in edges.combinator:
    thisEdgeset = selfedges
    thisEdgeset.incl edgeset
    if ccAcyclic.test(s, thisedgeset):
      var passed = 0
      for c in constraints:
        if c == ccAcyclic: # already tested
          passed += 1
          continue
        if c.test(s, thisedgeset):
          passed += 1
        else:
          break
      if passed == constraints.len: #
        return some(thisedgeset)
  return none(HashSet[Edge[SCC.D, SCC.M]])

proc pickFasAlgorithm(s: SCC): FasStrategy =
  ## Brute force or Eades-Lin-Smith depending on SCC size
  ##
  ## Can further tweak with computation budgets as future development direction
  var N: int = s.vertices.len()
  var M: int = 0
  for x in s.vertices:
    M += len(x.outbound) # set of outbound encompasses all inbound

  if M <= BRUTE_EDGES:
    return fsBruteEdgeset
  if N <= BRUTE_VERTICES:
    return fsBruteVertexOrder
  if N > JUST_ELS:
    return fsEls
  return fsElsReorder

proc fas*(g: Graph): HashSet[Edge[Graph.D, Graph.M]] =
  ## Derive a close to or minimal feedback arc set (FAS)
  ##
  ## This is done by finding a graphs condensation, iterating over the strongly
  ## connected components (SCC) and finding a FAS for each component. The graph
  ## FAS is the union of these SCC FAS.
  ##
  ## Let A, B be any two SCCs. No edge B-A can be a backedge. If B is reachable
  ## from A, then all vertices of A are reachable from B and vice versa thus A
  ## and B would be a single SCC. If B is not reachable from A, the B-A is not
  ## a backedge.
  ##
  ## ## Computational budget
  ## Large graphs are not feasible to brute force. Break into SCC, brute force
  ## small SCC, ELS+Reorder medium-large and ELS very large SCCs". Track
  ## computational complexity and take less intensive avenues once a computation
  ## budget is exhausted
  ##
  ## Avenues
  ##  * Eades Lin Smith (ELS) heuristic (lowest compute)
  ##  * ELS and optimal gap vertex reordering passes (low compute)
  ##  * Brute vertex ordering or edge set (only useful for very small SCCs)
  ##
  ## Algorithm
  ## 1) Condense graph
  ## 2) Accumulate FAS
  ##   2a) Iterate SCC topologically
  ##   2b) Generate FAS per SCC
  var
    scc: SCC[Graph.D, Graph.M]
    cumulator: HashSet[Edge[Graph.D, Graph.M]]

  for vx in g.condensation().vertices:
    scc = vx.data
    if scc.singleton: # no fas in this unless it has a selfedge
      for e in scc.chooseAnyVertex.selfEdges: # just the one vertex
        cumulator.incl e
    else:
      cumulator.incl:
        case scc.pickFasAlgorithm
        of fsEls:
          fasEadesLinSmith[Vertex[Graph.D, Graph.M]](scc.vertices)
        of fsElsReorder:
          fasOptimizedEadesLinSmith[Vertex[Graph.D, Graph.M]](scc.vertices, passes = 3)
        of fsBruteVertexOrder:
          (scc.fasBruteVertexOrdering()).get()
        of fsBruteEdgeset:
          scc.fasBruteEdgeset().get()

  return cumulator
