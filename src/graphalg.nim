## #
## :Author: Ben Tomlin
##
## Graph structure with useful algorithm implementations.
##
## Intended as a lower level implementation with enough detail exposed to be
## used for broad range of purposes. For example, walkDfs lists the
## traversed in DFS, which can be useful for algorithms that act at backtrack.
##
## Intended to be performant at scale but not use case optimized. If you want
## full optimization its best to implement your own fully specific to your use
## case using more performant structures like packed arrays. Memory is traded for
## computation - particularly to bound ccmplexity
##
## Edge and Vertex hold generic types to be suited for any purpose.
##
## # Strongly Connected Component
## Set of vertices, for which any vertex is reachable from any other by some path.
## A graph has a unique set of SCCs. All feedback arcs in a graph exist in SCCs.
##
## A single vertex is considered an SCC (provided any vertex that can reach to it
## cannot be reached from it). Such a vertex may have a self edge.
##
## # Feedback Arc Sets
## Set of edges that form cycles in a directed graph. Removing such edges will
## make the graph acyclic
##
## ## Algorithm
## Find all SCC. Find FAS per SCC. The union of all SCCs FAS is the graph FAS.
##
## # Condensation
## A graph can be collapsed into its SCCs. A vertex per SCC, with edges between
## SCCs as per the edges between their individual vertices. A condensation is
## useful for topologically sorting. By definition condensed graphs are acyclic.
##
## # Basis
## Set of vertices in a graph that from which all other vertices may be reached
## but no other basis vertex may be reached.
##
## # Finding Vertices
## Lookup vertices with a label, or with a data value. No distinct two vertices
## with the same label and data may exist.
import std/[tables, deques, math, sets, sugar, hashes, strutils, sequtils]
import std/[options, math]
import graphalg/[util]
import combinatronics, datastructures/bimap

const NONE_FILTER_HASH: Hash = 0
type
  ## There is an items iterator defined for the type
  Iterable[T] =
    concept x
      for element in x:
        element is T

  Edge*[D, M] = ref object
    ## edges to a vertex are stored both on the source and sink vertex.
    outbound*, inbound*: Vertex[D, M] ## vertex arc exits and enters
    meta*: M ## metadata, weights, applicability criteria etc

  Vertex*[D, M] = ref object
    label*: string
    data*: D # not necessarily unique, but label + data must be
    outbound*, inbound*: seq[Edge[D, M]]
    # When comparing edges with `==`, as ref object, the ref addresses themselves
    # are compared. Feedback arc sets and similar can generate edge instances for
    # self edges but each arc set construction will have then a different edge
    # instance to represent the same edge. We declare self edges as edge instances
    # so they are be canonical.
    selfEdges*: seq[Edge[D,M]] # suppord multiple self edges

  StronglyConnectedComponent[D, M] = ref object # root can be any node.
    vertices*: HashSet[Vertex[D, M]]

    # outbound encompasses all inter scc edges across all sccs. Use at condensation
    inbound*, outbound*: HashSet[Edge[D, M]]

    # Note the set of backedges is a property of the SCC root. Forming an SCC
    # with another root could result in a different set of backedgesv Backedges
    # form a feedback arc set, but not a minimal feedback arc set
    #backedges: HashSet[Edge[D, M]]

  Direction* = enum
    dOutbound # edge from node
    dInbound # edge to node
    dSelf # from self to self
    dAll

  SCC*[D, M] = StronglyConnectedComponent[D, M]

  # empty object for empty edge or node
  NoData* = object

  # Note that without D, M concrete we have a type class instead of an instantiation
  Graph*[D, M] = ref object
    ## Stores analysis and computation results
    ##
    ## The data types D and M should be hashable and lightweight or ref
    ##
    ## Note that basis, sccs and condensation depend on the vertices and edges
    ## that compose the graph. Many procedures/algorithms support filters, which
    ## exclude vertices and edges from a graph. Therefore, most caches are keyed
    ## on a hash which fingerprints the filter combination used to calculate the
    ## corresponding value.
    vertices*: OrderedSet[Vertex[D,M]] # all vertices, ordered for reproducibility

    basisCache: Table[Hash,seq[Vertex[D,M]]] # basis vertices, supercedes calculation

      ## hash values of edge filter semantic hashes to track SCCs for different
      ## prunings. The case for the SCC calculated  with no edge filter will be
      ## a "zero" value hash
    sccsCache: Table[Hash, seq[SCC[D,M]]] ## \
      ## Cached SCC calculations. Hash will represent some combination of filters
      ## used to prune (ignore edges) when the SCC was calculated

    # Where multiple vertices contain the same data they are differentiated by label
    dataToVertex: Table[D, Vertex[D,M]]
    labelToVertex: Table[string, Vertex[D,M]]
    dataToVertexOverflow: Table[D, seq[Vertex[D,M]]]
    labelToVertexOverflow: Table[string,seq[Vertex[D,M]]]

    vertexToScc: Table[Hash, Table[Vertex[D,M], SCC[D,M]]]

    # One vertex per SCC, edges between vertices of SCCs link them.
    # The condensation you get is dependant on the edgeset you use. The table
    # key represents the edgeset used to generate the SCCs, and thus the condensation
    # that derives
    condensationCache: Table[Hash, Graph[SCC[D,M], NoData]]

  Filter*[T] = object
    ## Filter items of type T matching predicate. By default, filter nothing.
    semanticHash: Hash = NONE_FILTER_HASH ## \
      ## Filters with the same semantic hash are equivalent
      ## 
      ## Enables caching calculation results that are a function of a filter. 
      ## 
      ## *It is manually set and its up to the programmer to provide a hash that 
      ## uniquely identifies the behaviour of their filter.* For example, an edge filter that
      ## removes all edges in a set, could have its semanticHash be the hash of the
      ## set of edges to remove. This hash can then is a unique fingerprint for the
      ## filter behaviour.
      ##  
      ## Some gotchas, if you fold a vertex filter into an edge filter, then only
      ## provide the edge filter as a dual purpose, then the semantic hash you set
      ## should be equivalent to that of which semanticHash_ would yield.
    predicate: Option[proc(x: T): bool {.closure, nosideeffect, gcsafe.}] ## \
      ## Where issome() and returns true, item x will be filtered
  EdgeFilter*[D,M] = Filter[Edge[D,M]]
  VertexFilter*[D,M] = Filter[Vertex[D,M]]

{.experimental: "callOperator".}
proc `()`(x: Filter, y: Filter.T): bool {.inline.} =
  if x.predicate.issome():
    (x.predicate.get())(y)
  else: false # no predicate, filter none default

proc semanticHash*(x: EdgeFilter, y: VertexFilter): Hash =
  ## Return a hash that represents the combined behavour of the given filters
  ##
  ## Where one filter is a noop then the hash of the other filter will be returned
  ## asis. Where both are noop then we will get the NONE_FILTER_HASH
  ##
  ## This is useful to cache results that depend on filters.
  if x.predicate.isnone(): return y.semanticHash
  if y.predicate.isnone(): return x.semanticHash
  result = !$(x.semanticHash !& y.semanticHash) # mix, in order
proc semanticHash*(x: VertexFilter, y: EdgeFilter): Hash = y.semanticHash x

proc hash[T: ref](x: T): Hash {.inline.} =
  ## the value of x is a memory address since it is a ref type
  cast[Hash](x)

proc selfEdge(e: Edge): bool {.inline.} = e.outbound == e.inbound

proc `$`*(g: Graph): string =
  for v in g.vertices.items:
    result &= v.pprint & "\n"

proc repr*(v: Vertex): string =
  var
    outs = collect:
      for e in v.outbound:
        e.inbound.label
    ins = collect:
      for e in v.inbound:
        e.outbound.label

  let spacer = ' '.repeat(len(v.label) + 2)
  result = "$#: out  $#,\n$#in   $#" % [v.label, $outs, spacer, $ins]

proc `$`*(v: Vertex): string {.inline.} =
  v.label

proc pprint(v: Vertex): string {.inline.} =
  &"Label: {v.label}\nOut:   {v.outbound}\nIn:    {v.inbound}"

proc `$`*(e: Edge, revArrow = false): string =
  if revArrow: # backtracking edge (we move backwards on the edge direction)
    "$# <- $#" % [e.outbound.label, e.inbound.label]
  else:
    "$# -> $#" % [e.outbound.label, e.inbound.label]

proc `$`*(s: SCC): string =
  let elems: seq[string] = collect:
    for v in s.vertices:
      v.label
  return "{$#}" % [elems.join(", ")]

proc initVertex*[D, M = NoData](label: string, data: D = default(D)): Vertex[D, M] =
  Vertex[D, M](label: label, data: data)


proc add*[D, M](g: Graph[D, M], v: Vertex[D, M]) =
  g.vertices.incl v
  g.mapVertexLookup v

proc initGraph*[D, M](v: openArray[Vertex[D, M]]): Graph[D, M] =
  result = Graph[D, M]()
  for vx in v:
    result.add vx

proc mapVertexLookup[D, M](g: Graph[D, M], vx: Vertex[D, M]) =
  ## Maintain vertex lookup by data and label
  ##
  ## Require label and data combination is unique

  if vx.data in g.dataToVertex: # data indice overflow, assert label unique
    let labels = # labels of vertices with equivalent data
      iterator (): string =
        yield g.dataToVertex[vx.data].label
        for v in g.dataToVertexOverflow.getOrDefault(vx.data):
          yield v.label

    for l in labels:
      if l == vx.label:
        raise ValueError.newException "Multiple vertices with same data and label"

    # invariant the label+data of this vertex is unique
    g.dataToVertexOverflow.mgetOrPut(vx.data).add(vx)
  else:
    g.dataToVertex[vx.data] = vx

  if vx.label in g.labelToVertex: # make sure data tiebreaks
    g.labelToVertexOverflow.mgetOrPut(vx.label).add vx
  else:
    g.labelToVertex[vx.label]=vx
proc initGraph*[D, M](v: iterator (): Vertex[D, M]): Graph[D, M] =
  # More flexible iterator
  result = Graph[D,M]()
  for vx in v():
    result.add vx

iterator items*(x: SCC): Vertex[SCC.D, SCC.M] =
  ## Vertices in SCC in an unspecified order
  for v in x.vertices: yield v

iterator items*(g: Graph, f: VertexFilter): Vertex[Graph.D,Graph.M] =
  ## Vertices in graph in an unspecified order
  for v in g.vertices:
    if not f(v): yield v

proc connectTo*[D, M](vfrom, vto: Vertex[D, M], meta: M = default(M)) =
  # Creates an edge from one vertex to another
  var e: Edge[D, M] = Edge[D, M](outbound: vfrom, inbound: vto, meta: meta)
  vfrom.outbound.add e
  vto.inbound.add e

proc connectFrom*[D, M](vto, vfrom: Vertex[D, M], meta: M = default(M)) =
  var e = Edge[D, M](outbound: vfrom, inbound: vto, meta: meta)
  vfrom.outbound.add e
  vto.inbound.add e

proc connectToSelf*(x: Vertex, meta: Vertex.M = default[Vertex.M](Vertex.M)) =
  let e = Edge[Vertex.D, Vertex.M](outbound:x,inbound:x,meta:meta)
  x.selfEdges.add e

iterator edges*[D, M](v: Vertex[D, M], direction: Direction = dOutbound, filter: EdgeFilter[D,M]=default(EdgeFilter[D,M])): Edge[D, M] =
  ## Iterate edges
  let f = filter
  case direction
  of dOutbound:
    for e in v.outbound:
      if not f(e): yield e
  of dInbound:
    for e in v.inbound:
      if not f(e): yield e
  of dSelf:
    for e in v.selfEdges:
      if not f(e): yield e
  of dAll:
    for e in v.outbound:
      if not f(e): yield e
    for e in v.inbound:
      if not f(e): yield e
    for e in v.selfEdges:
      if not f(e): yield e

iterator edges*[D, M](g: Graph[D, M], direction = dOutbound, filter: EdgeFilter[D,M] = default(EdgeFilter[D,M])): Edge[D, M] =
  ## All edges in graph. Note that outbound edge A->B will be outbound for A,
  ## and inbound for B. All edges are outbound for some vertex and vice versa.
  ## dAll then will iterate over the full set of edges twice
  for v in g.vertices:
    for e in v.edges(direction, filter):
      yield e

iterator neighbours*(v: Vertex, d: Direction = dOutbound): Vertex =
  ## Neighbours reachable from, that reach to vertex or both, include self edges
  ##
  ## Neighbours reachable from multiple edges will be yielded more than once
  case d
  of dOutbound:
    for e in v.outbound:
      yield e.inbound
  of dInbound:
    for e in v.inbound:
      yield e.outbound
  of dSelf:
    for e in v.selfEdges:
      yield v
  of dAll:
    for e in v.outbound:
      yield e.inbound
    for e in v.inbound:
      yield e.outbound
    for e in v.selfEdges: yield v

iterator walkDfs[D, M](
    vertices: iterable[Vertex[D, M]] | iterator (): Vertex[D, M],
    edgeFilter: EdgeFilter[D,M] = default(EdgeFilter[D,M]), ## no filter
    vertexFilter: VertexFilter[D,M] = default(VertexFilter[D,M]),
): tuple[entry: int, edge: Edge[D, M]] =
  ## Walk edges in DFS order. emitting on entry and exit
  ##
  ## first element is 1 for entry, 0 for exit
  ##
  ## Entry is traversal of edge, from outbound to inbound
  ## Backtracks (exit) will be the reverse of the edge
  ##
  ## DFS will stack all children for processing, and pop the stack for next node
  ## to process. Where a child has been seen (added to the stack) then it will
  ## be ignored.
  ##
  ## This iterator walks edges of DFS. An edge to a node is emitted when we enter
  ## that node for processing. Backtracking occurs when a node has no children
  ## left to visit.
  ##
  ## Note no enter emission occurs for root nodes as they are without an edge
  ## leading into them.
  ##
  ## Singletons with no edges have no emission
  var
    path: seq[Edge[D, M]] # path through tree to current node in processing
    seen: HashSet[Vertex[D, M]] # entered vertices
    keepEdge = proc(e: Edge[D, M]): bool = not edgeFilter(e) and not vertexFilter(e.inbound)
    stack: seq[Edge[D, M]]
    # queue root edges
  for v in vertices:
    if v in seen:
      continue
    seen.incl v
    stack = v.outbound.filter keepEdge
    while stack.len() > 0: # process edges (not nodes)
      var ex = stack.pop()
      var vx = ex.inbound # node in processing
      path.add ex
      seen.incl ex.inbound
      yield (1, ex) # enter node

      var initEdges = stack.len
      for edge in vx.outbound:
        if not keepEdge(edge):
          continue
        if edge.inbound notin seen: # tree edge, advance at next stack.pop
          stack.add edge

      # backtrack
      if stack.len == initEdges: # no edges to walk, backtrackpath
        if stack.len == 0: # final node was processed, backtrack whole path
          while len(path) > 0:
            yield (0, path.pop()) # exit
        else:
          # supports edge case where next edge comes from the root
          # stack[^1].outbound is the node we are next stepping from
          while stack[^1].outbound != path[^1].outbound: # backtrack one path step
            yield (0, path.pop()) # exit
          yield (0, path.pop) # back path up to the next node in processing

# Vertex without its type parameters D, M introduce two implicit generic parameters
# to this signature. Further references to Vertex is the concrete type that was
# bound it its first introduction to the signature (the anchor parameter)
#
# Signatures with such implicit generic parameters are more convenient than declaring
# explicit generic parameters for the signature. Explicit and implicit parameters
# are inferred from the parameters where possible. Explicit generic parameters
# provided in square brackets at a call site offer greater control for a cost of
# more verbosity
#
# **nimdoc**
iterator dfs*[D, M](
    anchor: Vertex[D, M],
    edgeFilter: EdgeFilter[D, M] = default(EdgeFilter[D, M]),
    vertexFilter: VertexFilter[D, M] = default(VertexFilter[D, M]),
    undirected: bool = false,
): Vertex[D, M] {.closure.} =
  ## Emit vertices in DFS visitation order, ignoring filtered edges or vertices
  ##
  ## Visitation order dependant on order of the vertices iterable. A -> B -> C
  ## with iterable in order "ABC" visits in order "ABC". "BAC" in order "BCA".
  ##
  ## Visitation order for A->B->{C,D} is A, B, D, C
  var
    seen: HashSet[Vertex[D, M]]
    stack: seq[Vertex[D, M]]

  stack = @[anchor]
  while stack.len() > 0:
    let cursor = stack.pop()
    seen.incl cursor
    yield cursor
    for edge in cursor.outbound: # Edges from node
      if edgeFilter(edge) or vertexFilter(edge.inbound): continue
      if edge.inbound notin seen: stack.add edge.inbound

    if undirected: # Include backwards traversal of edges
      for edge in cursor.inbound:
        if edgeFilter(edge) or vertexFilter(edge.outbound): continue
        if edge.outbound notin seen: stack.add edge.outbound

iterator dfs*[D, M](
  graph: Graph[D, M],
  edgeFilter: EdgeFilter[D,M] = default(EdgeFilter[D,M]),
  vertexFilter: VertexFilter[D,M] = default(VertexFilter[D,M]),
  undirected: bool = false
): Vertex[D,M] {.closure.} =
  ## Assumes basis is valid (all vertices reachable from basis, no basis vertex
  ## reachable from any other)
  for v in graph.basis:
    for vx in v.dfs(edgeFilter, vertexFilter, undirected):
      yield vx

iterator bfs*(anchor: Vertex): Vertex =
  # Emit vertices in BFS
  type V = Vertex
  var q: Deque[V] = initDeque[V]()
  var seen: HashSet[V] # seen != processed
  q.addLast anchor
  seen.incl anchor
  while q.len() > 0:
    let cursor = q.popFirst()
    yield cursor
    for edge in cursor.outbound:
      if edge.inbound notin seen:
        q.addLast edge.inbound
        seen.incl edge.inbound
iterator bfs*(graph: Graph): Vertex[Graph.D, Graph.M] =
  ## Assumes basis is valid (all vertices reachable from basis, no basis vertex
  ## reachable from any other)
  for v in graph.basis:
    for vx in v.bfs:
      yield vx

proc flux*[D, M](
    v: Vertex[D, M],
    efilter: EdgeFilter[D,M] = default(EdgeFilter[D,M]),
    countSelfEdges: bool = true
): tuple[i, o: int] =
  ## Find {in,out}degree
  ## 
  ## efilter: when true filter the edge (the edge wont count toward the flux)
  for e in v.outbound:
    if not efilter(e): result.o += 1
  for e in v.inbound:
    if not efilter(e): result.i += 1
  if countSelfEdges:
    for e in v.selfEdges:
      if not efilter(e):
        result.i+=1
        result.o+=1

proc lookup*[D, M](g: Graph[D, M], d: D, label = none[string]()): Vertex[D, M] =
  ## Find a vertex in graph by data, tiebreak with label
  ##
  ## Given a data value find the vertex associated with that data, Supply a
  ## label to differentiate vertices with the same data where necessary.
  if d in g.dataToVertexOverflow:
    if label.isnone():
      raise ValueError.newException &"Multiple vertices have data {d} and no label supplied to differentiate"
    for v in (
      iterator (): Vertex[D, M] =
        yield g.dataToVertex[d]
        for vv in g.dataToVertexOverflow[d]:
          yield vv

    ):
      if v.label == label.get():
        return v
      raise ValueError.newException &"No vertex with data {d} and label {label}"
  else:
    return g.dataToVertex[d]

proc lookup*(g: Graph, label: string, data=none[Graph.D]()): Vertex[Graph.D,Graph.M] =
  ## Lookup vertex by label break tie with data
  if label in g.labelToVertexOverflow:
    if data.isnone():
      raise ValueError.newException "Multiple vertices of same label and no data given to differentiate"
    let vxs = iterator(): Vertex[Graph.D,Graph.M] =
      yield g.labelToVertex[label]
      for vx in g.labelToVertexOverflow.getOrDefault(label): yield vx
    for vx in vxs:
      if vx.data == data.get():
        return vx
    raise ValueError.newException &"No vertex exists in graph for label {label} with data {data.get()}"
  else:
    g.labelToVertex[label]

proc fluxd*(v: Vertex): int =
  let f = v.flux
  f.o - f.i

proc source*(v: Vertex): bool {.inline.} =
  v.flux.i == 0 and v.flux.o > 0

proc sink*(v: Vertex): bool {.inline.} =
  v.flux.i > 0 and v.flux.o == 0

proc isolated*(v: Vertex): bool {.inline.} =
  ## Defined as vertex with no incoming or outgoing edges
  v.flux.i == 0 and v.flux.o == 0

proc isolated*(scc: SCC): bool {.inline.} =
  ## SCC with no vertices containing edges to or from an external vertex, may be multiple vertices

  for v in scc:
    for e in v.edges(dOutbound):
      if e.inbound notin scc.vertices:
        return false
    for e in v.edges(dInbound):
      if e.outbound notin scc.vertices:
        return false
  return true

proc singleton*(scc: SCC): bool {.inline.} =
  ## Single vertex that may or may not connect to other sccs
  scc.vertices.card == 1

iterator sccs[V: Vertex](
    vertices: Iterable[V],
    efilter: EdgeFilter[V.D,V.M] = default(EdgeFilter[V.D,V.M]),
    vfilter: VertexFilter[V.D,V.M] = default(VertexFilter[V.D,V.M])
): SCC[V.D, V.M] =
  ## Return all SCCs discoverable from given vertices. Uses iterative implementation
  ## of Tarjans SCC.
  ##
  ## Filtered edges will be ignored. Edges not filtered but leading
  ## to or from filtered vertices will be ignored.
  ##
  ## low[v] tracks the lowest discovery index of a node reachable from v
  ## disc[v] is the discover index of a vertice
  ##
  ## DFS recursion stack is the path down the tree to the current node. An
  ## iterative version of this is kept. This will be called the pathstack. We
  ## will refer to the recursion stack nonetheless, despite not recursing. To
  ## identify the next node up the recursion stack, we need to identify parent
  ## of the node being processed.  Rather than tracking nodes to process on the
  ## DFS stack we track edges. This allows us to identify this parent.
  ##
  ## A DAG may be traversed DFS to find the following edge types;
  ##  1) Tree: Edge leading to a undiscovered node
  ##  2) Back: Edge to an ancestor
  ##  3) Forward: Edge to a discovered node that is not an ancestor
  ##  4) Cross:
  ##
  ## Forward, reach to discovered descendants (may or may not be in same SCC)
  ## Back, reach to ancestors, these are in the same SCC
  ## Cross, reach to other discovered SCCs
  ## Tree, reach to new nodes
  ##
  ## Some terminology;
  ##  * Ancestor: Node from which the current can be reached and which has a
  ##    lower discovery index than the current.
  type
    G = Graph[V.D, V.M]
    E = Edge[V.D, V.M]
    S = SCC[V.D, V.M]

  var
    disc, low: Table[V, int]

    dfs, path: seq[E]
    tarjan: seq[V]
    seen, tarjanSet: HashSet[V]

    dindex = 0

  template discover(v: V) =
    ## Enter a node (begin its processing)
    disc[v] = dindex
    low[v] = dindex
    tarjan.add v
    tarjanSet.incl v
    dindex += 1

  template yieldScc(sccRootExpr: V) =
    let sroot = sccRootExpr
    var
      scc = S()
      done = false

    while not done: # put vertices
      var vertice = tarjan.pop()
      if vertice == sroot:
        done = true
      tarjanSet.excl vertice
      scc.vertices.incl(vertice)

    yield scc

  template backtrack(backedgeExpr: E) =
    ## Leave a node (complete its processing)
    ## backpropagate low, and check for SCC discovery at node backtracked from
    var
      backedge = backedgeExpr
      backTo = backedge.outbound # backtrack - edge is reversed
      backFrom = backedge.inbound

    low[backTo] = min(low[backTo], low[backFrom])
    if disc[backFrom] == low[backFrom]: # SCC found
      yieldScc backFrom

  for anchor in vertices:
    if anchor notin seen: # DFS search from here
      # initialize (enter the start node)
      discover anchor

      defer:
        yieldScc anchor
        # yield scc at anchor (invariant)

      # From anchor explore edges to unseen nodes
      seen.incl anchor
      for eg in anchor.outbound:
        if efilter(eg): continue # ignore edges marked as pruned
        if not vfilter(eg.inbound) and eg.inbound notin seen:
          dfs.add eg
          seen.incl eg.inbound

      # process edges (nodes)
      while dfs.len > 0:
        var
          edge = dfs.pop()
          v = edge.inbound # node entered
          stackDelta = dfs.len()

        path.add edge # track tree pathway (for recursion stack)
        discover v # we are visiting v, the node  the edge steps to

        for e in v.outbound: # node edges
          if efilter(e): continue
          var w = e.inbound # w is a child of v (an edge goes v->w)
          if not vfilter(w) and w notin seen: # undiscovered (tree edge)
            dfs.add e
            seen.incl w
          else: # discovered (back edge, cross edge, forward edge)
            if w in tarjanSet: # back edge, else cross edge (non exhaustive)
              low[v] = min(low[v], disc[w]) # neighbour to pull down the low

        # If no edges added for DFS processing, we are backtracking.
        # Backtrack as far as the next in progress node
        # This replaces the recursion stack (to accomodate larger graphs)
        if (dfs.len() - stackDelta) == 0:
          # special case we have completed DFS
          proc dfsCompletePathNotEmpty(): bool =
            dfs.len() == 0 and path.len() > 0

          # dfs[^1].outbound is the node whose child will be processed next
          proc pathOverExtended(): bool =
            path[^1].inbound != dfs[^1].outbound

          while path.len > 0 and (dfsCompletePathNotEmpty() or pathOverExtended()):
            backtrack path.pop()

iterator sccs*(g: Graph, filterSemanticHash: Hash): SCC[Graph.D,Graph.M] =
  ## Cached result lookup
  for s in g.sccsCache[filterSemantichash]: yield s
    
iterator sccs*(
    g: Graph,
    efilter = default(EdgeFilter[Graph.D,Graph.M]), ## filter edges, default filters none
    vfilter = default(VertexFilter[Graph.D,Graph.M]), ## filter vertices, default filters none
): SCC[Graph.D, Graph.M] =
  ## Iterate SCC of graph, with caching layer. No filters passed will not filter
  ## any vertices/edges.
  ##
  ## Different edge filters produce differing SCC, and therefore the calculation
  ## is cached on a semanticHash of the filters combined
  let cacheKey = semanticHash(efilter, vfilter)
  if cacheKey in g.sccsCache: # use cached result
    # **nimdoc** note that Graph has an sccs field and sccs iterator. Usually
    # in a loop context sccs resolves to an iterator. With square brackets, we
    # now have a call `[]`, which applies to a field
    for c in g.sccsCache[cacheKey]:
      yield c
  else:
    g.sccsCache[cacheKey] = @[]
    for c in sccs[Vertex[Graph.D, Graph.M]](g.vertices, efilter, vfilter):
      g.sccsCache[cacheKey].add c
      yield c

proc whichScc[D, M](
  g: Graph[D, M],
  vertex: Vertex[D, M],
  efilter: EdgeFilter[D,M] = default(EdgeFilter[D,M]),
  vfilter: VertexFilter[D,M] = default(VertexFilter[D,M])): SCC[D, M] =
  ## Given a vertex in the graph find the SCC it is in. 
  ## 
  ## Calculate answer if required and cache 
  ##
  ## This assumes that the SCCs are derived for the graph with no edges removed.
  ##
  ## Otherwise note that this will be dependant on what edge filters were used to
  ## find the SCC. Different filters, different set of SCCs. The filterSemanticHash identifies the
  ## combination of filters in play at SCC calculation thus a set if SCCs.
  ## Implementation for support of other SCC is not required yet. If this were
  ## to be done then rather than passing a cache key one should pass edge/vertex
  ## filters.
  let semHash: Hash = semanticHash(efilter,vfilter)
  if semHash in g.vertexToScc: # cache hit
    assert (vertex in g.vertexToScc[semHash]), "Vertex not known or filtered/unreachable"
    return g.vertexToScc[semHash][vertex]
  else: # miss. find all sccs (if not cached) and map all vertices to SCCs
    for scc in g.sccs(efilter, vfilter): # resolve to iterator not field
      # we want to iterate through all SCCs as this way the caluclation is cached
      for v in scc:
        var t = g.vertexToScc.getOrDefault(semHash)
        t[v] = scc
        if vertex == v: result = scc

proc condensation*[D, M](g: Graph[D, M],
  edgeFilter: EdgeFilter[D,M] = default(EdgeFilter[D,M]),
  vertexFilter: VertexFilter[D,M] = default(VertexFilter[D,M])
): Graph[SCC[D,M],NoData] =
  ## Take a graph and reduce it to an equivalen graph with one vertex per SCC
  ##
  ## Find all SCCs in graph. Generate a vertex for each. For all SCC outbound
  ## edges of SCC internal vertices, lookup the SCC they connect with. Given
  ## the two connected SCCs, add an edge between their SCC vertices.
  ##
  ## SCCs made of single vertices will have self edges if those vertices do.
  ## SCCs made of multiple vertices will have a self edge for every vertex that
  ## has a self edge
  ##
  ## SCCs dependant on the edges/vertices of the graph. Filters alter the SCCs.
  ## The condensation applies to the graphs full set of edges and vertices
  let cachekey = semanticHash(edgeFilter,vertexFilter)
  if cachekey in g.condensationCache:
    return g.condensationCache[cacheKey]
  else: # generate condensation
    # create vertices
    var condensationTable = collect:
      for c in g.sccs(edgeFilter,vertexFilter): # The vertices of condensation are SCCs of graph
        {c: Vertex[SCC[D, M], NoData](label: $c, data: c)}

    g.condensationCache[cacheKey] = Graph[SCC[D, M], NoData]()

    # wire vertex edges
    for scc, sccvx in condensationTable:
      # Tarjans SCC is limited to provide a subset of crossedges, as tree edges
      # may also be cross edges, thus we cannot cache discovered cross edges
      # during Tarjans SCC and must scan the vertices of the SCC
      for v in scc:
        for e in v.outbound:
          if e.inbound in scc.vertices: continue # intrascc
          let peer = g.whichScc(e.inbound, edgeFilter, vertexFilter)
          if peer == scc:
            assert false # we already caught the intrascc case above
            continue
          var vto = condensationTable[peer]
          var vfrom = sccvx
          vfrom.connectTo(vto) # connect condensed vertices
        for e in v.selfEdges:
          sccVx.connectToSelf()

    # fill out the graph with all condensed vertices
    for v in condensationTable.values():
      g.condensationCache[cacheKey].add v

    return g.condensationCache[cacheKey]

iterator sources[T: Vertex](
    v: Iterable[T],
    filter: EdgeFilter[T.D,T.M],
): T =
  ## iterate sources in vertex iterator with edges matching filter ignored
  for vx in v:
    var flux = vx.flux(filter)
    if flux.i == 0 and flux.o > 0:
      yield vx

iterator sources*(g: Graph): Vertex[Graph.D, Graph.M] =
  ## Sources are all nodes that may not be reached from another (no incoming
  ## edges) and that have edges out to another node.
  ##
  ## Vertices with self edges  only are not considered sources
  for v in g.vertices:
    var flux = v.flux
    if v.flux.i == 0 and v.flux.o > 0:
      yield v

iterator sinks*(g: Graph): Vertex[Graph.D, Graph.M] =
  for v in g.vertices:
    var flux = v.flux
    if flux.i > 0 and flux.o == 0:
      yield v

iterator isolated*(g: Graph): Vertex[Graph.D,Graph.M] =
  ## Yield vertices that connect to none other than themselves
  for v in g.vertices:
    var flux = v.flux(countSelfEdges=false)
    if flux.i == 0 and flux.o == 0:
      yield v

proc resetBasis*[D,M](g: Graph[D,M],
  edgeFilter: EdgeFilter[D,M] = default(EdgeFilter[D,M]), ## no filter
  vertexFilter: VertexFilter[D,M] = default(VertexFilter[D,M])
) = g.basisCache.del semanticHash(edgeFilter,vertexFilter)

proc `basis=`*[D,M](g: Graph[D,M], vlabel: openArray[string], 
  edgeFilter: EdgeFilter[D,M] = default(EdgeFilter[D,M]), ## no filter
  vertexFilter: VertexFilter[D,M] = default(VertexFilter[D,M])
) =
  ## Set vertices with given labels as the basis, reset basis if empty argument
  ##
  ## This will supercede calculation of a basis by determining one by source SCCs
  ##
  ## Exception for basis vertices in graphs with multiple vertices of same label
  ##
  ## Its assumed the basis supplied is valid (all vertices in graph reachable via
  ## some basis vertex, no basis vertex reachable from any other)
  ## 
  ## Labels are required to be unique to manually set the basis like this
  let filterCacheKey = semanticHash(edgeFilter,vertexFilter)
  if vlabel.len == 0:
    g.resetBasis edgeFilter, vertexFilter
    return

  g.basisCache[filterCacheKey] = @[]
  for l in vlabel:
    g.basisCache[filterCacheKey].add g.lookup(label=l)

proc chooseAny(x: HashSet): HashSet.A =
  for xx in x:
    return xx
proc chooseAnyVertex(scc: SCC): Vertex[SCC.D,SCC.M] = scc.vertices.chooseAny

proc basis*[D,M](g: Graph[D,M],
  edgeFilter: EdgeFilter[D,M] = default(EdgeFilter[D,M]), ## no filter
  vertexFilter: VertexFilter[D,M] = default(VertexFilter[D,M])
): seq[Vertex[D,M]] =
  ## Iterate graph basis, derive it iteratively if required, cache result
  ##
  ## Find all sccs, filter source sccs, take first vertex from each
  ##
  ## Basis is defined as a set of vertices, from which all other vertices are
  ## reachable. A basis in minimal, but not unique (consider a cycle). Minimal
  ## means that no basis vertex may be reachable from any other by definition.
  ##
  ## A set of SCC are unique to a graph, and the edges+vertices included therein
  ## The basis shall change for filtered edges/vertices then. Provide filters 
  let cacheKey = semanticHash(edgeFilter, vertexFilter)
  if cacheKey in g.basisCache:
    return g.basisCache[cacheKey]
  else:
    g.basisCache[cacheKey] = @[] # otherwise we keep building it
    # this is a condensation graph and by definition is condensed
    when D is SCC:
      # Condensed directed graphs basis is formed by the set of source vertices
      # and furthermore this basis is unique as no cycles exist
      for s in g.sources():
        g.basisCache[cacheKey].add s
      # some vertices shall have a self edge, capture as singletons. Nono of these
      # are going to be sources by definition [iterator isolated], [iterator sources]
      for s in g.isolated():
        g.basisCache[cacheKey].add s

      return g.basisCache[cacheKey]

    else: # Not a condensation graph
      # var gcondensed: graphalg.Graph[SCC[Graph.D,Graph.M],NoData] = (g.condensation[:Graph.D,Graph.M](filterCacheKey))
      var gcondensed = (g.condensation[:D,M](edgeFilter,vertexFilter))
      for v in gcondensed.vertices:
        if v.source:
          let avertex = v.data.chooseAnyVertex
          g.basisCache[cacheKey].add avertex
      # singletons are not sources and also need to be in the (complete) basis
      for s in gcondensed.isolated(): #
        let thevertex = s.data.chooseAnyVertex
        g.basisCache[cacheKey].add thevertex

      return g.basisCache[cacheKey]

iterator kahn[D,M](
  g: Graph[D,M],
  fas: HashSet[Edge[D,M]]=initHashSet[Edge[D,M]]()
): Vertex[D,M] =
  ## Emit vertices in an ordering determined by kahns algorithm. Vertices in loops will not be emitted as they dont reach indeg 0
  let ef: EdgeFilter[D,M] = EdgeFilter[D,M](semanticHash: fas.hash, predicate: some((e:Edge[D,M])=>e in fas))
  var vfluxin: BiMapSeq[int, Vertex[D,M]]
  for v in g.vertices:
    let d = v.flux(eFilter=ef).i
    vfluxin[d]=v

  while 0 in vfluxin:
    let v = vfluxin.pop(0)
    yield v
    for e in v.edges(dOutbound):
      if ef(e): continue
      let 
        neigh = e.inbound
        neighIndeg = vfluxin.find(e.inbound)
      # change indeg of neigh down one, it lost this edge
      vfluxin.rekey(e.inbound,neighIndeg-1)
      
include graphalg/fas

# O(V+E)
iterator toposort*[D, M](
    g: Graph[D, M],
    fas: HashSet[Edge[D, M]] = initHashSet[Edge[D, M]](),
): Vertex[D, M] =
  ## Topologically sort DAG where FAS pruned
  if not (ccAcyclic.test(g, fas)): # O(V+E)
    raise ValueError.newException "The given FAS does not make graph acyclic. Toposort not possible"

  for v in g.kahn(fas):
    yield v
