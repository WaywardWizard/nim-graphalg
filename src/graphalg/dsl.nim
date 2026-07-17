import std/[macros, sets, strutils, strformat, sugar, tables]
# Any libraries DSL uses must be exported or otherwise they will not be usable at callsite
export tables
import fusion/matching
{.experimental: "caseStmtMacros".}
import ../graphalg

type DslGraph = ref object # intermediary representation
  nodes: Table[string, string] # label to desc
  edges: Table[string, seq[string]] # out-node labels to seq of in-node labels
  selfedges: HashSet[string] # collection of nodes with self edge

proc `$`(x: DslGraph): string =
  $x.nodes & "\n" & $x.edges

proc enumerateNodes(s: NimNode): seq[tuple[label, desc: string]] =
  # List of nodes in given DSL
  case s
  of Ident(strVal: @nlabel): # node label
    result.add (nlabel, "")
  of Call[Ident(strVal: @nlabel), StrLit(strVal: @ndesc)]: # named node
    result.add (nlabel, ndesc)
  of Curly[all @nodedsl is Ident() | Call()]:
    for nodeset in @nodedsl:
      for node in nodeset.enumerateNodes:
        result.add node
  else:
    raise ValueError.newException "Unrecognized syntax " & s.repr

proc processNodes(s: NimNode, g: DslGraph) =
  for n in s.enumerateNodes:
    g.nodes[n.label] = n.desc

proc processEdgesAndNodes(s: NimNode, g: DslGraph) =
  ## edge (A-B) or chain of edges (A-B-C). Add nodes to graph and then edges
  ##
  ## A - A will be a self edge
  case s
  of Infix[==ident"-", @e1, @e2]:
    var
      nodeGroupsString: seq[string] = s.repr.split '-'
      nodeGroupsNn: seq[NimNode] = collect:
        for ngs in nodeGroupsString:
          ngs.parseExpr
      nodeGroups: seq[seq[tuple[label, desc: string]]] = collect:
        for ngnn in nodeGroupsNn:
          ngnn.enumerateNodes

    # add nodes
    for nodeGroup in nodeGroupsNn:
      nodeGroup.processNodes(g)

    # add edges
    for ix in 1 .. (len(nodeGroups) - 1):
      var
        outnodes = nodeGroups[ix - 1]
        innodes = nodeGroups[ix]
      for o in outnodes:
        var inlabels: seq[string]
        for i in innodes:
          if o == i: # self edge
            g.selfedges.incl o.label # invariant o.label == i.label
          else:
            g.edges.mgetOrPut(o.label).add i.label
  else:
    raise ValueError.newException "Not a valid edge"

proc processStatement(s: NimNode, g: DslGraph) =
  case s
  of Infix(): # A - B form
    processEdgesAndNodes(s, g)
  else:
    processNodes(s, g)

proc toGraphAst(g: DslGraph): NimNode {.compiletime.} =
  ## Convert DslGraph to ast that will create a corresponding graph at runtime
  ##
  ## AST: (proc(): auto = ... )()
  var
    body = newStmtList()
    vmap = genSym(nskVar, "vmap")

  body.add quote do:
    # bool edge data
    var `vmap`: Table[string, Vertex[string, NoData]] # label to vertex

  # Create vertices and edges (populates vmap)
  var vertexPuts, edgePuts = newStmtList()
  for label, desc in g.nodes:
    var
      ilabel = ident label
      idesc = ident desc
      llabel = newlit label
      ldesc = newlit desc
    vertexPuts.add quote do:
      `vmap`[`llabel`] = initVertex[string](`llabel`, `ldesc`) # label, data

    if label in g.edges: # node has edge(s), put them in vertices
      for tolabel in g.edges[label]: #
        var ltolabel = newLit(tolabel)
        edgePuts.add quote do:
          `vmap`[`llabel`].connectTo(`vmap`[`ltolabel`])

    if label in g.selfedges:
      edgePuts.add quote do:
        `vmap`[`llabel`].connectToSelf()

  body.add vertexPuts
  body.add edgePuts
  # return the actual graph from lambda proc (a statement the evals to Graph)
  body.add quote do:
    let iter =
      iterator (): Vertex[string, NoData] {.closure.} =
        for v in `vmap`.values:
          yield v

    return initGraph[string, NoData](iter)

  var rt = parseStmt("Graph[string, NoData]")
  var theResult =
    newCall(newPar(newProc(body = body, params = [`rt`], procType = nnkLambda)))
  return theResult

macro graph*(body: untyped): untyped =
  ## Graph definition DSL for testing purposes
  ##
  ## A - A                # Self edge
  ## A - B - C            # Edge A to B, B to C
  ## B - {D, E, F} - G    # Edge B to nodes D, E, F. D E F to G
  ##
  ## A(label)   # Label node A
  ##
  ## This macro will;
  ## 1) Parse DSL into an intermediary DslGraph representation
  ## 2) Generate AST declaring a Graph that matches the DSL
  ## 3) Emit that AST to replace the macro call
  body.expectKind nnkStmtList
  var g = DslGraph()
  for s in body:
    s.processStatement(g)
  result = g.toGraphAst()
