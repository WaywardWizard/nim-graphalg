# graphalg

Iterative (vs. recursive) graph algorithms and structures for Nim.

Provides a generic `Graph[D, M]` over `Vertex[D, M]` and `Edge[D, M]`, exposing
enough internal state to be used as a lower-level building block for a wide
range of algorithms. Performance is the goal, but not use-case optimization —
memory is traded for computation where it helps bound complexity.

## Features

- Strongly connected components (iterative Tarjan)
- Feedback arc sets: brute force (vertex ordering or edge set) and
  Eades–Lin–Smith with reorder/ILS-style improvements
- Condensation of a graph into its SCCs
- Basis (root vertices), sources, sinks
- DFS walk, Kahn and topological ordering
- Vertex lookup by label or data
- Filters to exclude vertices/edges from analysis, with cached results keyed
  on the filter combination
- A small `graph` DSL for concise graph definitions in tests

## Installation

```sh
nimble install graphalg
```

## Dependencies

- `nim >= 1.4.0`
- `combinatronics` — brute forcing vertex orderings / edge sets
- `fusion` — DSL pattern matching
- `datastructures`

## Usage

```nim
import graphalg

# The DSL (intended for tests/examples) builds a Graph[string, NoData]:
var g = graph:
  A - B - C("Desc")
  A - C

for scc in g.sccs:
  echo scc

for v in g.kahn:
  echo v.label
```

See `tests/` for worked examples covering basis, SCCs, FAS, sources, sinks,
Kahn and topological ordering.

## Documentation

Rendered docs are hosted on GitHub Pages:
<https://waywardwizard.github.io/nim-graphalg/>

HTML docs are generated under `docs/` via:

```sh
nimble mkdocs
```

## License

MIT — see [LICENSE](LICENSE).
