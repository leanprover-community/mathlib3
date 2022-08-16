/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import combinatorics.graph.multi.basic

/-!
# Graph connectivity

## Main definitions

* `multigraph.walk`: Walk
* `multigraph.path`: Path
* `multigraph.reachable`: Whether there exists a walk between a given pair of vertices.
* `multigraph.preconnected`, `multigraph.connected`: Predicates on multigraphs for whether every
  vertex can be reached from every other and, in the latter case, if the vertex type is nonempty.
* `multigraph.connected_component`: Type of connected components of a given graph.

## References

* [Chou1994]

## Tags

walks, trails, paths, circuits, cycles
-/

open function

universes u v

namespace multigraph

/-- A multigraph is preconnected if any vertex is reachable from any other. -/
def preconnected (G : multigraph) : Prop := sorry

/-- A multigraph is connected if it's preconnected and nonempty. -/
structure connected (G : multigraph) : Prop :=
(preconnected : G.preconnected)
[nonempty : nonempty G]

end multigraph
