/-
Copyright (c) 2021 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller
-/
import data.fintype.basic
import data.sym2
import data.set.finite
import combinatorics.simple_graph.basic
/-!
# Digraphs and multidigraphs

This module defines (multi)digraphs on a vertex type `V` with edges
labeled from a type `α`.  An edge is an ordered pair of vertices
along with a label -- this means that between any pair of vertices,
there can be at most one edge with a given label.

Labels give flexibility to the way (multi)digraphs are used.  At one
extreme, you are free to require that each edge label be used exactly
once, and in this case, the label type is exactly the edge type.  At
the other extreme, `α` might be a singleton, in which case the
definition reduces graphs without multiple edges.

## Main definitions

* `multidigraph` is a structure for a multigraph with labeled edges.

* `digraph V` is an abbreviation for `multidigraph V unit`.  This
  allows at most one edge from any given vertex to any given vertex
  (loop edges are allowed).


-/
open finset
universes u v

structure multidigraph (V : Type u) (α : Type v) :=
(labels : V → V → set α)

abbreviation digraph (V : Type u) := multidigraph V unit
