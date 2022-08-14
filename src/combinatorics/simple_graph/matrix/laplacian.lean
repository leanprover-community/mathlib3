/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.simple_graph.matrix.incidence

/-!
# Laplacian of a simple graph

-/

namespace simple_graph
variables (R : Type*) [add_group_with_one R] {α : Type*} [decidable_eq α] [fintype α]
  (G : simple_graph α) [decidable_rel G.adj]

/-- The Laplacian of a graph is the matrix on its vertices that's `G.degree a` in `(a, a)`, `-1`
in `(a, b)` if `a` and `b` are connected by an edge and `0` elsewhere. -/
def laplacian : matrix α α R :=
λ a b, if a = b
         then G.degree a
       else if G.adj a b
         then -1
         else 0

@[simp] lemma laplacian_apply (a b : α) :
  G.laplacian R a b = if a = b then G.degree a else if G.adj a b then -1 else 0 := rfl

end simple_graph
