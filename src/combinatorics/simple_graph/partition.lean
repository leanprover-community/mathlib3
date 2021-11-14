/-
Copyright (c) 2021 Arthur Paulino. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Arthur Paulino, Kyle Miller
-/

import combinatorics.simple_graph.coloring
import data.setoid.partition
import order.antichain

universes u v

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

structure is_partition (P : set (set V)) : Prop :=
(valid : setoid.is_partition P)
(independent : ∀ (s ∈ P), is_antichain G.adj s)

variable {P : set (set V)}

def subset_of_vertex (hp : G.is_partition P) (v : V): set V :=
classical.some (hp.valid.2 v)

lemma subset_of_vertex_spec (hp : G.is_partition P) (v : V) :
  G.subset_of_vertex hp v ∈ P ∧ v ∈ G.subset_of_vertex hp v :=
begin
  obtain ⟨⟨h1, h2⟩, h3⟩ := (hp.valid.2 v).some_spec,
  exact ⟨h1, h2.1⟩,
end

lemma different_subsets_of_adjacent {v w : V} (hp : G.is_partition P) (h : G.adj v w) :
  G.subset_of_vertex hp v ≠ G.subset_of_vertex hp w :=
begin
  intro hn,
  have hv := G.subset_of_vertex_spec hp v,
  have hw := G.subset_of_vertex_spec hp w,
  have h1 := hp.independent _ hv.1,
  rw ←hn at hw,
  exact h1 v hv.2 w hw.2 (G.ne_of_adj h) h,
end

def partition_to_coloring (hp : G.is_partition P) : G.coloring (set V) :=
begin
  let color : V → set V := λ v, G.subset_of_vertex hp v,
  have h : ∀ (v w : V), G.adj v w → color v ≠ color w,
  { intros _ _ hvw,
    exact G.different_subsets_of_adjacent hp hvw, },
  exact coloring.mk color h,
end

end simple_graph
