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

lemma different_subsets_of_adjacent {v w : V} (hp : G.is_partition P) (h : G.adj v w) :
  G.subset_of_vertex hp v ≠ G.subset_of_vertex hp w :=
begin
  by_contra hn,
  have hi := hp.independent,
  simp [is_antichain, set.pairwise] at hi,

  have hvalid := hp.valid,
  simp [setoid.is_partition] at hvalid,
  cases hvalid with hmpty hvalid,

  specialize hvalid v,
  cases hvalid with sv hvalid,
  cases hvalid with hv hvalid,
  cases hv with h_sv_in_P h_v_in_sv,
  have h_w_in_sv : w ∈ sv,
  {
    sorry, },
  have h_w_neq_v : w ≠ v, by exact ne_of_adj G (adj_symm G h),
  have hwv : G.adj w v, by exact adj_symm G h,
  have := hi sv h_sv_in_P w h_w_in_sv v h_v_in_sv h_w_neq_v,
  contradiction,
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
