/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara
-/
import combinatorics.simple_graph.connectivity
import data.nat.lattice

/-!
# Graph metric

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This module defines the `simple_graph.dist` function, which takes
pairs of vertices to the length of the shortest walk between them.

## Main definitions

- `simple_graph.dist` is the graph metric.

## Todo

- Provide an additional computable version of `simple_graph.dist`
  for when `G` is connected.

- Evaluate `nat` vs `enat` for the codomain of `dist`, or potentially
  having an additional `edist` when the objects under consideration are
  disconnected graphs.

- When directed graphs exist, a directed notion of distance,
  likely `enat`-valued.

## Tags

graph metric, distance

-/

namespace simple_graph
variables {V : Type*} (G : simple_graph V)

/-! ## Metric -/

/-- The distance between two vertices is the length of the shortest walk between them.
If no such walk exists, this uses the junk value of `0`. -/
noncomputable
def dist (u v : V) : ℕ := Inf (set.range (walk.length : G.walk u v → ℕ))

variables {G}

protected
lemma reachable.exists_walk_of_dist {u v : V} (hr : G.reachable u v) :
  ∃ (p : G.walk u v), p.length = G.dist u v :=
nat.Inf_mem (set.range_nonempty_iff_nonempty.mpr hr)

protected
lemma connected.exists_walk_of_dist (hconn : G.connected) (u v : V) :
  ∃ (p : G.walk u v), p.length = G.dist u v :=
(hconn u v).exists_walk_of_dist

lemma dist_le {u v : V} (p : G.walk u v) : G.dist u v ≤ p.length := nat.Inf_le ⟨p, rfl⟩

@[simp]
lemma dist_eq_zero_iff_eq_or_not_reachable {u v : V} : G.dist u v = 0 ↔ u = v ∨ ¬ G.reachable u v :=
by simp [dist, nat.Inf_eq_zero, reachable]

lemma dist_self {v : V} : dist G v v = 0 := by simp

protected
lemma reachable.dist_eq_zero_iff {u v : V} (hr : G.reachable u v) :
  G.dist u v = 0 ↔ u = v := by simp [hr]

protected
lemma reachable.pos_dist_of_ne {u v : V} (h : G.reachable u v) (hne : u ≠ v) : 0 < G.dist u v :=
nat.pos_of_ne_zero (by simp [h, hne])

protected
lemma connected.dist_eq_zero_iff (hconn : G.connected) {u v : V} :
  G.dist u v = 0 ↔ u = v := by simp [hconn u v]

protected
lemma connected.pos_dist_of_ne {u v : V} (hconn : G.connected) (hne : u ≠ v) : 0 < G.dist u v :=
nat.pos_of_ne_zero (by simp [hconn.dist_eq_zero_iff, hne])

lemma dist_eq_zero_of_not_reachable {u v : V} (h : ¬ G.reachable u v) : G.dist u v = 0 :=
by simp [h]

lemma nonempty_of_pos_dist {u v : V} (h : 0 < G.dist u v) :
  (set.univ : set (G.walk u v)).nonempty :=
by simpa [set.range_nonempty_iff_nonempty, set.nonempty_iff_univ_nonempty]
     using nat.nonempty_of_pos_Inf h

protected
lemma connected.dist_triangle (hconn : G.connected) {u v w : V} :
  G.dist u w ≤ G.dist u v + G.dist v w :=
begin
  obtain ⟨p, hp⟩ := hconn.exists_walk_of_dist u v,
  obtain ⟨q, hq⟩ := hconn.exists_walk_of_dist v w,
  rw [← hp, ← hq, ← walk.length_append],
  apply dist_le,
end

private
lemma dist_comm_aux {u v : V} (h : G.reachable u v) : G.dist u v ≤ G.dist v u :=
begin
  obtain ⟨p, hp⟩ := h.symm.exists_walk_of_dist,
  rw [← hp, ← walk.length_reverse],
  apply dist_le,
end

lemma dist_comm {u v : V} : G.dist u v = G.dist v u :=
begin
  by_cases h : G.reachable u v,
  { apply le_antisymm (dist_comm_aux h) (dist_comm_aux h.symm), },
  { have h' : ¬ G.reachable v u := λ h', absurd h'.symm h,
    simp [h, h', dist_eq_zero_of_not_reachable], },
end

end simple_graph
