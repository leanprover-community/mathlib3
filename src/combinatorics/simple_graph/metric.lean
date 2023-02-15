/-
Copyright (c) 2022 Kyle Miller. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kyle Miller, Vincent Beffara
-/
import combinatorics.simple_graph.connectivity
import data.nat.lattice
import data.enat.lattice
import algebra.order.pointwise

/-!
# Graph metric

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
def edist (u v : V) : ℕ∞ := ⨅ w : G.walk u v, w.length

variables {G}

protected
lemma reachable.exists_walk_of_edist {u v : V} (h : G.reachable u v) :
  ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
begin
  haveI : nonempty (G.walk u v) := h,
  refine ⟨function.argmin (λ w : G.walk u v, (w.length : ℕ)) nat.lt_wf,
          le_antisymm (le_infi (λ w', _)) (infi_le _ _)⟩,
  simp only [nat.cast_le, function.argmin_le],
end

lemma reachable_iff_exists_walk_of_edist {u v : V} :
  G.reachable u v ↔ ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
⟨reachable.exists_walk_of_edist, λ p, ⟨p.some⟩⟩

lemma not_reachable_iff_edist_eq_top {u v : V} :
  ¬ G.reachable u v ↔ G.edist u v = ⊤ :=
begin
  rw [edist, reachable, not_nonempty_iff, infi_eq_top],
  exact ⟨λ h p, h.elim p, λ h, ⟨λ p,  with_top.nat_ne_top _ (h p)⟩⟩,
end

lemma reachable_iff_edist_ne_top {u v : V} :
  G.reachable u v ↔ G.edist u v ≠ ⊤ :=
by rw [←not_iff_not, not_reachable_iff_edist_eq_top, not_not]

lemma exists_walk_of_edist_iff_ne_top {u v : V} :
  (∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v) ↔ G.edist u v ≠ ⊤ :=
by rw [←reachable_iff_edist_ne_top, ←reachable_iff_exists_walk_of_edist]

lemma exists_walk_of_edist_eq_nat {u v : V} {n : ℕ} (h : G.edist u v = n) :
  (∃ (p : G.walk u v), p.length = n) :=
begin
  have : ∃ (p : G.walk u v), ↑(p.length) = G.edist u v, by
  { rw [exists_walk_of_edist_iff_ne_top, h],
    apply with_top.nat_ne_top _, },
  rw h at this,
  obtain ⟨w,hw⟩ := this,
  simp only [nat.cast_inj] at hw,
  exact ⟨w,hw⟩,
end

protected
lemma connected.exists_walk_of_edist (hconn : G.connected) (u v : V) :
  ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
(hconn u v).exists_walk_of_edist

lemma edist_le {u v : V} (p : G.walk u v) : G.edist u v ≤ p.length := infi_le _ p

lemma le_edist {u v : V} {n : ℕ} (h : ∀ p : G.walk u v, n ≤ p.length) : (n : ℕ∞) ≤ G.edist u v :=
le_infi (λ p, nat.cast_le.mpr $ h p)

lemma edist_self {v : V} : edist G v v = 0 := by
begin
  convert le_antisymm (infi_le _ (walk.nil' v)) _,
  simp only [walk.length_nil, enat.coe_zero, zero_le],
end

lemma edist_comm {u v : V} : edist G u v = edist G v u :=
begin
  dsimp [edist],
  refine le_antisymm (le_infi (λ w, _)) (le_infi (λ w, _));
  { rw ←walk.length_reverse,
    apply infi_le _ _, }
end

protected
lemma edist_triangle (hconn : G.connected) {u v w : V} :
  G.edist u w ≤ G.edist u v + G.edist v w :=
begin
  by_cases huv : nonempty (G.walk u v),
  by_cases hvw : nonempty (G.walk v w),
  { obtain ⟨p,hp⟩ := reachable.exists_walk_of_edist huv,
    obtain ⟨q,hq⟩ := reachable.exists_walk_of_edist hvw,
    rw [←hp, ←hq, ←enat.coe_add,←walk.length_append],
    apply edist_le, },
  { simp only [not_reachable_iff_edist_eq_top.mp hvw, with_top.add_top, le_top], },
  { simp only [not_reachable_iff_edist_eq_top.mp huv, with_top.top_add, le_top], },
end

@[simp]
lemma edist_eq_zero_iff_eq {u v : V} : G.edist u v = 0 ↔ u = v :=
⟨λ h, walk.eq_of_length_eq_zero (exists_walk_of_edist_eq_nat h).some_spec, λ h, h ▸ edist_self⟩

@[simp]
lemma edist_eq_one_iff_adj {u v : V} : G.edist u v = 1 ↔ G.adj u v :=
begin
  split,
  { rintro h,
    obtain ⟨w, hw⟩ := exists_walk_of_edist_eq_nat h,
    exact walk.adj_of_length_eq_one hw, },
  { refine λ a, le_antisymm (edist_le (walk.cons a walk.nil)) (le_edist (λ w, _)),
    simp only [nat.one_le_iff_ne_zero, walk.length_cons, walk.length_nil, ne.def],
    exact λ h, (a.ne $ walk.eq_of_length_eq_zero h), },
end

lemma exists_edist_eq_of_edist_eq_succ {u v : V} {n : ℕ} (h : G.edist u v = n+1) :
  ∃ w, G.edist u w = n ∧ G.edist w v = 1 :=
begin
  rw edist_comm at h,
  obtain ⟨p,hp⟩ := exists_walk_of_edist_eq_nat h,
  cases p with a v w u a q,
  { simpa using hp, },
  { simp, refine ⟨w, _, a.symm⟩,
    apply le_antisymm,
    { rw [←enat.coe_one, ←enat.coe_add, ←hp] at h,
      simp at h, },
    { apply le_edist, } },
end

end simple_graph
