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
lemma reachable.exists_walk {u v : V} (h : G.reachable u v) :
  ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
begin
  haveI : nonempty (G.walk u v) := h,
  refine ⟨function.argmin (λ w : G.walk u v, (w.length : ℕ)) nat.lt_wf,
          le_antisymm (le_infi (λ w', _)) (infi_le _ _)⟩,
  simp only [nat.cast_le, function.argmin_le],
end

lemma reachable_iff_exists_walk {u v : V} :
  G.reachable u v ↔ ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
⟨reachable.exists_walk, λ p, ⟨p.some⟩⟩

lemma not_reachable_iff_edist_eq_top {u v : V} :
  ¬ G.reachable u v ↔ G.edist u v = ⊤ :=
begin
  rw [edist, reachable, not_nonempty_iff, infi_eq_top],
  exact ⟨λ h p, h.elim p, λ h, ⟨λ p,  with_top.nat_ne_top _ (h p)⟩⟩,
end

lemma reachable_iff_edist_ne_top {u v : V} :
  G.reachable u v ↔ G.edist u v ≠ ⊤ :=
by rw [←not_iff_not, not_reachable_iff_edist_eq_top, not_not]

lemma exists_walk_iff_edist_ne_top {u v : V} :
  (∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v) ↔ G.edist u v ≠ ⊤ :=
by rw [←reachable_iff_edist_ne_top, ←reachable_iff_exists_walk]

lemma exists_walk_of_edist_eq_nat {u v : V} {n : ℕ} (h : G.edist u v = n) :
  (∃ (p : G.walk u v), p.length = n) :=
begin
  have : ∃ (p : G.walk u v), ↑(p.length) = G.edist u v, by
  { rw [exists_walk_iff_edist_ne_top, h],
    apply with_top.nat_ne_top _, },
  rw h at this,
  obtain ⟨w,hw⟩ := this,
  simp only [nat.cast_inj] at hw,
  exact ⟨w,hw⟩,
end

protected
lemma connected.exists_walk (hconn : G.connected) (u v : V) :
  ∃ (p : G.walk u v), (p.length : ℕ∞) = G.edist u v :=
(hconn u v).exists_walk

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

lemma edist_triangle {u v w : V} :
  G.edist u w ≤ G.edist u v + G.edist v w :=
begin
  by_cases huv : nonempty (G.walk u v),
  by_cases hvw : nonempty (G.walk v w),
  { obtain ⟨p,hp⟩ := reachable.exists_walk huv,
    obtain ⟨q,hq⟩ := reachable.exists_walk hvw,
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

lemma _root_.enat.add_one_lt_add_one {a b : ℕ∞} (ab : a < b) : a + 1 < b + 1 := sorry

lemma exists_edist_eq_of_edist_eq_succ {u v : V} {n : ℕ} (h : G.edist u v = n+1) :
  ∃ w, G.edist w v = n ∧ G.edist u w = 1 :=
begin
  obtain ⟨p, hp⟩ := exists_walk_of_edist_eq_nat h,
  cases p with _ u w v a q,
  { simpa only using hp, },
  { simp only [edist_eq_one_iff_adj],
    refine ⟨w, _, a⟩,
    simp only [walk.length_cons, add_left_inj] at hp,
    refine le_antisymm (hp ▸ edist_le _) _,
    { by_contra' h',
      rw ←edist_eq_one_iff_adj at a,
      refine ((enat.add_one_lt_add_one h').trans_le (_ : ↑n + 1 ≤ G.edist w v + 1)).ne rfl,
      rw [←h, ←a, add_comm],
      apply edist_triangle, }, },
end

@[reducible]
def closed_ball (G : simple_graph V) (v : V) (n : ℕ) := {u | G.edist u v ≤ n}

lemma closed_ball_zero_eq (v : V) : G.closed_ball v 0 = {v} :=
by simp only [closed_ball, edist_eq_zero_iff_eq, enat.coe_zero, nonpos_iff_eq_zero,
              set.set_of_eq_eq_singleton]

lemma _root_.enat.le_add (n m : ℕ∞) : n ≤ n + m := sorry
lemma _root_.enat.add_le_add {n n' m m' : ℕ∞} (hn : n ≤ n') (hm : m ≤ m') : n + m ≤ n' + m' := sorry
lemma _root_.enat.le_add_one_iff_ {n m : ℕ∞} : n ≤ m  := sorry



lemma closed_ball_succ_eq  (v : V) (n : ℕ) :
  G.closed_ball v (n+1) = G.closed_ball v n ∪ (⋃ u ∈ G.closed_ball v n, G.neighbor_set u) :=
begin
  ext x,
  simp only [enat.coe_add, enat.coe_one, set.mem_set_of_eq, set.mem_union, set.mem_Union,
             mem_neighbor_set, exists_prop],
  split,
  { rintro hx, rw le_iff_eq_or_lt at hx,
    rcases hx with (he|hlt),
    sorry,
    sorry, /- enat is a pain -/  },
  { rintro (hx|⟨u,hu,a⟩),
    { exact hx.trans (enat.le_add _ _), },
    { apply (@edist_triangle _ G x u v).trans _,
      rw add_comm _ (1 : ℕ∞),
      apply enat.add_le_add (eq.le _) hu,
      simpa using a.symm, }, }
end

instance fintype_closed_ball [lf : locally_finite G] [decidable_eq V] (v : V) (n : ℕ) :
  fintype (G.closed_ball v n) :=
begin
  induction n,
  { rw closed_ball_zero_eq,
    apply set.fintype_singleton, },
  { rw closed_ball_succ_eq,
    haveI := n_ih,
    apply set.fintype_union, },
end

lemma closed_ball_ne_univ_of_infinite [lf : locally_finite G] [decidable_eq V] [infinite V]
  (v : V) (n : ℕ) : G.closed_ball v n ≠ set.univ :=
begin
  sorry,
end

end simple_graph
