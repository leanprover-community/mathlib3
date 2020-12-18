/-
Copyright (c) 2020 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/
import topology.algebra.ordered

/-!
This file contains some lemmas about real polynomials and their derivatives
-/

open set

--  This section contains results that do not belong to this file, but are
-- used to obtain the literal statements of the original PR #5361.  Except
-- for `finset_closed_of_t1`, they are not used, though to prove the results
-- that, in my opinion, contain the "essence" of the lemmas.

section topology

/-- A `finset` in a `t1_space` is closed. -/
lemma finset_closed_of_t1 {α : Type*} [topological_space α] [t1_space α] (s : finset α) :
  is_closed (s : set α) :=
begin
  have sbU : (s : set α) = ⋃ a ∈ s, {a}:= by { ext,
    simp only [exists_prop, mem_Union, mem_singleton_iff, exists_eq_right', finset.mem_coe] },
  rw sbU,
  exact is_closed_bUnion (finite_mem_finset s) (λ i hi, t1_space.t1 i),
end

/-- There is an open interval around any point in the complement of a closed set,
missing the closed set. -/
lemma Ioo_not_mem_finset {R : Type*} [topological_space R] [linear_order R]
  [order_topology R] [no_bot_order R] [no_top_order R]
  (x : R) (C : finset R) :
  ∃ l m : R, x ∈ Ioo l m ∧ ∀ y (yI : y ∈ Ioo l m) (yx : y ≠ x), y ∉ C :=
begin
  obtain oU := is_open_compl_iff.mpr (finset_closed_of_t1 (finset.erase C x)),
  rcases (mem_nhds_iff_exists_Ioo_subset.mp (mem_nhds_sets oU
    (λ xh, finset.ne_of_mem_erase xh rfl))) with ⟨l, m, aI, IU⟩,
  exact ⟨l, m, aI, λ y Iy yx yC, mem_of_mem_of_subset Iy IU (finset.mem_coe.mpr
    (finset.mem_erase.mpr ⟨yx, yC⟩))⟩,
end

end topology

section intervals

variables {R : Type*} [linear_ordered_add_comm_group R]

/-- A lemma relating a compact interval and its shifts. -/
lemma sub_mem_Icc_iff_d
  (x y l m : R) : (x - y ∈ Icc l m ↔ x ∈ Icc (y + l) (y + m)) :=
by simp only [le_sub_iff_add_le', sub_le_iff_le_add', iff_self, mem_Icc]
--⟨λ a, ⟨le_sub_iff_add_le'.mp a.1, sub_le_iff_le_add'.mp a.2⟩,
--    λ b, ⟨le_sub_iff_add_le'.mpr b.1, sub_le_iff_le_add'.mpr b.2⟩⟩

/-- A lemma relating a symmetric compact interval and its shifts. -/
lemma sub_mem_Icc_iff_symmetric (x y z : R) : (x - y ∈ Icc (- z) z ↔ x ∈ Icc (y - z) (y + z)) :=
by rw [sub_mem_Icc_iff_d, tactic.ring.add_neg_eq_sub y z]

/-- A lemma describing a compact interval via absolute values. -/
lemma abs_le_iff_mem_Icc (x y z : R) : (abs (x - y) ≤ z ↔ x ∈ Icc (y - z) (y + z)) :=
⟨λ h, ⟨sub_le_of_abs_sub_le_left h, sub_le_iff_le_add'.mp (abs_le.mp h).2⟩,
  λ h, abs_le.mpr ((sub_mem_Icc_iff_symmetric _ _ _).mpr h)⟩

/-- An element of an open interval is closer to the left end-point than
the length of the interval. -/
lemma abs_lt_abs_left {a b c : R} (hc : b ∈ Ioo a c) :
  abs (a - b) < abs (a - c) :=
begin
  rw [abs_lt, neg_lt, lt_abs, lt_abs, neg_sub, neg_sub],
  exact ⟨or.inr (sub_lt_sub_right hc.2 a), or.inr (sub_lt_sub (lt_trans hc.1 hc.2) hc.1)⟩,
end

/-- An element of an open interval is closer to the right end-point than
the length of the interval. -/
lemma abs_lt_abs_right {a b c : R} (hc : b ∈ Ioo a c) :
  abs (c - b) < abs (a - c) :=
begin
  rw [abs_sub, sub_eq_neg_add, sub_eq_neg_add, ← neg_neg b, ← neg_neg a],
  exact abs_lt_abs_left ⟨neg_lt_neg_iff.mpr hc.2, neg_lt_neg_iff.mpr hc.1⟩,
end

end intervals
