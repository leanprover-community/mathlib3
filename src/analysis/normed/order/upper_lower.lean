/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.field.pi
import analysis.normed.group.pointwise
import analysis.normed.order.basic
import topology.algebra.order.upper_lower

/-!
# Upper/lower/order-connected sets in normed groups

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.
-/

open function metric set

variables {α ι : Type*}

section metric_space
variables [normed_ordered_group α] {s : set α}

@[to_additive is_upper_set.thickening]
protected lemma is_upper_set.thickening' (hs : is_upper_set s) (ε : ℝ) :
  is_upper_set (thickening ε s) :=
by { rw ←ball_mul_one, exact hs.mul_left }

@[to_additive is_lower_set.thickening]
protected lemma is_lower_set.thickening' (hs : is_lower_set s) (ε : ℝ) :
  is_lower_set (thickening ε s) :=
by { rw ←ball_mul_one, exact hs.mul_left }

@[to_additive is_upper_set.cthickening]
protected lemma is_upper_set.cthickening' (hs : is_upper_set s) (ε : ℝ) :
  is_upper_set (cthickening ε s) :=
by { rw cthickening_eq_Inter_thickening'', exact is_upper_set_Inter₂ (λ δ hδ, hs.thickening' _) }

@[to_additive is_lower_set.cthickening]
protected lemma is_lower_set.cthickening' (hs : is_lower_set s) (ε : ℝ) :
  is_lower_set (cthickening ε s) :=
by { rw cthickening_eq_Inter_thickening'', exact is_lower_set_Inter₂ (λ δ hδ, hs.thickening' _) }

end metric_space

/-! ### `ℝⁿ` -/

section finite
variables [finite ι] {s : set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

lemma is_upper_set.mem_interior_of_forall_lt (hs : is_upper_set s) (hx : x ∈ closure s)
  (h : ∀ i, x i < y i) :
  y ∈ interior s :=
begin
  casesI nonempty_fintype ι,
  obtain ⟨ε, hε, hxy⟩ := pi.exists_forall_pos_add_lt h,
  obtain ⟨z, hz, hxz⟩ := metric.mem_closure_iff.1 hx _ hε,
  rw dist_pi_lt_iff hε at hxz,
  have hyz : ∀ i, z i < y i,
  { refine λ i, (hxy _).trans_le' (sub_le_iff_le_add'.1 $ (le_abs_self _).trans _),
    rw [←real.norm_eq_abs, ←dist_eq_norm'],
    exact (hxz _).le },
  obtain ⟨δ, hδ, hyz⟩ := pi.exists_forall_pos_add_lt hyz,
  refine mem_interior.2 ⟨ball y δ, _, is_open_ball, mem_ball_self hδ⟩,
  rintro w hw,
  refine hs (λ i, _) hz,
  simp_rw [ball_pi _ hδ, real.ball_eq_Ioo] at hw,
  exact ((lt_sub_iff_add_lt.2 $ hyz _).trans (hw _ $ mem_univ _).1).le,
end

lemma is_lower_set.mem_interior_of_forall_lt (hs : is_lower_set s) (hx : x ∈ closure s)
  (h : ∀ i, y i < x i) :
  y ∈ interior s :=
begin
  casesI nonempty_fintype ι,
  obtain ⟨ε, hε, hxy⟩ := pi.exists_forall_pos_add_lt h,
  obtain ⟨z, hz, hxz⟩ := metric.mem_closure_iff.1 hx _ hε,
  rw dist_pi_lt_iff hε at hxz,
  have hyz : ∀ i, y i < z i,
  { refine λ i, (lt_sub_iff_add_lt.2 $ hxy _).trans_le (sub_le_comm.1 $ (le_abs_self _).trans _),
    rw [←real.norm_eq_abs, ←dist_eq_norm],
    exact (hxz _).le },
  obtain ⟨δ, hδ, hyz⟩ := pi.exists_forall_pos_add_lt hyz,
  refine mem_interior.2 ⟨ball y δ, _, is_open_ball, mem_ball_self hδ⟩,
  rintro w hw,
  refine hs (λ i, _) hz,
  simp_rw [ball_pi _ hδ, real.ball_eq_Ioo] at hw,
  exact ((hw _ $ mem_univ _).2.trans $ hyz _).le,
end

end finite

section fintype
variables [fintype ι] {s : set (ι → ℝ)} {x y : ι → ℝ} {δ : ℝ}

lemma is_upper_set.exists_subset_ball (hs : is_upper_set s) (hx : x ∈ closure s) (hδ : 0 < δ) :
  ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ interior s :=
begin
  refine ⟨x + const _ (3/4*δ), closed_ball_subset_closed_ball' _, _⟩,
  { rw dist_self_add_left,
    refine (add_le_add_left (pi_norm_const_le $ 3 / 4 * δ) _).trans_eq _,
    simp [real.norm_of_nonneg, hδ.le, zero_le_three],
    ring_nf },
  obtain ⟨y, hy, hxy⟩ := metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four),
  refine λ z hz, hs.mem_interior_of_forall_lt (subset_closure hy) (λ i, _),
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  linarith,
end

lemma is_lower_set.exists_subset_ball (hs : is_lower_set s) (hx : x ∈ closure s) (hδ : 0 < δ) :
  ∃ y, closed_ball y (δ/4) ⊆ closed_ball x δ ∧ closed_ball y (δ/4) ⊆ interior s :=
begin
  refine ⟨x - const _ (3/4*δ), closed_ball_subset_closed_ball' _, _⟩,
  { rw dist_self_sub_left,
    refine (add_le_add_left (pi_norm_const_le $ 3 / 4 * δ) _).trans_eq _,
    simp [real.norm_of_nonneg, hδ.le, zero_le_three],
    ring_nf },
  obtain ⟨y, hy, hxy⟩ := metric.mem_closure_iff.1 hx _ (div_pos hδ zero_lt_four),
  refine λ z hz, hs.mem_interior_of_forall_lt (subset_closure hy) (λ i, _),
  rw [mem_closed_ball, dist_eq_norm'] at hz,
  rw dist_eq_norm at hxy,
  replace hxy := (norm_le_pi_norm _ i).trans hxy.le,
  replace hz := (norm_le_pi_norm _ i).trans hz,
  dsimp at hxy hz,
  rw abs_sub_le_iff at hxy hz,
  linarith,
end

end fintype
