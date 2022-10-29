/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.order.upper_lower
import analysis.normed_space.ordered
import topology.metric_space.hausdorff_distance

/-!
# Topological facts about upper/lower/order-connected sets

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.
-/

section
variables {E : Type*} [seminormed_group E]

@[simp, to_additive] lemma dist_mul_self_right (a b : E) : dist b (a * b) = ∥a∥ :=
by rw [←dist_one_left, ←dist_mul_right 1 a b, one_mul]

@[simp, to_additive] lemma dist_mul_self_left (a b : E) : dist (a * b) b = ∥a∥ :=
by rw [dist_comm, dist_mul_self_right]

end

section
variables {α : Type*} [preorder α] {s : set α} {p : α → Prop}

@[simp] lemma monotone_mem : monotone (∈ s) ↔ is_upper_set s := iff.rfl
@[simp] lemma antitone_mem : antitone (∈ s) ↔ is_lower_set s := forall_swap

@[simp] lemma is_upper_set_set_of : is_upper_set {a | p a} ↔ monotone p := iff.rfl
@[simp] lemma is_lower_set_set_of : is_lower_set {a | p a} ↔ antitone p := forall_swap

end

section
variables {α : Type*} [mul_one_class α] [has_lt α] [contravariant_class α α (*) (<)] {a b : α}

@[to_additive] lemma one_lt_of_lt_mul_right : a < a * b → 1 < b :=
by simpa only [mul_one] using (lt_of_mul_lt_mul_left' : a * 1 < a * b → 1 < b)

end

section
variables {α : Type*} [mul_one_class α] [preorder α] [contravariant_class α α (*) (<)]
  [has_exists_mul_of_le α] {a b : α}

@[to_additive] lemma exists_one_lt_mul_of_lt' (h : a < b) : ∃ c, 1 < c ∧ a * c = b :=
by { obtain ⟨c, rfl⟩ := exists_mul_of_le h.le, exact ⟨c, one_lt_of_lt_mul_right h, rfl⟩ }

end

section finite
variables {α ι : Type*} [linear_ordered_semifield α] [has_exists_add_of_le α] [finite ι]
  {x y : ι → α}

lemma pi.exists_forall_pos_add_lt (h : ∀ i, x i < y i) : ∃ ε, 0 < ε ∧ ∀ i, x i + ε < y i :=
begin
  casesI nonempty_fintype ι,
  casesI is_empty_or_nonempty ι,
  { exact ⟨1, zero_lt_one, is_empty_elim⟩ },
  choose ε hε hxε using λ i, exists_pos_add_of_lt' (h i),
  obtain rfl : x + ε = y := funext hxε,
  have hε : 0 < finset.univ.inf' finset.univ_nonempty ε := (finset.lt_inf'_iff _).2 (λ i _, hε _),
  exact ⟨_, half_pos hε, λ i, add_lt_add_left ((half_lt_self hε).trans_le $ finset.inf'_le _ $
    finset.mem_univ _) _⟩,
end

end finite

open function metric set
open_locale pointwise

variables {α ι : Type*}

section topological_space
variables [topological_space α] [ordered_comm_group α] [has_continuous_const_smul α α]
  {s : set α}

@[to_additive is_upper_set.closure]
protected lemma is_upper_set.closure' (h : is_upper_set s) : is_upper_set (closure s) :=
λ x y hxy hx, closure_mono (h.smul_subset $ one_le_div'.2 hxy) $
  by { rw closure_smul, exact ⟨x, hx, div_mul_cancel' _ _⟩ }

@[to_additive is_lower_set.closure]
protected lemma is_lower_set.closure' (h : is_lower_set s) : is_lower_set (closure s) :=
h.of_dual.closure'

/-
Note: ` s.ord_connected` does not imply `(closure s).ord_connected`, as we can see by taking
`s := Ioo 0 1 × Ioo 1 2 ∪ Ioo 2 3 × Ioo 0 1` because then
`closure s = Icc 0 1 × Icc 1 2 ∪ Icc 2 3 × Icc 0 1` is not order-connected as
`(1, 1) ∈ closure s`, `(2, 1) ∈ closure s` but `Icc (1, 1) (2, 1) ⊈ closure s`.

`s` looks like
```
xxooooo
xxooooo
oooooxx
oooooxx
```
-/

@[to_additive is_upper_set.interior]
protected lemma is_upper_set.interior' (h : is_upper_set s) : is_upper_set (interior s) :=
by { rw [←is_lower_set_compl, ←closure_compl], exact h.compl.closure' }

@[to_additive is_lower_set.interior]
protected lemma is_lower_set.interior' (h : is_lower_set s) : is_lower_set (interior s) :=
h.of_dual.interior'

@[to_additive set.ord_connected.interior]
protected lemma set.ord_connected.interior' (h : s.ord_connected) : (interior s).ord_connected :=
begin
  rw [←h.upper_closure_inter_lower_closure, interior_inter],
  exact (upper_closure s).upper.interior'.ord_connected.inter
    (lower_closure s).lower.interior'.ord_connected,
end

end topological_space

section metric_space
variables [normed_ordered_group α] {s : set α}

@[to_additive is_upper_set.thickening]
protected lemma is_upper_set.thickening' (hs : is_upper_set s) (ε : ℝ) :
  is_upper_set (thickening ε s) :=
begin
  simp_rw [is_upper_set, mem_thickening_iff],
  rintro x y h ⟨z, hz, hxz⟩,
  refine ⟨y / x * z, hs (by simpa) hz, _⟩,
  rwa [div_mul_comm y, dist_mul_self_right _ y, ←dist_eq_norm_div'],
end

@[to_additive is_lower_set.thickening]
protected lemma is_lower_set.thickening' (hs : is_lower_set s) (ε : ℝ) :
  is_lower_set (thickening ε s) :=
begin
  simp_rw [is_lower_set, mem_thickening_iff],
  rintro x y h ⟨z, hz, hxz⟩,
  refine ⟨y / x * z, hs (by simpa) hz, _⟩,
  rwa [div_mul_comm y, dist_mul_self_right _ y, ←dist_eq_norm_div'],
end

@[to_additive is_upper_set.cthickening]
protected lemma is_upper_set.cthickening' (hs : is_upper_set s) (ε : ℝ) :
  is_upper_set (cthickening ε s) :=
begin
  obtain hε | hε := le_total ε 0,
  { rw cthickening_of_nonpos hε,
    exact hs.closure' },
  { rw cthickening_eq_Inter_thickening hε,
    exact is_upper_set_Inter₂ (λ δ hδ, hs.thickening' _) }
end

@[to_additive is_lower_set.cthickening]
protected lemma is_lower_set.cthickening' (hs : is_lower_set s) (ε : ℝ) :
  is_lower_set (cthickening ε s) :=
begin
  obtain hε | hε := le_total ε 0,
  { rw cthickening_of_nonpos hε,
    exact hs.closure' },
  { rw cthickening_eq_Inter_thickening hε,
    exact is_lower_set_Inter₂ (λ δ hδ, hs.thickening' _) }
end

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
  { refine λ i, (lt_sub_iff_add_lt.2 $ hxy _).trans_le (_root_.sub_le.1 $ (le_abs_self _).trans _),
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
