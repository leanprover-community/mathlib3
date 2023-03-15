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

The topological closure and interior of an upper/lower/order-connected set is an
upper/lower/order-connected set (with the notable exception of the closure of an order-connected
set).

We also prove lemmas specific to `ℝⁿ`. Those are helpful to prove that order-connected sets in `ℝⁿ`
are measurable.
-/

section
variables {α : Type*} [preorder α] {s : set α} {a b : α}

lemma is_antichain.not_lt (hs : is_antichain (≤) s) (ha : a ∈ s) (hb : b ∈ s) : ¬ a < b :=
λ h, hs ha hb h.ne h.le

end

section
open set
variables {α : Type*} [partial_order α] {s : set α}

lemma is_antichain_iff_forall_not_lt : is_antichain (≤) s ↔ ∀ ⦃a⦄, a ∈ s → ∀ ⦃b⦄, b ∈ s → ¬ a < b :=
⟨λ hs a ha b, hs.not_lt ha, λ hs a ha b hb h h', hs ha hb $ h'.lt_of_ne h⟩

lemma is_antichain.ord_connected (hs : is_antichain (≤) s) : s.ord_connected :=
⟨λ x hx y hy z hz, by { obtain rfl := hs.eq hx hy (hz.1.trans hz.2),
  rw [Icc_self, mem_singleton_iff] at hz, rwa hz }⟩

end

section left_cancel_monoid
variables {M : Type*} [left_cancel_monoid M] {a b : M}

@[to_additive] lemma mul_right_ne_self : a * b ≠ a ↔ b ≠ 1 := mul_right_eq_self.not
@[to_additive] lemma self_ne_mul_right : a ≠ a * b ↔ b ≠ 1 := self_eq_mul_right.not

end left_cancel_monoid

section right_cancel_monoid
variables {M : Type*} [right_cancel_monoid M] {a b : M}

@[to_additive] lemma mul_left_ne_self : a * b ≠ b ↔ a ≠ 1 := mul_left_eq_self.not
@[to_additive] lemma self_ne_mul_left : b ≠ a * b ↔ a ≠ 1 := self_eq_mul_left.not

end right_cancel_monoid

section
variables {α : Type*} [linear_ordered_semifield α] {a : α}

@[simp] lemma half_lt_self_iff : a / 2 < a ↔ 0 < a :=
by rw [div_lt_iff (zero_lt_two' α), mul_two, lt_add_iff_pos_left]

end

section
variables {ι E : Type*} [fintype ι] [seminormed_group E] [nonempty ι]

open function

@[simp, to_additive pi_norm_const''] lemma pi_norm_const''' (a : E) : ∥const ι a∥ = ∥a∥ :=
pi_norm_const' a

@[simp, to_additive pi_nnnorm_const''] lemma pi_nnnorm_const''' (a : E) : ∥const ι a∥₊ = ∥a∥₊ :=
pi_nnnorm_const' a

end

section
variables {ι : Type*} [fintype ι] [nonempty ι] {ε : ℝ}

open function metric

lemma pi.exists_gt_mem_ball (x : ι → ℝ) (hε : 0 < ε) : ∃ y, x < y ∧ dist y x < ε :=
begin
  refine ⟨x + const ι (ε / 2), lt_add_of_pos_right _ $ by positivity, _⟩,
  simpa [@pi_norm_const'' ι ℝ _ _ _ (ε / 2), abs_of_nonneg hε.le],
end

lemma pi.exists_lt_mem_ball (x : ι → ℝ) (hε : 0 < ε) : ∃ y, y < x ∧ dist y x < ε :=
begin
  refine ⟨x - const ι (ε / 2), sub_lt_self _ $ by positivity, _⟩,
  simpa [@pi_norm_const'' ι ℝ _ _ _ (ε / 2), abs_of_nonneg hε.le],
end

end

open function metric set
open_locale pointwise

variables {α ι : Type*}

section
variables [topological_space α] [preorder α] [order_closed_topology α] {s : set α}

protected lemma bdd_below.closure : bdd_below s → bdd_below (closure s) :=
by { simp_rw bdd_below_iff_subset_Ici, rintro ⟨a, ha⟩, exact ⟨a, closure_minimal ha is_closed_Ici⟩ }

protected lemma bdd_above.closure : bdd_above s → bdd_above (closure s) :=
by { simp_rw bdd_above_iff_subset_Iic, rintro ⟨a, ha⟩, exact ⟨a, closure_minimal ha is_closed_Iic⟩ }

end

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

@[to_additive upper_closure_interior_subset]
lemma upper_closure_interior_subset' (s : set α) :
  (upper_closure (interior s) : set α) ⊆ interior (upper_closure s) :=
upper_closure_min (interior_mono subset_upper_closure) (upper_closure s).upper.interior'

@[to_additive lower_closure_interior_subset]
lemma lower_closure_interior_subset' (s : set α) :
  (upper_closure (interior s) : set α) ⊆ interior (upper_closure s) :=
upper_closure_min (interior_mono subset_upper_closure) (upper_closure s).upper.interior'

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

lemma is_antichain.interior_eq_empty [nonempty ι] (hs : is_antichain (≤) s) : interior s = ∅ :=
begin
  refine eq_empty_of_forall_not_mem (λ x hx, _),
  have hx' := interior_subset hx,
  rw [mem_interior_iff_mem_nhds, metric.mem_nhds_iff] at hx,
  obtain ⟨ε, hε, hx⟩ := hx,
  obtain ⟨y, hy, hyx⟩ := pi.exists_gt_mem_ball x hε,
  exact hs.not_lt hx' (hx hyx) hy,
end

/-
Note: The closure and frontier of an antichain might not be antichains. Take for example the union
of the open segments from `(0, 2)` to `(1, 1)` and from `(2, 1)` to `(3, 0)`. `(1, 1)` and `(2, 1)`
are comparable and both in the closure/frontier.
-/

protected lemma is_closed.upper_closure (hs : is_closed s) (hs' : bdd_below s) :
  is_closed (upper_closure s : set (ι → ℝ)) :=
sorry

protected lemma is_closed.lower_closure (hs : is_closed s) (hs' : bdd_above s) :
  is_closed (lower_closure s : set (ι → ℝ)) :=
sorry

protected lemma is_clopen.upper_closure (hs : is_clopen s) (hs' : bdd_below s) :
  is_clopen (upper_closure s : set (ι → ℝ)) :=
⟨hs.1.upper_closure, hs.2.upper_closure hs'⟩

protected lemma is_clopen.lower_closure (hs : is_clopen s) (hs' : bdd_above s) :
  is_clopen (lower_closure s : set (ι → ℝ)) :=
⟨hs.1.lower_closure, hs.2.lower_closure hs'⟩

lemma closure_upper_closure_comm (hs : bdd_below s) :
  closure (upper_closure s : set (ι → ℝ)) = upper_closure (closure s) :=
(closure_minimal (upper_closure_anti subset_closure) $
  is_closed_closure.upper_closure hs.closure).antisymm $
    upper_closure_min (closure_mono subset_upper_closure) (upper_closure s).upper.closure

lemma closure_lower_closure_comm (hs : bdd_above s) :
  closure (lower_closure s : set (ι → ℝ)) = lower_closure (closure s) :=
(closure_minimal (lower_closure_mono subset_closure) $
  is_closed_closure.lower_closure hs.closure).antisymm $
    lower_closure_min (closure_mono subset_lower_closure) (lower_closure s).lower.closure

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
