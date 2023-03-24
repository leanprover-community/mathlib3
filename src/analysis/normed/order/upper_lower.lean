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
variables {α : Type*} [linear_ordered_semifield α] {a : α}

@[simp] lemma half_lt_self_iff : a / 2 < a ↔ 0 < a :=
by rw [div_lt_iff (zero_lt_two' α), mul_two, lt_add_iff_pos_left]

end

section
variables {ι E : Type*} [fintype ι] [seminormed_group E] [nonempty ι]

open function

@[simp, to_additive pi_norm_const''] lemma pi_norm_const''' (a : E) : ‖const ι a‖ = ‖a‖ :=
pi_norm_const' a

@[simp, to_additive pi_nnnorm_const''] lemma pi_nnnorm_const''' (a : E) : ‖const ι a‖₊ = ‖a‖₊ :=
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

namespace real

@[simp] lemma to_nnreal_abs (x : ℝ) : |x|.to_nnreal = x.nnabs := nnreal.coe_injective $ by simp

end real

open function metric set
open_locale pointwise

variables {α ι : Type*}

section normed_ordered_group
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
upper_closure_min (interior_mono subset_upper_closure) (upper_closure s).upper.interior

@[to_additive lower_closure_interior_subset]
lemma lower_closure_interior_subset' (s : set α) :
  (upper_closure (interior s) : set α) ⊆ interior (upper_closure s) :=
upper_closure_min (interior_mono subset_upper_closure) (upper_closure s).upper.interior

end normed_ordered_group

/-! ### `ℝⁿ` -/

section finite
variables [finite ι] {s : set (ι → ℝ)} {x y : ι → ℝ}

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
variables [fintype ι] {s t : set (ι → ℝ)} {a₁ a₂ b₁ b₂ x y : ι → ℝ} {δ : ℝ}

-- TODO: Generalise those lemmas so that they also apply to `ℝ` and `euclidean_space ι ℝ`
lemma dist_inf_sup (x y : ι → ℝ) : dist (x ⊓ y) (x ⊔ y) = dist x y :=
begin
  refine congr_arg coe (finset.sup_congr rfl $ λ i _, _),
  simp only [real.nndist_eq', sup_eq_max, inf_eq_min, max_sub_min_eq_abs, pi.inf_apply,
    pi.sup_apply, real.nnabs_of_nonneg, abs_nonneg, real.to_nnreal_abs],
end

lemma dist_mono_left : monotone_on (λ x, dist x y) (Ici y) :=
begin
  refine λ y₁ hy₁ y₂ hy₂ hy, nnreal.coe_le_coe.2 (finset.sup_mono_fun $ λ i _, _),
  rw [real.nndist_eq, real.nnabs_of_nonneg (sub_nonneg_of_le (‹y ≤ _› i : y i ≤ y₁ i)),
    real.nndist_eq, real.nnabs_of_nonneg (sub_nonneg_of_le (‹y ≤ _› i : y i ≤ y₂ i))],
  exact real.to_nnreal_mono (sub_le_sub_right (hy _) _),
end

lemma dist_mono_right : monotone_on (dist x) (Ici x) :=
by simpa only [dist_comm] using dist_mono_left

lemma dist_anti_left : antitone_on (λ x, dist x y) (Iic y) :=
begin
  refine λ y₁ hy₁ y₂ hy₂ hy, nnreal.coe_le_coe.2 (finset.sup_mono_fun $ λ i _, _),
  rw [real.nndist_eq', real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ ≤ y› i : y₂ i ≤ y i)),
    real.nndist_eq', real.nnabs_of_nonneg (sub_nonneg_of_le (‹_ ≤ y› i : y₁ i ≤ y i))],
  exact real.to_nnreal_mono (sub_le_sub_left (hy _) _),
end

lemma dist_anti_right : antitone_on (dist x) (Iic x) :=
by simpa only [dist_comm] using dist_anti_left

lemma dist_le_dist_of_le (ha : a₂ ≤ a₁) (h₁ : a₁ ≤ b₁) (hb : b₁ ≤ b₂) : dist a₁ b₁ ≤ dist a₂ b₂ :=
(dist_mono_right h₁ (h₁.trans hb) hb).trans $
  dist_anti_left (ha.trans $ h₁.trans hb) (h₁.trans hb) ha

protected lemma metric.bounded.bdd_below : metric.bounded s → bdd_below s :=
begin
  rintro ⟨r, hr⟩,
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty,
  { exact bdd_below_empty },
  { exact ⟨x - const _ r, λ y hy i, sub_le_comm.1
      (abs_sub_le_iff.1 $ (dist_le_pi_dist _ _ _).trans $ hr _ hx _ hy).1⟩ }
end

protected lemma metric.bounded.bdd_above : bounded s → bdd_above s :=
begin
  rintro ⟨r, hr⟩,
  obtain rfl | ⟨x, hx⟩ := s.eq_empty_or_nonempty,
  { exact bdd_above_empty },
  { exact ⟨x + const _ r, λ y hy i, sub_le_iff_le_add'.1 $
      (abs_sub_le_iff.1 $ (dist_le_pi_dist _ _ _).trans $ hr _ hx _ hy).2⟩ }
end

protected lemma bdd_below.bounded : bdd_below s → bdd_above s → bounded s :=
begin
  rintro ⟨a, ha⟩ ⟨b, hb⟩,
  refine ⟨dist a b, λ x hx y hy, _⟩,
  rw ←dist_inf_sup,
  exact dist_le_dist_of_le (le_inf (ha hx) $ ha hy) inf_le_sup (sup_le (hb hx) $ hb hy),
end

protected lemma bdd_above.bounded : bdd_above s → bdd_below s → bounded s := flip bdd_below.bounded

lemma bounded_iff_bdd_below_bdd_above : bounded s ↔ bdd_below s ∧ bdd_above s :=
⟨λ h, ⟨h.bdd_below, h.bdd_above⟩, λ h, h.1.bounded h.2⟩

lemma bdd_below.bounded_inter (hs : bdd_below s) (ht : bdd_above t) : bounded (s ∩ t) :=
(hs.mono $ inter_subset_left _ _).bounded $ ht.mono $ inter_subset_right _ _

lemma bdd_above.bounded_inter (hs : bdd_above s) (ht : bdd_below t) : bounded (s ∩ t) :=
(hs.mono $ inter_subset_left _ _).bounded $ ht.mono $ inter_subset_right _ _

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

section finite
variables [finite ι] {s t : set (ι → ℝ)} {a₁ a₂ b₁ b₂ x y : ι → ℝ} {δ : ℝ}

lemma is_antichain.interior_eq_empty [nonempty ι] (hs : is_antichain (≤) s) : interior s = ∅ :=
begin
  casesI nonempty_fintype ι,
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
begin
  casesI nonempty_fintype ι,
  refine is_seq_closed.is_closed (λ f x hf hx, _),
  choose g hg hgf using hf,
  obtain ⟨a, ha⟩ := hx.bdd_above_range,
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.bounded_inter
    bdd_above_Iic) (λ n, ⟨hg n, (hgf _).trans $  ha $ mem_range_self _⟩),
  exact ⟨b, closure_minimal (inter_subset_left _ _) hs hb,
    le_of_tendsto_of_tendsto' hbf (hx.comp hφ.tendsto_at_top) $ λ _, hgf _⟩,
end

protected lemma is_closed.lower_closure (hs : is_closed s) (hs' : bdd_above s) :
  is_closed (lower_closure s : set (ι → ℝ)) :=
begin
  casesI nonempty_fintype ι,
  refine is_seq_closed.is_closed (λ f x hf hx, _),
  choose g hg hfg using hf,
  haveI : bounded_ge_nhds_class ℝ := by apply_instance,
  obtain ⟨a, ha⟩ := hx.bdd_below_range,
  obtain ⟨b, hb, φ, hφ, hbf⟩ := tendsto_subseq_of_bounded (hs'.bounded_inter
    bdd_below_Ici) (λ n, ⟨hg n, (ha $ mem_range_self _).trans $ hfg _⟩),
  exact ⟨b, closure_minimal (inter_subset_left _ _) hs hb,
    le_of_tendsto_of_tendsto' (hx.comp hφ.tendsto_at_top) hbf $ λ _, hfg _⟩,
end

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

end finite
