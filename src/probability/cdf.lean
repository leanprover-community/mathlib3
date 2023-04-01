/-
Copyright (c) 2022 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/

import measure_theory.constructions.borel_space
import measure_theory.measure.stieltjes

/-!
# Cdf

## Main definitions

* `foo_bar`

## Main statements

* `foo_bar_unique`

-/


open measure_theory topological_space set measure_theory.measure filter

open_locale topological_space ennreal

section cdf

/-- Cumulative distribution function of a real measure. -/
def cdf (μ : measure ℝ) : ℝ → ℝ := λ x, (μ (Iic x)).to_real

lemma monotone_cdf (μ : measure ℝ) [is_finite_measure μ] :
  monotone (cdf μ) :=
begin
  intros x y hxy,
  refine (ennreal.to_real_le_to_real (measure_ne_top μ _) (measure_ne_top μ _)).mpr _,
  exact measure_mono (λ a ha, le_trans ha hxy),
end

lemma cdf_eq_add_of_le {μ : measure ℝ} [is_finite_measure μ] {x y : ℝ} (h : x ≤ y) :
  cdf μ y = cdf μ x + (μ (Ioc x y)).to_real :=
begin
  rw [cdf],
  dsimp only,
  rw [← Iic_union_Ioc_eq_Iic h, measure_union _ (measurable_set_Ioc : measurable_set (Ioc x y))],
  { exact ennreal.to_real_add (measure_ne_top μ _) (measure_ne_top μ _), },
  { rw set.disjoint_iff,
    intro z,
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, and_imp],
    exact λ hzx hxz _, lt_irrefl _ (hzx.trans_lt hxz), },
end

lemma right_lim_eq_of_tendsto {α β : Type*} [linear_order α] [topological_space β]
  [hα : topological_space α] [h'α : order_topology α] [t2_space β]
  {f : α → β} {a : α} {y : β} (h : 𝓝[>] a ≠ ⊥) (h' : tendsto f (𝓝[>] a) (𝓝 y)) :
  function.right_lim f a = y :=
@left_lim_eq_of_tendsto αᵒᵈ β _ _ _ _ _ _ _ _ h h'

lemma tendsto_measure_Ioc_zero (μ : measure ℝ) [is_finite_measure μ] (x : ℝ) :
  tendsto (λ y, μ (Ioc x y)) (𝓝[Ioi x] x) (𝓝 0) :=
begin
  have h := @tendsto_measure_bInter_gt ℝ _ μ ℝ _ _ _ _ _ (λ y, Ioc x y) x
    (λ _ _, measurable_set_Ioc) _ ⟨x+1, lt_add_one _, measure_ne_top μ _⟩,
  swap,
  { intros i j hxi hij y hy,
    dsimp only at hy ⊢,
    rw mem_Ioc at hy ⊢,
    exact ⟨hy.1, hy.2.trans hij⟩, },
  dsimp at h,
  have : (⋂ r (H : x < r), Ioc x r) = ∅,
  { ext1 y,
    simp only [mem_Inter, mem_Ioc, mem_empty_iff_false, iff_false, not_forall, not_and, not_le,
      exists_prop],
    cases le_or_lt y x with h' h',
    { exact ⟨x+1, lt_add_one _, λ hxy, absurd hxy (not_lt.mpr h')⟩, },
    { exact ⟨(x + y)/2, by linarith, λ _, by linarith⟩, }, },
  rwa [this, measure_empty] at h,
end

lemma tendsto_cdf (μ : measure ℝ) [is_finite_measure μ] (x : ℝ) :
  tendsto (cdf μ) (𝓝[>] x) (𝓝 (cdf μ x)) :=
begin
  have h_add : ∀ y, x ≤ y → cdf μ y = cdf μ x + (μ (Ioc x y)).to_real,
  { intros y hxy,
    exact cdf_eq_add_of_le hxy, },
  suffices : tendsto (λ y, cdf μ x + (μ (Ioc x y)).to_real) (𝓝[>] x) (𝓝 (cdf μ x)),
  { refine (tendsto_congr' _).mpr this,
    rw [eventually_eq, eventually_nhds_within_iff],
    refine eventually_of_forall (λ z hz, cdf_eq_add_of_le _),
    rw mem_Ioi at hz,
    exact hz.le, },
  rw ← add_zero (cdf μ x),
  refine tendsto.add _ _,
  { rw add_zero, exact tendsto_const_nhds, },
  { rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff _ ennreal.zero_ne_top],
    { exact tendsto_measure_Ioc_zero μ x, },
    { exact λ i, measure_ne_top μ _, }, },
end

lemma right_lim_cdf (μ : measure ℝ) [is_finite_measure μ] (x : ℝ) :
  function.right_lim (cdf μ) x = cdf μ x :=
begin
  refine right_lim_eq_of_tendsto _ _,
  { rw ← ne_bot_iff,
    apply_instance, },
  { exact tendsto_cdf μ x, },
end

lemma continuous_within_at_cdf_Ioi (μ : measure ℝ) [is_finite_measure μ] (x : ℝ) :
  continuous_within_at (cdf μ) (Ioi x) x :=
(monotone.continuous_within_at_Ioi_iff_right_lim_eq (monotone_cdf μ)).mpr (right_lim_cdf μ x)

noncomputable
def cdf_stieltjes (μ : measure ℝ) [is_finite_measure μ] : stieltjes_function :=
monotone.stieltjes_function (monotone_cdf μ)

@[simp]
lemma cdf_stieltjes_apply (μ : measure ℝ) [is_finite_measure μ] (x : ℝ) :
  cdf_stieltjes μ x = cdf μ x :=
by rw [cdf_stieltjes, monotone.stieltjes_function_eq, right_lim_cdf]

lemma cdf_stieltjes_coe (μ : measure ℝ) [is_finite_measure μ] : ⇑(cdf_stieltjes μ) = cdf μ :=
by { ext1 x, exact cdf_stieltjes_apply μ x, }

lemma cdf_inj {μ ν : measure ℝ} [is_finite_measure μ] [is_finite_measure ν] :
  cdf μ = cdf ν ↔ μ = ν :=
begin
  refine ⟨λ h, ext_of_Iic μ ν (λ x, _), λ h, by rw h⟩,
  refine (ennreal.to_real_eq_to_real (measure_ne_top μ _) (measure_ne_top ν _)).mp _,
  have hx : cdf μ x = cdf ν x, by rw h,
  assumption,
end

lemma cdf_stieltjes_inj {μ ν : measure ℝ} [is_finite_measure μ] [is_finite_measure ν] :
  cdf_stieltjes μ = cdf_stieltjes ν ↔ μ = ν :=
begin
  refine ⟨λ h, cdf_inj.mp _, λ h, by simp_rw h⟩,
  rw [← cdf_stieltjes_coe, h, cdf_stieltjes_coe],
end

lemma measure_cdf_stieltjes (μ : measure ℝ) [is_finite_measure μ] :
  (cdf_stieltjes μ).measure = μ :=
begin
  refine ext_of_Ioc _ _ (λ x y hxy, _),
  rw stieltjes_function.measure_Ioc,
  simp_rw [cdf_stieltjes_apply],
  rw [cdf_eq_add_of_le hxy.le, add_sub_cancel', ennreal.of_real_to_real (measure_ne_top μ _)],
  apply_instance,
end

end cdf
