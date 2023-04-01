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

lemma right_lim_eq_of_tendsto {α β : Type*} [linear_order α] [topological_space β]
  [hα : topological_space α] [h'α : order_topology α] [t2_space β]
  {f : α → β} {a : α} {y : β} (h : 𝓝[>] a ≠ ⊥) (h' : tendsto f (𝓝[>] a) (𝓝 y)) :
  function.right_lim f a = y :=
@left_lim_eq_of_tendsto αᵒᵈ β _ _ _ _ _ _ _ _ h h'

section cdf

lemma monotone_measure_Iic {α : Type*} {m : measurable_space α} (μ : measure α)
  [preorder α] [is_finite_measure μ] :
  monotone (λ x, (μ (Iic x)).to_real) :=
begin
  intros x y hxy,
  refine (ennreal.to_real_le_to_real (measure_ne_top μ _) (measure_ne_top μ _)).mpr _,
  exact measure_mono (λ a ha, le_trans ha hxy),
end

lemma measure_Iic_eq_add_of_le {α : Type*} {m : measurable_space α} {μ : measure α}
  [linear_order α] [topological_space α] [opens_measurable_space α] [order_closed_topology α]
  [is_finite_measure μ] {x y : α} (h : x ≤ y) :
  (μ (Iic y)).to_real = (μ (Iic x)).to_real + (μ (Ioc x y)).to_real :=
begin
  rw [← Iic_union_Ioc_eq_Iic h, measure_union _ (measurable_set_Ioc : measurable_set (Ioc x y))],
  { exact ennreal.to_real_add (measure_ne_top μ _) (measure_ne_top μ _), },
  { rw set.disjoint_iff,
    intro z,
    simp only [mem_inter_iff, mem_Iic, mem_Ioc, mem_empty_iff_false, and_imp],
    exact λ hzx hxz _, lt_irrefl _ (hzx.trans_lt hxz), },
end

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

lemma tendsto_measure_Iic (μ : measure ℝ) [is_finite_measure μ] (x : ℝ) :
  tendsto (λ x, (μ (Iic x)).to_real) (𝓝[>] x) (𝓝 (μ (Iic x)).to_real) :=
begin
  have h_add : ∀ y, x ≤ y → (μ (Iic y)).to_real = (μ (Iic x)).to_real+ (μ (Ioc x y)).to_real,
  { intros y hxy,
    exact measure_Iic_eq_add_of_le hxy, },
  suffices : tendsto (λ y, (μ (Iic x)).to_real + (μ (Ioc x y)).to_real) (𝓝[>] x)
    (𝓝 ((μ (Iic x)).to_real)),
  { refine (tendsto_congr' _).mpr this,
    rw [eventually_eq, eventually_nhds_within_iff],
    refine eventually_of_forall (λ z hz, measure_Iic_eq_add_of_le _),
    rw mem_Ioi at hz,
    exact hz.le, },
  rw ← add_zero (μ (Iic x)).to_real,
  refine tendsto.add _ _,
  { rw add_zero, exact tendsto_const_nhds, },
  { rw [← ennreal.zero_to_real, ennreal.tendsto_to_real_iff _ ennreal.zero_ne_top],
    { exact tendsto_measure_Ioc_zero μ x, },
    { exact λ i, measure_ne_top μ _, }, },
end

lemma right_lim_measure_Iic (μ : measure ℝ) [is_finite_measure μ] (x : ℝ) :
  function.right_lim (λ y, (μ (Iic y)).to_real) x = (μ (Iic x)).to_real :=
begin
  refine right_lim_eq_of_tendsto _ _,
  { rw ← ne_bot_iff,
    apply_instance, },
  { exact tendsto_measure_Iic μ x, },
end

/-- Cumulative distribution function of a real measure. -/
noncomputable
def cdf (μ : measure ℝ) [is_finite_measure μ] : stieltjes_function :=
monotone.stieltjes_function (monotone_measure_Iic μ)

lemma cdf_apply (μ : measure ℝ) [is_finite_measure μ] (x : ℝ) :
  cdf μ x = (μ (Iic x)).to_real :=
by rw [cdf, monotone.stieltjes_function_eq, right_lim_measure_Iic]

lemma cdf_inj {μ ν : measure ℝ} [is_finite_measure μ] [is_finite_measure ν] :
  cdf μ = cdf ν ↔ μ = ν :=
begin
  refine ⟨λ h, ext_of_Iic μ ν (λ x, _), λ h, by simp_rw h⟩,
  refine (ennreal.to_real_eq_to_real (measure_ne_top μ _) (measure_ne_top ν _)).mp _,
  have hx : cdf μ x = cdf ν x, by rw h,
  simpa only [cdf_apply] using hx,
end

lemma measure_cdf (μ : measure ℝ) [is_finite_measure μ] :
  (cdf μ).measure = μ :=
begin
  refine ext_of_Ioc _ _ (λ x y hxy, _),
  rw stieltjes_function.measure_Ioc,
  simp_rw [cdf_apply],
  rw [measure_Iic_eq_add_of_le hxy.le, add_sub_cancel',
    ennreal.of_real_to_real (measure_ne_top μ _)],
  apply_instance,
  apply_instance,
end

end cdf
