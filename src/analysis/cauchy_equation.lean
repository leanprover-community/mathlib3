/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import measure_theory.measure.lebesgue.eq_haar

/-!
# Cauchy's Functional Equation

This file contains the classical results about the Cauchy's functional equation
`f (x + y) = f x + f y` for functions `f : ℝ → ℝ`. In this file, we prove that the solutions to this
equation are linear up to the case when `f` is a Lebesgue measurable functions, while also deducing
intermediate well-known variants.
-/

open add_monoid_hom measure_theory measure_theory.measure metric nnreal set
open_locale pointwise topology

section seminormed_group
open topological_space
variables {G H : Type*} [seminormed_add_group G] [topological_add_group G] [is_R_or_C H] {s : set G}

lemma add_monoid_hom.continuous_of_bounded_nhds_zero (f : G →+ H) (hs : s ∈ 𝓝 (0 : G))
  (hbounded : bounded (f '' s)) : continuous f :=
begin
  obtain ⟨δ, hδ, hUε⟩ := metric.mem_nhds_iff.mp hs,
  obtain ⟨C, hC⟩ := (bounded_iff_subset_ball 0).1 (hbounded.mono $ image_subset f hUε),
  refine continuous_of_continuous_at_zero _ (continuous_at_iff.2 $ λ ε (hε : _ < _), _),
  simp only [gt_iff_lt, dist_zero_right, _root_.map_zero, exists_prop],
  obtain ⟨n, hn⟩ := exists_nat_gt (C / ε),
  obtain hC₀ | hC₀ := le_or_lt C 0,
  { refine ⟨δ, hδ, λ x hxδ, _⟩,
    rwa [eq_of_dist_eq_zero (dist_nonneg.antisymm' $ (mem_closed_ball.1 $ hC $ mem_image_of_mem f $
      mem_ball_zero_iff.2 hxδ).trans hC₀), norm_zero] },
  have hnpos : 0 < (n : ℝ) := (div_pos hC₀ hε).trans hn,
  refine ⟨δ / n, div_pos hδ hnpos, λ x hxδ, _⟩,
  have h2 : f (n • x) = n • f x := map_nsmul f _ _,
  have hn' : (n : H) ≠ 0 := nat.cast_ne_zero.2 (by { rintro rfl, simpa using hnpos }),
  simp_rw [nsmul_eq_mul, mul_comm (n : H), ←div_eq_iff hn'] at h2,
  replace hxδ : ‖n • x‖ < δ,
  { refine (norm_nsmul_le _ _).trans_lt _,
    simpa only [norm_mul, real.norm_coe_nat, lt_div_iff hnpos, mul_comm] using hxδ },
  rw [←h2, norm_div, is_R_or_C.norm_nat_cast, div_lt_iff' hnpos, ←mem_ball_zero_iff],
  rw div_lt_iff hε at hn,
  exact hC.trans (closed_ball_subset_ball hn) (mem_image_of_mem _ $ mem_ball_zero_iff.2 hxδ),
end

end seminormed_group

variables {ι : Type*} [fintype ι] {s : set ℝ} {a : ℝ}

local notation `ℝⁿ` := ι → ℝ

lemma add_monoid_hom.measurable_of_continuous (f : ℝ →+ ℝ) (h : measurable f) : continuous f :=
let ⟨s, hs, hbdd⟩ := h.exists_nhds_zero_bounded f in f.continuous_of_bounded_nhds_zero hs hbdd

-- do we want this one and where would it go?
lemma is_linear_map_iff_apply_eq_apply_one_mul {M : Type*} [comm_semiring M] (f : M →+ M) :
  is_linear_map M f ↔ ∀ x : M, f x = f 1 * x :=
begin
  refine ⟨λ h x, _, λ h, ⟨map_add f, λ c x, _⟩⟩,
  { convert h.2 x 1 using 1,
    { simp only [algebra.id.smul_eq_mul, mul_one] },
    { simp only [mul_comm, algebra.id.smul_eq_mul] }},
  { rw [smul_eq_mul, smul_eq_mul, h (c * x), h x, ←mul_assoc, mul_comm _ c, mul_assoc] }
end

lemma is_linear_rat (f : ℝ →+ ℝ) (q : ℚ) : f q = f 1 * q :=
begin
  have := map_rat_cast_smul f ℚ ℚ q (1 : ℝ),
  simpa [mul_comm] using this,
end

lemma additive_is_bounded_of_bounded_on_interval (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a)
  (h : bounded (f '' s)) : ∃ V, V ∈ 𝓝 (0 : ℝ) ∧ bounded (f '' V) :=
begin
  rcases metric.mem_nhds_iff.mp hs with ⟨δ, hδ, hδa⟩,
  refine ⟨ball 0 δ, ball_mem_nhds 0 hδ, _⟩,
  rw bounded_iff_forall_norm_le,
  simp only [mem_image, mem_ball_zero_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
  obtain ⟨M, hM⟩ := bounded_iff_forall_norm_le.1 h,
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hM,
  refine ⟨M + M, λ x hxδ, (norm_le_add_norm_add _ $ f a).trans $ add_le_add _ $ hM _ $ hδa _⟩,
  { rw ←map_add f,
    refine hM _ (hδa _),
    simp only [mem_ball],
    convert hxδ,
    rw [←dist_zero_right, ←dist_add_right x 0 a, zero_add] },
  { simpa [mem_ball, dist_self] }
end

-- to generalize
lemma add_monoid_hom.continuous_at_iff_continuous_at_zero (f : ℝ →+ ℝ) :
  continuous_at f a ↔ continuous_at f 0 :=
begin
  refine ⟨λ ha, continuous_at_iff.2 $ λ ε hε, Exists₂.imp (λ δ hδ, _) (continuous_at_iff.1 ha ε hε),
    λ h, (continuous_of_continuous_at_zero f h).continuous_at⟩,
  refine λ hδf y hyδ, _,
  replace hyδ : dist (y + a) a < δ,
  { convert hyδ using 1,
    simp only [dist_eq_norm, sub_zero, add_sub_cancel] },
  convert hδf hyδ using 1,
  simp only [dist_eq_norm, map_sub, _root_.map_add, _root_.map_zero, sub_zero, add_sub_cancel],
end

lemma continuous.is_linear_real (f : ℝ →+ ℝ) (h : continuous f) : is_linear_map ℝ f :=
(f.to_real_linear_map h).to_linear_map.is_linear

lemma is_linear_map_real_of_bounded_nhds (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a) (hf : bounded (f '' s)) :
  is_linear_map ℝ f :=
let ⟨V, hV0, hVb⟩ := additive_is_bounded_of_bounded_on_interval f hs hf in
  (f.continuous_of_bounded_nhds_zero hV0 hVb).is_linear_real f

lemma monotone_on.is_linear_map_real (f : ℝ →+ ℝ) (hs : s ∈ 𝓝 a) (hf : monotone_on f s) :
  is_linear_map ℝ f :=
begin
  obtain ⟨t, ht, h⟩ := metric.mem_nhds_iff.mp hs,
  refine is_linear_map_real_of_bounded_nhds f (closed_ball_mem_nhds a $ half_pos ht) _,
  replace h := (closed_ball_subset_ball $ half_lt_self ht).trans h,
  rw real.closed_ball_eq_Icc at ⊢ h,
  have ha :  a - t / 2 ≤ a + t / 2 := by linarith,
  refine bounded_of_bdd_above_of_bdd_below (hf.map_bdd_above h _) (hf.map_bdd_below h _),
  { refine ⟨a + t / 2, _, h $ right_mem_Icc.2 ha⟩,
    rw upper_bounds_Icc ha,
    exact left_mem_Ici },
  { refine ⟨a - t / 2, _, h $ left_mem_Icc.2 ha⟩,
    rw lower_bounds_Icc ha,
    exact right_mem_Iic }
end
