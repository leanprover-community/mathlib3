/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import analysis.normed_space.pointwise
import measure_theory.measure.haar_lebesgue

/-!
# Cauchy's Functional Equation

This file contains the classical results about the Cauchy's functional equation
`f (x + y) = f x + f y` for functions `f : ℝ → ℝ`. In this file, we prove that the solutions to this
equation are linear up to the case when `f` is a Lebesgue measurable functions, while also deducing
intermediate well-known variants.
-/

open add_monoid_hom measure_theory measure_theory.measure metric nnreal set
open_locale pointwise topological_space

section PR13381
variables {E : Type*} [semi_normed_group E] [normed_space ℝ E] {x y z : E} {δ ε : ℝ}

@[simp] lemma ball_sub_ball (hε : 0 < ε) (hδ : 0 < δ) (a b : E) :
  ball a ε - ball b δ = ball (a - b) (ε + δ) :=
sorry

end PR13381

section
variables {F α β : Type*}

@[simp, to_additive]
lemma image_div [group α] [group β] [monoid_hom_class F α β] (f : F) (s t : set α) :
  f '' (s / t) = f '' s / f '' t :=
image_image2_distrib $ map_div f

end

variables {ι : Type*} [fintype ι]

local notation `ℝⁿ` := ι → ℝ

/-- **Cauchy's functional equation**. An additive monoid homomorphism automatically preserves `ℚ`.
-/
theorem add_monoid_hom.is_linear_map_rat (f : ℝ →+ ℝ) : is_linear_map ℚ f :=
by exact ⟨map_add f, λ c x, map_rat_cast_smul f ℝ ℝ c x⟩

-- should this one get generalised?
lemma exists_real_preimage_ball_pos_volume (f : ℝ → ℝ) : ∃ r z : ℝ, 0 < volume (f⁻¹' (ball z r)) :=
begin
  have : measure_space.volume (f⁻¹' set.univ) = ⊤,
  { simp only [set.preimage_univ, real.volume_univ] },
  by_contra hf,
  push_neg at hf,
  simp only [nonpos_iff_eq_zero] at hf,
  have hrat : (⋃ (q : ℚ), ball (0 : ℝ) q) = set.univ,
  { ext,
    split,
    { simp only [set.mem_univ, implies_true_iff]},
    { intro hx,
      simp only [set.mem_Union, mem_ball_zero_iff],
      exact exists_rat_gt _}},
  simp only [←hrat, preimage_Union] at this,
  have htop : ⊤ ≤ ∑' (i : ℚ), measure_space.volume ((λ (q : ℚ), f ⁻¹' ball 0 ↑q) i),
  { rw ← this,
    apply measure_Union_le (λ q : ℚ, f⁻¹' (ball (0 : ℝ) q)) },
  simp only [hf, tsum_zero, nonpos_iff_eq_zero, ennreal.top_ne_zero] at htop,
  exact htop
end

lemma exists_zero_nhds_bounded (f : ℝ →+ ℝ) (h : measurable f) :
  ∃ U, U ∈ nhds (0 : ℝ) ∧ metric.bounded (f '' U) :=
begin
  obtain ⟨r, z, hfr⟩ := exists_real_preimage_ball_pos_volume f,
  refine ⟨_, sub_mem_nhds_zero_of_add_haar_pos volume (f⁻¹' ball z r) (h $ measurable_set_ball) hfr,
    _⟩,
  suffices : f '' (⇑f ⁻¹' ball z r - ⇑f ⁻¹' ball z r) ⊆ ball (z - z) (r + r),
  { exact bounded_ball.mono this },
  obtain hr | hr := le_or_lt r 0,
  { simp only [ball_eq_empty.2 hr, preimage_empty, sub_empty, image_empty, empty_subset] },
  rw [image_sub, ←ball_sub_ball hr hr],
  exact sub_subset_sub (image_preimage_subset _ _) (image_preimage_subset _ _),
  apply_instance,
end

lemma additive_continuous_at_zero_of_bounded_nhds_zero (f : ℝ →+ ℝ) {U : set ℝ}
  (hU : U ∈ nhds (0 : ℝ)) (hbounded : metric.bounded (f '' U)) : continuous_at f 0 :=
begin
  rcases (metric.mem_nhds_iff.mp hU) with ⟨δ, hδ, hUε⟩,
  rcases ((metric.bounded_iff_subset_ball (0 : ℝ)).mp
    (metric.bounded.mono (image_subset f hUε) hbounded)) with ⟨C, hC⟩,
  refine continuous_at_iff.2 (λ ε hε, _),
  simp only [gt_iff_lt, dist_zero_right, _root_.map_zero, exists_prop],
  cases (exists_nat_gt (C / ε)) with n hn,
  obtain hC0 | rfl | hC0 := lt_trichotomy C 0,
  { simp only [closed_ball_eq_empty.mpr hC0, image_subset_iff, preimage_empty] at hC,
    rw [subset_empty_iff, ball_eq_empty] at hC,
    linarith },
  { simp only [closed_ball_zero] at hC,
    refine ⟨δ, hδ, λ x hxδ, _⟩,
    rwa [mem_singleton_iff.1 (hC $ mem_image_of_mem f $ mem_ball_zero_iff.2 hxδ), norm_zero] },
  { have hnpos : 0 < (n : ℝ) := (div_pos hC0 hε).trans hn,
    refine ⟨δ/n, div_pos hδ hnpos, λ x hxδ, _⟩,
    have h2 : f (n • x) = n • f x := map_nsmul f n x,
    simp_rw [nsmul_eq_mul, mul_comm (n : ℝ), ← div_eq_iff hnpos.ne'] at h2,
    rw ← h2,
    replace hxδ : ∥ x * n ∥ < δ,
    { simpa only [norm_mul, real.norm_coe_nat, ← lt_div_iff hnpos] using hxδ },
    norm_num,
    rw [div_lt_iff hnpos, ← mem_ball_zero_iff],
    apply (subset.trans hC _) (mem_image_of_mem _ $ mem_ball_zero_iff.2 hxδ),
    apply closed_ball_subset_ball,
    rw (div_lt_iff hε) at hn,
    simpa [mul_comm] using hn }
end

lemma additive_continuous_at_zero (f : ℝ →+ ℝ) (h : measurable f) : continuous_at f 0 :=
let ⟨U, hU, hbounded⟩ := exists_zero_nhds_bounded f h in
  additive_continuous_at_zero_of_bounded_nhds_zero f hU hbounded

lemma continuous_of_measurable (f : ℝ →+ ℝ) (h : measurable f) : continuous f :=
(f.uniform_continuous_of_continuous_at_zero $ additive_continuous_at_zero f h).continuous

-- do we want this one and where would it go?
lemma is_linear_map_iff_apply_eq_apply_one_mul {M : Type*} [comm_semiring M] (f : M →+ M) :
  is_linear_map M f ↔ ∀ x : M, f x = f 1 * x :=
begin
  refine ⟨λ h x, _, λ h, ⟨map_add f, λ c x, _⟩⟩,
  { convert h.2 x 1 using 1,
    { simp only [algebra.id.smul_eq_mul, mul_one] },
    { simp only [mul_comm, algebra.id.smul_eq_mul] }},
  { rw [smul_eq_mul, smul_eq_mul, h (c * x), h x, ← mul_assoc, mul_comm _ c, mul_assoc] }
end

lemma is_linear_rat (f : ℝ →+ ℝ) : ∀ (q : ℚ), f q = f 1 * q :=
begin
  intro q,
  have h1 : f ((q : ℝ) • 1) = (q : ℝ) • f 1 := map_rat_cast_smul f _ _ _ _,
  convert h1 using 1,
  { simp only [algebra.id.smul_eq_mul, mul_one], },
  { simp only [mul_comm, algebra.id.smul_eq_mul] }
end

lemma additive_is_bounded_of_bounded_on_interval (f : ℝ →+ ℝ) {a : ℝ} {U : set ℝ} (hU : U ∈ 𝓝 a)
  (h : metric.bounded (f '' U)) : ∃ (V : set ℝ), V ∈ 𝓝 (0 : ℝ) ∧ metric.bounded (f '' V) :=
begin
  rcases (metric.mem_nhds_iff.mp hU) with ⟨δ, hδ, hδa⟩,
  refine ⟨ball 0 δ, ball_mem_nhds 0 hδ, _⟩,
  rw bounded_iff_exists_norm_le,
  simp only [mem_image, mem_ball_zero_iff, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂],
  rcases (bounded_iff_exists_norm_le.mp h) with ⟨M, hM⟩,
  simp only [mem_image, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hM,
  refine ⟨M + M, λ x hxδ, (norm_le_add_norm_add _ $ f a).trans $ add_le_add _ $ hM _ $ hδa _⟩,
  { rw ←map_add f,
    refine hM _ (hδa _),
    simp only [mem_ball],
    convert hxδ,
    rw [← dist_zero_right, ← dist_add_right x 0 a, zero_add] },
  { simpa [mem_ball, dist_self] }
end

lemma continuous.is_linear_real  (f : ℝ →+ ℝ) (h : continuous f) : is_linear_map ℝ f :=
begin
  rw is_linear_map_iff_apply_eq_apply_one_mul,
  have h1 := is_linear_rat f,
  refine λ x, eq_of_norm_sub_le_zero (le_of_forall_pos_lt_add _),
  by_contra' hf,
  rcases hf with ⟨ε, hε, hf⟩,
  rw continuous_iff at h,
  specialize h x (ε/2) (by linarith [hε]),
  rcases h with ⟨δ, hδ, h⟩,
  by_cases hf1 : f 1 = 0,
  { simp only [hf1, zero_mul] at h1,
    simp only [hf1, zero_mul, sub_zero] at hf,
    cases (exists_rat_near x hδ) with q hq,
    specialize h q _,
    { simp only [dist_eq_norm', real.norm_eq_abs, hq] },
    simp only [h1, dist_zero_left] at h,
    linarith },
  { have hq : ∃ (q : ℚ), | x - ↑q | < min δ (ε / 2 / ∥f 1∥),
    apply exists_rat_near,
    { refine lt_min hδ (mul_pos (by linarith) _),
      simp only [_root_.inv_pos, norm_pos_iff, ne.def, hf1, not_false_iff] },
    cases hq with q hq,
    specialize h ↑q _,
    { simp only [dist_eq_norm', real.norm_eq_abs],
      apply lt_of_lt_of_le hq (min_le_left δ _) },
    rw [dist_eq_norm', h1] at h,
    suffices h2 : ∥ f x - f 1 * x ∥ < ε, by linarith [hf, h2],
    have h3 : ∥ f x - f 1 * q ∥ + ∥ f 1 * q - f 1 * x ∥ < ε,
    { have h4 : ∥ f 1 * q - f 1 * x ∥ < ε / 2,
      { replace hf1 : 0 < ∥ f 1 ∥ := by simpa [norm_pos_iff, ne.def],
        simp only [←mul_sub, norm_mul, mul_comm (∥f 1∥) _, ← lt_div_iff hf1],
        rw [← dist_eq_norm, dist_eq_norm', real.norm_eq_abs],
        apply lt_of_lt_of_le hq (min_le_right δ _) },
      linarith },
    refine ((norm_add_le _ _).trans_eq' _).trans_lt h3,
    congr,
    abel }
end

-- to generalize
lemma add_monoid_hom.continuous_at_iff_continuos_at_zero (f : ℝ →+ ℝ) {x : ℝ} :
  continuous_at f x ↔ continuous_at f 0 :=
begin
  refine ⟨λ hx, continuous_at_iff.2 $ λ ε hε, Exists₂.imp (λ δ hδ, _) (continuous_at_iff.1 hx ε hε),
    λ h, (f.uniform_continuous_of_continuous_at_zero h).continuous.continuous_at⟩,
  refine λ hδf y hyδ, _,
  replace hyδ : dist (y + x) x < δ,
  { convert hyδ using 1,
    simp only [dist_eq_norm, sub_zero, add_sub_cancel] },
  convert hδf hyδ using 1,
  simp only [dist_eq_norm, map_sub, _root_.map_add, _root_.map_zero, sub_zero, add_sub_cancel],
end

lemma is_linear_real_of_continuous_at (f : ℝ →+ ℝ) {y : ℝ} (h : continuous_at f y) :
  is_linear_map ℝ f :=
(f.uniform_continuous_of_continuous_at_zero $
  (f.continuous_at_iff_continuos_at_zero).mp h).continuous.is_linear_real f

lemma is_linear_real_of_bounded_nhds (f : ℝ →+ ℝ) {a : ℝ} {U : set ℝ} (hU : U ∈ 𝓝 a)
  (hf : metric.bounded (f '' U)) : is_linear_map ℝ f :=
begin
  rcases (additive_is_bounded_of_bounded_on_interval f hU hf) with ⟨V, hV0, hVb⟩,
  exact is_linear_real_of_continuous_at f
    (additive_continuous_at_zero_of_bounded_nhds_zero f hV0 hVb)
end

lemma monotone_on.is_linear_map_real (f : ℝ →+ ℝ) {a : ℝ} {U : set ℝ} (hU : U ∈ 𝓝 a)
  (hf : monotone_on f U) : is_linear_map ℝ f :=
begin
  rcases (metric.mem_nhds_iff.mp hU) with ⟨t, ht, h⟩,
  replace h := subset.trans (metric.closed_ball_subset_ball (show t / 2 < t, by linarith)) h,
  apply is_linear_real_of_bounded_nhds f
    (metric.closed_ball_mem_nhds a $ show (0 : ℝ) < t / 2, by linarith) _,
  apply bounded_of_bdd_above_of_bdd_below,
  { refine hf.map_bdd_above h ⟨a + t / 2, _, h _⟩,
    { rw [real.closed_ball_eq_Icc, upper_bounds_Icc],
      { exact left_mem_Ici },
      { linarith } },
    { rw [add_mem_closed_ball_iff_norm, real.norm_of_nonneg],
      linarith } },
  { refine hf.map_bdd_below h ⟨a - t / 2, _, h _⟩,
    { rw [real.closed_ball_eq_Icc, lower_bounds_Icc],
      { exact right_mem_Iic },
      { linarith } },
    { rw [sub_eq_add_neg, add_mem_closed_ball_iff_norm, real.norm_of_nonpos];
      linarith } }
end
