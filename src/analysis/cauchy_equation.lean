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

variables {ι : Type*} [fintype ι]

local notation `ℝⁿ` := ι → ℝ

/-- **Cauchy's functional equation**. An additive monoid homomorphism automatically preserves `ℚ`.
-/
theorem add_monoid_hom.is_linear_map_rat (f : ℝ →+ ℝ) :
  is_linear_map ℚ f := by exact ⟨map_add f, λ c x, add_monoid_hom.map_rat_cast_smul f ℝ ℝ c x⟩

-- should this one get generalised?
lemma exists_real_preimage_ball_pos_volume (f : ℝ → ℝ) :
  ∃ (r z : ℝ), 0 < volume (f⁻¹' (ball z r)) :=
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

lemma exists_zero_nhds_bounded (f : ℝ →+ ℝ)
  (h : measurable f) :
  ∃ (U : set ℝ), U ∈ nhds (0 : ℝ) ∧ metric.bounded (f '' U) :=
begin
  rcases (exists_real_preimage_ball_pos_volume f) with ⟨r, z, hr⟩,
  have hrm : measurable_set (f⁻¹' (ball z r)),
  { apply h,
    exact measurable_set_ball },
  rcases (steinhaus_theorem_add volume (f⁻¹' (ball z r)) hrm hr) with ⟨U, hU0, hUr⟩,
  refine ⟨U, hU0, _⟩,
  { rw (metric.bounded_iff_subset_ball (0 : ℝ)),
    use 2 * r,
    simp only [image_subset_iff],
    convert subset.trans hUr _,
    intros x hx,
    rw mem_sub at hx,
    rcases hx with ⟨a, b, ha, hb, habx⟩,
    rw [mem_preimage, mem_ball_iff_norm] at ha,
    rw [mem_preimage, mem_ball_iff_norm'] at hb,
    simp only [mem_preimage, mem_closed_ball_zero_iff, ← habx],
    calc ∥f (a - b)∥ ≤ ∥ f a - f b ∥ : by simp only [map_sub]
    ... = ∥ (f a - z) + (z - f b) ∥ : by abel
    ... ≤ ∥ f a - z ∥ + ∥ z - f b ∥  : norm_add_le (f a - z) (z - f b)
    ... ≤ 2 * r : by linarith }
end

lemma additive_continuous_at_zero_of_bounded_nhds_zero (f : ℝ →+ ℝ) {U : set ℝ}
  (hU : U ∈ nhds (0 : ℝ)) (hbounded : metric.bounded (f '' U)) : continuous_at f 0 :=
begin
  rcases (metric.mem_nhds_iff.mp hU) with ⟨δ, hδ, hUε⟩,
  rcases ((metric.bounded_iff_subset_ball (0 : ℝ)).mp
    (metric.bounded.mono (image_subset f hUε) hbounded)) with ⟨C, hC⟩,
  rw continuous_at_iff,
  intros ε hε,
  simp only [gt_iff_lt, dist_zero_right, _root_.map_zero, exists_prop],
  cases (exists_nat_gt (C / ε)) with n hn,
  obtain hC0 | rfl | hC0 := lt_trichotomy C 0,
  { simp only [closed_ball_eq_empty.mpr hC0, image_subset_iff, preimage_empty] at hC,
    rw [subset_empty_iff, ball_eq_empty] at hC,
    linarith },
  { simp only [closed_ball_zero] at hC,
    refine ⟨δ, hδ, λ x hxδ, _⟩,
    replace hxδ : f x ∈ f '' (ball 0 δ),
    { simp only [mem_image, mem_ball_zero_iff],
        refine ⟨x, hxδ, rfl⟩},
    replace hxδ := mem_of_subset_of_mem hC hxδ,
    suffices : f x = 0,
    { simp only [this, norm_zero],
      exact hε },
    { simp only [← mem_singleton_iff, hxδ] }},
  { use δ/n,
    split,
    { apply div_pos hδ (lt_trans (div_pos hC0 hε) hn) },
    { intros x hxδ,
      have h2 : f (n • x) = n • f x, { exact map_nsmul f x n },
      have hnpos : 0 < (n : ℝ) := (lt_trans (div_pos hC0 hε) hn),
      simp only [nsmul_eq_mul] at h2,
      simp only [mul_comm, ← div_eq_iff (ne.symm (ne_of_lt hnpos))] at h2,
      rw ← h2,
      replace hxδ : ∥ x * n ∥ < δ,
      { simp only [norm_mul, real.norm_coe_nat, ← lt_div_iff hnpos, hxδ], },
      norm_num,
      replace hxδ : f (x * n) ∈ f '' (ball 0 δ),
      { simp only [mem_image, mem_ball_zero_iff],
        refine ⟨x * n, hxδ, rfl⟩ },
      rw [div_lt_iff hnpos, ← mem_ball_zero_iff],
      apply mem_of_subset_of_mem (subset.trans hC _) hxδ,
      apply closed_ball_subset_ball,
      rw (div_lt_iff hε) at hn,
      simpa [mul_comm] using hn }}
end

lemma additive_continuous_at_zero (f : ℝ →+ ℝ)
  (h : measurable f) : continuous_at f 0 :=
begin
  rcases (exists_zero_nhds_bounded f h) with ⟨U, hU, hbounded⟩,
  exact additive_continuous_at_zero_of_bounded_nhds_zero f hU hbounded
end

lemma continuous_of_measurable (f : ℝ →+ ℝ)
  (h : measurable f) : continuous f :=
  by exact uniform_continuous.continuous
    (uniform_continuous_of_continuous_at_zero f (additive_continuous_at_zero f h))

-- do we want this one and where would it go?
lemma is_linear_map_iff_apply_eq_apply_one_mul {M : Type*} [comm_semiring M] (f : M →+ M) :
  is_linear_map M f ↔ ∀ x : M, f x = f 1 * x :=
begin
  split,
  { intros h x,
    convert h.2 x 1 using 1,
    { simp only [algebra.id.smul_eq_mul, mul_one] },
    { simp only [mul_comm, algebra.id.smul_eq_mul] }},
  { intros h,
    refine ⟨map_add f, λ c x, _⟩,
    rw [smul_eq_mul, smul_eq_mul, h (c * x), h x, ← mul_assoc, mul_comm _ c, mul_assoc] }
end

lemma is_linear_rat (f : ℝ →+ ℝ) : ∀ (q : ℚ), f q = f 1 * q :=
begin
  intro q,
  suffices h1 : f ((q : ℝ) • 1) = (q : ℝ) • f 1,
  { convert h1 using 1,
    { simp only [algebra.id.smul_eq_mul, mul_one], },
    { simp only [mul_comm, algebra.id.smul_eq_mul] }},
  { rw map_rat_cast_smul f ℝ ℝ q 1 }
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
  refine ⟨2 * M, λ x hxδ, _⟩,
  suffices : ∥ f (x + a) ∥ + ∥ f a ∥ ≤ 2 * M,
  { apply le_trans _ this,
    simp only [_root_.map_add, norm_le_add_norm_add] },
  { rw two_mul,
    apply add_le_add,
    { apply hM,
      apply hδa,
      simp only [mem_ball],
      convert hxδ,
      rw [← dist_zero_right, ← dist_add_right x 0 a, zero_add] },
    { apply hM,
      apply hδa,
      simpa [mem_ball, dist_self] }}
end

lemma continuous.is_linear_real  (f : ℝ →+ ℝ) (h : continuous f) : is_linear_map ℝ f :=
begin
  rw is_linear_map_iff_apply_eq_apply_one_mul,
  have h1 := is_linear_rat f,
  intro x,
  apply eq_of_norm_sub_le_zero,
  apply le_of_forall_pos_lt_add,
  by_contra hf,
  push_neg at hf,
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
    { apply lt_min hδ,
      apply mul_pos,
      { linarith },
      { simp only [_root_.inv_pos, norm_pos_iff, ne.def, hf1, not_false_iff] }},
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
    apply lt_of_le_of_lt _ h3,
    apply le_trans _ (norm_add_le _ _),
    apply le_of_eq,
    congr,
    abel }
end

-- to generalize
lemma add_monoid_hom.continuous_at_iff_continuos_at_zero (f : ℝ →+ ℝ) {x : ℝ} :
  continuous_at f x ↔ continuous_at f 0 :=
begin
  split,
  { intro hx,
    rw [← sub_self x, continuous_at_iff],
    intros ε hε,
    rcases ((continuous_at_iff.mp hx) ε hε) with ⟨δ, hδ, hδf⟩,
    refine ⟨δ, hδ, λ y hyδ, _⟩,
    replace hyδ : dist (y + x) x < δ,
    { convert hyδ using 1,
      simp only [dist_eq_norm],
      abel },
    convert hδf hyδ using 1,
    simp only [dist_eq_norm, map_sub, _root_.map_add],
    abel },
  { intro h0,
    apply continuous.continuous_at (uniform_continuous.continuous
      ((uniform_continuous_of_continuous_at_zero f) h0)) }
end

lemma is_linear_real_of_continuous_at (f : ℝ →+ ℝ) {y : ℝ} (h : continuous_at f y) :
  is_linear_map ℝ f := by exact continuous.is_linear_real f
    (uniform_continuous.continuous (uniform_continuous_of_continuous_at_zero f
    ((f.continuous_at_iff_continuos_at_zero).mp h)))


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
  { apply hf.map_bdd_above h _,
    use a + t / 2,
    simp only [real.closed_ball_eq_Icc, mem_inter_eq],
    refine ⟨_, h _⟩,
    { rw upper_bounds_Icc,
      { exact left_mem_Ici },
      { linarith } },
    { rw [add_mem_closed_ball_iff_norm, real.norm_of_nonneg],
      linarith }},
  { apply hf.map_bdd_below h _,
    use a - t / 2,
    simp only [real.closed_ball_eq_Icc, mem_inter_eq],
    refine ⟨_, h _⟩,
    { rw lower_bounds_Icc,
      { exact right_mem_Iic },
      { linarith } },
    { rw [sub_eq_add_neg, add_mem_closed_ball_iff_norm, real.norm_of_nonpos];
      linarith }}
end
