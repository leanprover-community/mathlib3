import measure_theory.group.measure measure_theory.measure.lebesgue topology.basic
import analysis.normed_space.pointwise measure_theory.measure.haar
import measure_theory.measure.haar_lebesgue



open add_monoid_hom measure_theory measure_theory.measure metric nnreal set
open_locale pointwise

/-!
# Cauchy's Functional Equation
-/

theorem cauchy_rational_add (f : ℝ →+ ℝ) :
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

lemma exists_zero_nbhd_bounded (f : ℝ →+ ℝ)
  (h : @measurable ℝ ℝ (real.measurable_space) (borel ℝ) f) :
  ∃ (U : set ℝ), U ∈ nhds (0 : ℝ) ∧ metric.bounded (f '' U) :=
begin
  rcases (exists_real_preimage_ball_pos_volume f) with ⟨r, z, hr⟩,
  have hrm : measurable_set (f⁻¹' (ball z r)),
  { apply h,
    exact measurable_set_ball },
  rcases (steinhaus_theorem_add ℝ (f⁻¹' (ball z r)) hrm hr) with ⟨U, hU0, hUr⟩,
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

lemma additive_continuous_at_zero_of_bounded_nbhd_zero (f : ℝ →+ ℝ) {U : set ℝ}
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
  (h : @measurable ℝ ℝ (real.measurable_space) (borel ℝ) f) : continuous_at f 0 :=
begin
  rcases (exists_zero_nbhd_bounded f h) with ⟨U, hU, hbounded⟩,
  exact additive_continuous_at_zero_of_bounded_nbhd_zero f hU hbounded
end

lemma continuous_of_measurable (μ : measure ℝ) [is_add_haar_measure μ] (f : ℝ →+ ℝ)
  (h : @measurable ℝ ℝ (borel ℝ) (borel ℝ) f) : continuous f :=
  by exact uniform_continuous.continuous
    (uniform_continuous_of_continuous_at_zero f (additive_continuous_at_zero f h))


lemma real_eq_forall_pos_lt {a b : ℝ} : (∀ (ε : ℝ), 0 < ε → ∥ a - b ∥ < ε) → a = b :=
begin
  intro h,
  contrapose h,
  push_neg,
  use ∥ a - b ∥ / 2,
  split,
  { rw lt_div_iff (show 0 < (2 : ℝ), by norm_num),
    norm_num [sub_eq_zero, h] },
  { rw div_le_iff (show 0 < (2 : ℝ), by norm_num),
    simp only [mul_two, le_add_iff_nonneg_left, norm_nonneg] }
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

lemma additive_is_bounded_of_bounded_on_interval (f : ℝ →+ ℝ) {a b : ℝ} (hab : a < b)
  (h : metric.bounded (f '' set.Icc a b)) :
  ∀ (U : set ℝ), metric.bounded U → metric.bounded (f '' U) :=
begin
  contrapose h,
  simp only [not_forall, exists_prop] at h,
  rcases h with ⟨U, hU, hUf⟩,
  sorry
end

lemma is_linear_real_of_continuous (f : ℝ →+ ℝ) (h : continuous f) : ∀ (x : ℝ), f x  = f 1 * x :=
begin
  have h1 := is_linear_rat f,
  intro x,
  apply real_eq_forall_pos_lt,
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

lemma additive_continuous_at_iff_continuos_at_zero (f : ℝ →+ ℝ) {x : ℝ} :
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
  ∀ (x : ℝ), f x  = f 1 * x := by exact is_linear_real_of_continuous f
    (uniform_continuous.continuous (uniform_continuous_of_continuous_at_zero f
    ((additive_continuous_at_iff_continuos_at_zero f).mp h)))


lemma is_linear_map_real_of_continuous (f : ℝ →+ ℝ) (h : continuous f) : is_linear_map ℝ f :=
begin
  refine ⟨map_add f,λ c x, _⟩,
  rw [smul_eq_mul, smul_eq_mul, is_linear_real_of_continuous f h (c * x),
    is_linear_real_of_continuous f h x],
  ring_exp_eq
end

lemma is_linear_of_bounded_interval (f : ℝ →+ ℝ) {a b : ℝ} (hab : a < b)
  (hf : metric.bounded (f '' (set.Icc a b))) : ∀ (x : ℝ), f x = f 1 * x :=
begin
  replace hf := (additive_is_bounded_of_bounded_on_interval f hab hf) (set.Icc (-1 : ℝ) 1) _,
  { have : continuous_at f 0,
    { apply additive_continuous_at_zero_of_bounded_nbhd_zero f _ hf,
      rw metric.mem_nhds_iff,
      refine ⟨1, one_pos, _⟩,
      rw real.ball_eq_Ioo,
      convert Ioo_subset_Icc_self;
      norm_num },
    exact is_linear_real_of_continuous_at f this },
  { exact bounded_Icc (-1 : ℝ) 1 },
end


--todo add the monotone assumption case
