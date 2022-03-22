import measure_theory.group.measure

/-!
# Cauchy's Functional Equation
-/


open add_monoid_hom measure_theory measure_theory.measure metric

theorem cauchy_rational (f : ℝ →+ ℝ) :
  is_linear_map ℚ f := by exact ⟨map_add f, λ c x, add_monoid_hom.map_rat_cast_smul f ℝ ℝ c x⟩

lemma prereq (μ : measure ℝ) [is_add_haar_measure μ] (f : ℝ →+ ℝ) (h : @measurable ℝ ℝ (borel ℝ) (borel ℝ) f) :
  ∃ (C δ : ℝ), 0 < C ∧ 0 < δ ∧ ∀ (x : ℝ), x ∈ closed_ball (0 : ℝ) δ → ∥f x∥ ≤ C :=
begin
  have h1 : ∃ (r : ℝ), 0 < r ∧ μ (f⁻¹' (closed_ball 0 r)) ≠ 0,
  { by_contra hr,
    push_neg at hr,
    sorry },
  cases h1 with r hr,
  set E : set ℝ := f⁻¹' (closed_ball 0 r) with hE,
  have h2 : ∃ (δ : ℝ), 0 < δ ∧ closed_ball (0 : ℝ) δ ⊆ E -ᵥ E,
  { sorry },
  cases h2 with δ hδ,
  refine ⟨(2 * r), δ, _, hδ.1, λ x hx, _⟩,
  { linarith [hr.1] },
  { replace hx := set.mem_of_subset_of_mem hδ.2 hx,
    rw set.mem_vsub at hx,
    rcases hx with ⟨a, b, ha, hb, hab⟩,
    rw ← hab,
    simp only [vsub_eq_sub, map_sub],
    calc ∥f a - f b∥ ≤ ∥ f a ∥ + ∥ f b ∥ : norm_sub_le (f a) (f b)
      ... ≤ 2 * r : by linarith [(mem_closed_ball_zero_iff).mp (set.mem_preimage.mp ha),
      (mem_closed_ball_zero_iff).mp (set.mem_preimage.mp hb)]}
end

lemma prereq2 (μ : measure ℝ) [is_add_haar_measure μ] (f : ℝ →+ ℝ)
  (h : @measurable ℝ ℝ (borel ℝ) (borel ℝ) f) : continuous_at f 0 :=
begin
  rw continuous_at_iff,
  intros ε hε,
  simp only [gt_iff_lt, dist_zero_right, _root_.map_zero, exists_prop],
  have h1 := prereq μ f h,
  rcases h1 with ⟨C, δ, h1⟩,
  cases (exists_nat_gt (C / ε)) with n hn,
  use δ/n,
  split,
  { apply div_pos h1.2.1 (lt_trans (div_pos h1.1 hε) hn) },
  { intros x hxδ,
    have h2 : f (n • x) = n • f x, { exact map_nsmul f x n },
    have hnpos : 0 < (n : ℝ) := (lt_trans (div_pos h1.1 hε) hn),
    simp only [nsmul_eq_mul] at h2,
    simp only [mul_comm, ← div_eq_iff (ne.symm (ne_of_lt hnpos))] at h2,
    rw ← h2,
    replace hxδ : ∥ x * n ∥ ≤ δ,
    { simp only [norm_mul, real.norm_coe_nat, ← le_div_iff hnpos, le_of_lt hxδ], },
    norm_num,
    simp only [mem_closed_ball_zero_iff] at h1,
    apply lt_of_le_of_lt (div_le_div (le_of_lt h1.1) (h1.2.2 (x * n) hxδ) hnpos (le_of_eq rfl)) _,
    simp only [div_lt_iff hnpos, mul_comm ε _, ← div_lt_iff hε, hn] }
end


lemma continuous_of_measurable (μ : measure ℝ) [is_add_haar_measure μ] (f : ℝ →+ ℝ)
  (h : @measurable ℝ ℝ (borel ℝ) (borel ℝ) f) : continuous f :=
  by exact uniform_continuous.continuous
    (uniform_continuous_of_continuous_at_zero f (prereq2 μ f h))
