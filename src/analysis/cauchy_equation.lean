import tactic data.real.basic linear_algebra order data.rat.basic data.int.basic topology.basic
import topology.instances.real

theorem cauchy_rational (f : ℚ → ℝ) (h : ∀ (x y : ℚ), f (x + y) = f x + f y) :
  is_linear_map ℚ f := 
begin
  refine ⟨h, λ c x, _⟩,
  have h0 : f 0 = 0,
  { simpa using h 0 0 },
  have hodd : ∀ (x : ℚ), f (- x) = - f x,
  { intro x,
    specialize h x (-x),
    simp only [h0, add_right_neg] at h,
    linarith },
  have : ∀ (n : ℕ) (x : ℚ), f (n * x) = n * f x,
  { intros n x,
    induction n with d hd,
    { simpa using h0 },
    { simp only [nat.cast_succ, add_mul, one_mul, h (d * x) x, hd] }},
  obtain rfl | hc := eq_or_ne c 0,
  { simpa using h0 },
  suffices : (c.denom : ℝ) * f (c • x) = (c.denom * c : ℝ) • f x,
    { simp only [smul_eq_mul, mul_assoc] at this,
      apply mul_left_cancel₀ _ this,
      simp only [ne.def, nat.cast_eq_zero, rat.denom_ne_zero c, not_false_iff] },
  simp only [smul_eq_mul, ← mul_assoc, mul_comm _ c, rat.mul_denom_eq_num,
    ← this c.denom],
  obtain hc | hc := lt_or_gt_of_ne hc,
  { have h1 : 0 ≤ - c := by simp only [right.nonneg_neg_iff, le_of_lt hc],
    suffices h2 : f (((-c).num) * x) = ((- c).num) * f x,
    { simp only [rat.num_neg_eq_neg_num, int.cast_neg, neg_mul, hodd, neg_inj] at h2,
      have h3 : (c.num : ℝ) = c * c.denom,
      { norm_cast,
        rw ← rat.mul_denom_eq_num },
      rw [h2, h3, mul_comm (c : ℝ) _] },
    rw [← abs_eq_self.mpr (rat.num_nonneg_iff_zero_le.mpr h1), int.abs_eq_nat_abs],
    norm_cast,
    rw ← this },
  { rw [← abs_eq_self.mpr (rat.num_nonneg_iff_zero_le.mpr (le_of_lt hc)), int.abs_eq_nat_abs],
    norm_cast,
    rw [mul_comm _ c, rat.mul_denom_eq_num, this],
    rw [← abs_eq_self.mpr (rat.num_nonneg_iff_zero_le.mpr (le_of_lt hc)), int.abs_eq_nat_abs],
    norm_cast }
end

theorem additive_continuous_at_imp_continuous (f : ℝ → ℝ) {a : ℝ} 
  (h₁  : ∀ (x y : ℝ), f (x + y) = f x + f y) (h₂ : continuous_at f a) : 
  continuous f :=
begin
  rw continuous_iff_continuous_at,
  intro b,
  set g : ℝ → ℝ := λ x, x + (a - b) with hg,
  set k : ℝ → ℝ := λ x, ((f ∘ g) x - f (a - b)) with hk,
  have hfk : f = k,
  { ext x,
    simp only [hk, function.comp_app, h₁, add_tsub_cancel_right] },
  rw hfk,
  rw hk,
  apply continuous_at.sub,
  { simp only [function.comp_app],
    apply continuous_at.comp,
    { simp only [hg, add_sub_cancel'_right, h₂],},
    { apply continuous.continuous_at,
      continuity }},
  { apply continuous.continuous_at,
    continuity }
end

theorem cauchy_real (f : ℝ → ℝ) {a : ℝ} (h₁ : ∀ (x y : ℝ), f (x + y) = f x + f y)
  (h₂ : continuous_at f a) :
  is_linear_map ℝ f := 
begin
  refine ⟨h₁, λ c x, _⟩,
  by_contra h,
  set g : ℚ → ℝ := λ x, f x with hg,
  have : ∀ (x : ℚ), g x = g 1 * x,
  { have hgzero : g 0 = 0,
    { sorry },
    sorry },
  sorry
end