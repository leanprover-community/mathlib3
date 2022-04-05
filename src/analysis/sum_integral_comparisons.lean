import measure_theory.integral.interval_integral
import algebra.order.floor

open_locale big_operators

lemma convert_finite_sum_to_interval_integral {m n : ℕ} {f : ℝ → ℝ} (hmn : m ≤ n) :
  ∑ (i : ℕ) in finset.Ico m n, ∫ (x : ℝ) in ↑i..↑i + 1, f ↑i =
  ∫ (x : ℝ) in m..n, f ↑⌊x⌋₊ :=
begin
  conv {
    to_lhs,
    congr,
    skip,
    funext,
    rw integral_const_on_unit_interval i (f ↑i),
  },
  obtain ⟨n', hn'⟩ := le_iff_exists_add.mp hmn,
  rw [hn', ←sum_integral_adjacent_intervals'],
  { apply finset.sum_congr rfl,
    intros x hx,
    rw ←integral_const_on_unit_interval x (f ↑x),
    apply interval_integral.integral_congr_ae,
    rw [set.interval_oc_of_le (calc (x : ℝ) ≤ x + 1 : by simp), ae_iff],
    refine real.measure_space.volume.to_outer_measure.mono_null _ (@real.volume_singleton ((x : ℝ) + 1)),
    simp only [set.mem_Ioc, and_imp, not_forall, exists_prop, set.subset_singleton_iff, set.mem_set_of_eq],
    intros y hy hy' hf,
    cases lt_or_eq_of_le hy',
    { exfalso, rw floor_eq_on_Ico x y ⟨le_of_lt hy, h⟩ at hf, exact hf rfl, },
    { exact h, },
  },
  { intros k hk,
    rw [interval_integrable_iff, set.interval_oc_of_le (calc (k : ℝ) ≤ ↑(k + 1) : by simp)],
    have : integrable_on (λ x : ℝ, f ↑k) (set.Ioc (k : ℝ) (↑k + 1)) real.measure_space.volume,
    { simp, },
    apply integrable_on.congr_fun' this,
    rw [filter.eventually_eq, ae_iff],
    simp only [measure.restrict_apply', measurable_set_Ioc],
    refine outer_measure.mono_null _ _ (@real.volume_singleton ((k : ℝ) + 1)),
    simp only [set.subset_singleton_iff, set.mem_inter_eq, set.mem_set_of_eq, set.mem_Ioc, and_imp],
    intros y hf hy hy',
    cases lt_or_eq_of_le hy',
    { exfalso, rw floor_eq_on_Ico k y ⟨le_of_lt hy, h⟩ at hf, exact hf rfl, },
    { exact h, }, },
end

lemma antitone_integral_le_sum {a b : ℕ} {f : ℝ → ℝ} (hab : a ≤ b)
  (hf : antitone_on f (set.Icc a b)) : ∫ x in a..b, f x ≤ ∑ x in finset.Ico a b, f x :=
begin
  have : ∀ (x : ℝ), x ∈ set.Icc (a : ℝ) ↑b → f x ≤ f ⌊x⌋₊,
  { intros x hx,
    apply hf (floor_mem_Icc_of_Icc hx) hx,
    exact floor_le (calc (0 : ℝ) ≤ ↑a : by simp ... ≤ x : hx.left), },
  transitivity,
  refine interval_integral.integral_mono_on (cast_le.mpr hab) _ _ this,
  apply antitone_on.interval_integrable,
  rwa set.interval_of_le (calc (a : ℝ) ≤ b : cast_le.mpr hab),
  apply antitone_on.interval_integrable,
  rwa set.interval_of_le (calc (a : ℝ) ≤ b : cast_le.mpr hab),
  intros c hc d hd hcd,
  exact hf (floor_mem_Icc_of_Icc hc) (floor_mem_Icc_of_Icc hd) (cast_le.mpr $ floor_mono hcd),
  conv {
    to_rhs,
    congr,
    skip,
    funext,
    rw ← integral_const_on_unit_interval x (f ↑x),
  },
  rw convert_finite_sum_to_interval_integral hab,
end
