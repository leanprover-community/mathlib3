import probability.martingale
import probability.independence
import probability.integration

open measure_theory filter set

open_locale probability_theory

localized "notation `Var[` X `]` := 𝔼[X^2] - 𝔼[X]^2" in probability_theory
localized "notation `ℙ` := volume" in probability_theory


open_locale topological_space big_operators measure_theory probability_theory ennreal


lemma ennreal.one_le_two : (1 : ℝ≥0∞) ≤ 2 := ennreal.one_lt_two.le

lemma measure_theory.mem_ℒp.integrable_sq
  {α : Type*} {m : measurable_space α} {μ : measure α} {f : α → ℝ} (h : mem_ℒp f 2 μ) :
  integrable (λ x, (f x)^2) μ :=
begin
  rw ← mem_ℒp_one_iff_integrable,
  convert h.norm_rpow ennreal.two_ne_zero ennreal.two_ne_top,
  ext x,
  simp only [real.norm_eq_abs, ennreal.to_real_bit0, ennreal.one_to_real],
  conv_rhs { rw [← nat.cast_two, real.rpow_nat_cast] },
  simp only [pow_bit0_abs],
end

namespace probability_theory

variables {Ω : Type*} [measure_space Ω] [is_probability_measure (ℙ : measure Ω)]


theorem indep_fun.Var_add {X Y : Ω → ℝ} (hX : mem_ℒp X 2) (hY : mem_ℒp Y 2) (h : indep_fun X Y) :
  Var[X + Y] = Var[X] + Var[Y] :=
calc
Var[X + Y] = 𝔼[λ a, (X a)^2 + (Y a)^2 + 2 * X a * Y a] - 𝔼[X+Y]^2 :
  by { congr' 2, ext a, simp only [pi.pow_apply, pi.add_apply], ring }
... = (𝔼[X^2] + 𝔼[Y^2] + 2 * 𝔼[X * Y]) - (𝔼[X] + 𝔼[Y])^2 :
begin
  simp only [pi.add_apply, pi.pow_apply, pi.mul_apply, mul_assoc],
  rw [integral_add, integral_add, integral_add, integral_mul_left],
  { exact hX.integrable ennreal.one_le_two },
  { exact hY.integrable ennreal.one_le_two },
  { exact hX.integrable_sq },
  { exact hY.integrable_sq },
  { exact hX.integrable_sq.add hY.integrable_sq },
  { apply integrable.const_mul,
    exact h.integrable_mul (hX.integrable ennreal.one_le_two) (hY.integrable ennreal.one_le_two) }
end
... = (𝔼[X^2] + 𝔼[Y^2] + 2 * (𝔼[X] * 𝔼[Y])) - (𝔼[X] + 𝔼[Y])^2 :
begin
  congr,
  exact h.integral_mul_of_integrable
    (hX.integrable ennreal.one_le_two) (hY.integrable ennreal.one_le_two),
end
... = Var[X] + Var[Y] : by ring

open_locale classical

lemma sq_add (x y : ℝ) : (x + y)^2 = x^2 + y^2 + 2 * x * y := by ring

lemma sq_sum {ι : Type*} {s : finset ι} (f : ι → ℝ) :
  (∑ i in s, f i) ^ 2 = (∑ i in s, (f i)^2) + ∑ i in s, ∑ j in s \ {i}, f i * f j :=
begin
  induction s using finset.induction_on with k s ks IH,
  { simp only [finset.sum_empty, zero_pow', ne.def, bit0_eq_zero, nat.one_ne_zero, not_false_iff,
    add_zero] },
  have A : ∑ (i : ι) in s, ∑ (j : ι) in insert k s \ {i}, f i * f j
    = ∑ (i : ι) in s, (f i * f k + ∑ (j : ι) in s \ {i}, f i * f j),
  { refine finset.sum_congr rfl _,
    assume i hi,
    rw [finset.insert_sdiff_of_not_mem, finset.sum_insert],
    { simpa only [finset.mem_sdiff, not_and] using ks },
    { assume hk,
      apply ks,
      rwa finset.mem_singleton.1 hk } },
  rw [finset.sum_insert ks, finset.sum_insert ks, finset.sum_insert ks,
      finset.insert_sdiff_of_mem _ (finset.mem_singleton_self _),
      finset.sdiff_eq_self_of_disjoint (finset.disjoint_singleton_right.2 ks), sq_add, IH, A,
      finset.sum_add_distrib, ← finset.mul_sum, ← finset.sum_mul,
      mul_comm ((∑ (x : ι) in s, f x)) (f k)],
  ring,
end

theorem indep_fun.Var_sum {ι : Type*} {X : ι → Ω → ℝ} {s : finset ι}
  (hs : ∀ i ∈ s, mem_ℒp (X i) 2) (h : set.pairwise ↑s (λ i j, indep_fun (X i) (X j))) :
  Var[∑ i in s, X i] = ∑ i in s, Var[X i] :=
calc
Var[∑ i in s, X i]
    = 𝔼[∑ i in s, (X i)^2 + ∑ i in s, ∑ j in s \ {i}, X i * X j] - 𝔼[∑ i in s, X i]^2 :
by { congr, ext x, simp only [sq_sum, pi.pow_apply, finset.sum_apply, pi.add_apply, pi.mul_apply] }
... = (𝔼[∑ i in s, (X i)^2] + 𝔼[∑ i in s, ∑ j in s \ {i}, X i * X j]) - (∑ i in s, 𝔼[X i])^2 :
begin
  simp only [pi.add_apply, finset.sum_apply, pi.pow_apply, pi.mul_apply],
  rw integral_add,
  sorry,
  { exact integrable_finset_sum _ (λ i hi, (hs i hi).integrable_sq) },
  { apply integrable_finset_sum _ (λ i hi, _),
    apply integrable_finset_sum _ (λ j hj, _),

  }
end
... = ∑ i in s, Var[X i] : sorry


theorem
  strong_law1
  (X : ℕ → Ω → ℝ) (hint : ∀ i, integrable (X i))
  (hindep : pairwise (λ i j, indep_fun (X i) (X j)))
  (h'i : ∀ i j, measure.map (X i) ℙ = measure.map (X j) ℙ)
  (h''i : ∀ i ω, 0 ≤ X i ω) :
  ∀ᵐ ω, tendsto (λ n, (∑ i in finset.range n, X i ω) / (n : ℝ)) at_top (𝓝 (𝔼[X 0])) :=
begin
  have A : ∀ i, strongly_measurable (indicator (Icc (0 : ℝ) i) id) :=
    λ i, strongly_measurable_id.indicator measurable_set_Icc,
  let Y := λ (n : ℕ), (indicator (Icc (0 : ℝ) n) id) ∘ (X n),
  have : ∀ n, ae_strongly_measurable (Y n) ℙ :=
    λ n, (A n).ae_strongly_measurable.comp_ae_measurable (hint n).ae_measurable,
  have : pairwise (λ i j, indep_fun (Y i) (Y j) ℙ),
  { assume i j hij,
    exact (hindep i j hij).comp (A i).measurable (A j).measurable },

end

end probability_theory
