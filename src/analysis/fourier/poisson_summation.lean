/-
Copyright (c) 2022 David Loeffler. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Loeffler
-/
import analysis.fourier.add_circle
import measure_theory.integral.exp_decay
import analysis.special_functions.gaussian

noncomputable theory

open_locale real big_operators filter
open function complex set topological_space filter measure_theory

/-!
# Poisson's summation formula

We prove Poisson's summation formula `∑ (n : ℤ), f n = ∑ (n : ℤ), g n`, where `g` is the Fourier
transform of `f`, under the following hypotheses:
* `f` and `g` are continuous functions `ℝ → ℂ`.
* `∀ t:ℝ, g t = ∫ x:ℝ, complex.exp (-2 * π * I * t * x) * f x`.
* `f` is integrable.
* The sum `∑ (n:ℤ), g n` is convergent.
* For all compacts `K ⊂ ℝ`, the sum `∑ (n:ℤ), sup { ‖f(x + n)‖ | x ∈ K }` is convergent.

More practically, we show that if `f` and `g` have exponential decay, then the last three conditions
are automatically satisfied.

(One could conceivably strengthen the result by deriving continuity of `g`, etc, from the Fourier
transform integral rather than making it a hypothesis. However, in the application I have in mind
there is a closed-form formula for `g` from which continuity is obvious.)
-/

/-! ## Preliminaries -/

section eval_clm

variables {β : Type*} [topological_space β] [locally_compact_space β]
  (𝕜 : Type*) [normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]

/-- The continuous linear map given by evaluation at a point. -/
def continuous_map.eval_clm' (x : β) : C(β, E) →L[𝕜] E :=
{ to_fun := (λ f : C(β, E), f x),
  cont := continuous_map.continuous_eval_const' x,
  map_add' := by { intros f g, simp only [continuous_map.coe_add, pi.add_apply]},
  map_smul' := by { intros c f,
    simp only [continuous_map.coe_smul, pi.smul_apply, ring_hom.id_apply]} }

lemma continuous_map.eval_clm'_apply (x : β) (f : C(β, E)) : continuous_map.eval_clm' 𝕜 x f = f x :=
by refl

lemma continuous_map.tsum_apply {α : Type} {f : α → C(β, E)} (hf : summable f) (x : β) :
  (∑' (n : α), f n) x = ∑' (n : α), f n x := (continuous_map.eval_clm' 𝕜 x).map_tsum hf

end eval_clm

lemma real.Union_Ioc_coe_int : (⋃ (n : ℤ), Ioc (n:ℝ) (n + 1)) = univ :=
begin
  rw eq_univ_iff_forall,
  intro x,
  rw mem_Union,
  refine ⟨⌈x⌉ - 1, _, _⟩,
  { rw [int.cast_sub, int.cast_one], linarith [int.ceil_lt_add_one x], },
  { rw [int.cast_sub, int.cast_one], linarith [int.le_ceil x]},
end

lemma real.disjoint_Ioc_coe_int_of_ne {m n : ℤ} (h : m ≠ n) :
disjoint (Ioc (m:ℝ) (m + 1)) (Ioc (n:ℝ) (n + 1)) :=
begin
  rw [disjoint_iff, inf_eq_inter, bot_eq_empty, eq_empty_iff_forall_not_mem],
  contrapose! h,
  obtain ⟨u, hu1, hu2⟩ := h,
  have i1 := hu1.1.trans_le hu2.2,
  have i2 := hu2.1.trans_le hu1.2,
  rw [←int.cast_one, ←int.cast_add, int.cast_lt, int.lt_add_one_iff] at i1 i2,
  linarith,
end

lemma has_sum_interval_integral {f : ℝ → ℂ} (hfi : integrable f) :
  has_sum (λ (n:ℤ), ∫ x in n..n + 1, f x) (∫ (x:ℝ), f x) :=
begin
  conv { congr, funext, rw interval_integral.integral_of_le (by linarith : (n:ℝ) ≤ n + 1) },
  rw [←integral_univ, ←real.Union_Ioc_coe_int],
  refine has_sum_integral_Union (λ i:ℤ, measurable_set_Ioc)
    (λ m n hmn, real.disjoint_Ioc_coe_int_of_ne hmn) _,
  rwa [real.Union_Ioc_coe_int, integrable_on_univ],
end

lemma has_sum_interval_integral' {f : ℝ → ℂ} (hfi : integrable f) :
  has_sum (λ (n:ℤ), ∫ x in 0..1, f (x + n)) (∫ (x:ℝ), f x) :=
begin
  convert has_sum_interval_integral hfi using 2,
  ext1 n,
  rw interval_integral.integral_comp_add_right,
  rw [zero_add, add_comm],
end

/-! ## Shift summability -/

/-- Translating the variable in a continuous map. -/
def shift (f : C(ℝ, ℂ)) (m : ℝ) : C(ℝ, ℂ) :=
continuous_map.mk (λ x:ℝ, f $ x + m) (by continuity)

lemma shift_summable {f : C(ℝ, ℂ)}
  (hf : ∀ (K : compacts ℝ), summable (λ n:ℤ, ‖(shift f n).restrict K‖)) :
  summable (λ n:ℤ, shift f n) :=
continuous_map.summable_of_locally_summable_norm hf

lemma shift_summable_pointwise {f : C(ℝ, ℂ)}
  (hf : ∀ (K : compacts ℝ), summable (λ n:ℤ, ‖(shift f n).restrict K‖)) (x : ℝ) :
  summable (λ n:ℤ, shift f n x) :=
begin
  convert (continuous_map.eval_clm' ℂ x).summable (shift_summable hf),
end

lemma shift_sum_apply {f : C(ℝ, ℂ)}
  (hf : ∀ (K : compacts ℝ), summable (λ n:ℤ, ‖(shift f n).restrict K‖)) (x : ℝ) :
  has_sum (λ n:ℤ, f (x + n)) ((∑' (n:ℤ), shift f n) x) :=
begin
  rw [continuous_map.tsum_apply ℝ (shift_summable hf)],
  exact (shift_summable_pointwise hf x).has_sum,
end

lemma periodic_shift_sum (f : C(ℝ, ℂ)) : periodic ⇑(∑' (n:ℤ), shift f n) 1 :=
-- doesn't require convergence
λ x, begin
  by_cases h : summable (λ n:ℤ, shift f n),
  { simp_rw continuous_map.tsum_apply ℝ h,
    let s : ℤ ≃ ℤ := {to_fun := λ n, n + 1, inv_fun := λ n, n - 1,
      left_inv := λ n, by simp, right_inv := λ n, by simp },
    convert (s.has_sum_iff.mpr (summable.has_sum _)).tsum_eq,
    { ext1 n,
      dsimp [s, shift],
      rw [int.cast_add, int.cast_one],
      congr' 1, ring },
    exact t2_5_space.t2_space,
    exact_mod_cast (continuous_map.eval_clm' ℂ x).summable h },
  { rw tsum_eq_zero_of_not_summable h,
    simp only [continuous_map.coe_zero, pi.zero_apply] },
end

/-- The key lemma for Poisson summation: the `m`-th Fourier coefficient of the periodic function
`∑' (n:ℤ), f (x + n)` is the value at `m` of the Fourier transform of `f`. -/
lemma fourier_coeff_F {f : C(ℝ, ℂ)}
  (hf : ∀ (K : compacts ℝ), summable (λ n:ℤ, ‖(shift f n).restrict K‖))
  (hfi : integrable f) (m : ℤ) :
  ∫ x:ℝ in 0..1, @fourier 1 (-m) x * (∑' (n:ℤ), shift f n) x =
  ∫ x:ℝ, complex.exp (-2 * π * I * m * x) * f x :=
begin
  let e : C(ℝ, ℂ) := (fourier (-m)).comp ⟨(coe : ℝ → unit_add_circle), continuous_quotient_mk⟩,
  have ne : ∀ (x : ℝ), ‖e x‖ = 1 := λ x, abs_coe_circle _,
  conv_lhs { congr, funext, rw [←(shift_sum_apply hf x).tsum_eq, ←tsum_mul_left] },
  -- Use dominated convergence to rewrite the integral of a sum as a sum of integrals,
  -- bounding the `n`-th integrand `fₙ` by the sup norm of `f (x + n)` on `[0, 1]`.
  have := interval_integral.has_sum_integral_of_dominated_convergence
    (λ (n:ℤ) (x:ℝ), ‖(shift f n).restrict (Icc (0:ℝ) 1)‖) -- (the bound)
    (λ (n:ℤ), (map_continuous (e * shift f n)).ae_strongly_measurable) -- (measurability)
    (λ (n:ℤ), ae_of_all _ (λ a ha, _)) -- (nth integrand is bounded by the bound)
    (ae_of_all _ (λ (x : ℝ) hh, hf ⟨Icc (0:ℝ) 1, is_compact_Icc⟩))  -- (the bound is summable)
    _ --  (each bound is integrable)
    (ae_of_all _ (λ x hx, _)), -- sum of f_n is f
  rw ←this.tsum_eq,
  rotate, -- first clear all the subsidiary goals from dominated convergence
  { -- 1/3 : fₙ * e is bounded by the norm of fₙ
    refine le_trans (le_of_eq _) (continuous_map.norm_coe_le_norm _ _),
    refine ⟨a, _⟩,
    { rw interval_oc_of_le (zero_le_one' ℝ) at ha,
      exact mem_of_mem_of_subset ha Ioc_subset_Icc_self },
    rw [continuous_map.coe_mul, pi.mul_apply, norm_mul, continuous_map.coe_restrict, comp_apply,
      subtype.coe_mk, shift, continuous_map.coe_mk, ne, one_mul] },
  { -- 2/3 : bound is integrable (because it's constant!)
    convert interval_integrable_const,
    ext1 x,
    simp only,
    exact real.locally_finite_volume },
  { -- 3/3: the sum of the fₙ is what it should be
    convert summable.has_sum _,
    rw [←summable_norm_iff],
    simp_rw [continuous_map.coe_mul, pi.mul_apply, norm_mul, ne, one_mul],
    rw [summable_norm_iff],
    exact shift_summable_pointwise hf x, },
  -- Now finish by gathering the sum of integrals into an integral over `ℝ`.
  dsimp only,
  convert (has_sum_interval_integral' (_ : integrable (e * f))).tsum_eq,
  { ext1 n,
    refine interval_integral.integral_congr (λ x hx, _),
    dsimp only,
    rw [pi.mul_apply],
    congr' 1,
    { dsimp only [e],
      rw [continuous_map.comp_apply, continuous_map.comp_apply, continuous_map.coe_mk,
        quotient_add_group.coe_add],
      suffices : ((n:ℝ) : unit_add_circle) = 0,
      { rw [this, add_zero], },
      rw add_circle.coe_eq_zero_iff,
      use n, simp only [int.smul_one_eq_coe], } },
  { ext1 x, simp only [fourier_coe_apply, neg_mul, continuous_map.coe_comp, continuous_map.coe_mk,
      pi.mul_apply, comp_app, int.cast_neg, mul_neg, of_real_one, div_one], },
  { refine ⟨(map_continuous (e * f)).ae_strongly_measurable, hfi.2.congr' (ae_of_all _ (λ x, _))⟩,
    rw [pi.mul_apply, norm_mul, ne, one_mul], },
end

/-- Poisson's summation formula. -/
theorem poisson_summation {f : C(ℝ, ℂ)}
  (hf : ∀ (K : compacts ℝ), summable (λ n:ℤ, ‖(shift f n).restrict K‖)) (hfi : integrable f)
  {g : C(ℝ, ℂ)} (hg : summable (λ n:ℤ, g n))
  (hfg : ∀ t:ℝ, g t = ∫ x:ℝ, complex.exp (-2 * π * I * t * x) * f x) :
  ∑' (n:ℤ), f n  = ∑' (n:ℤ), g n :=
begin
  let F' : C(unit_add_circle, ℂ) :=
  { to_fun := periodic.lift (periodic_shift_sum f), continuous_to_fun := by
    { rw [continuous_coinduced_dom],
      exact map_continuous _, } },
  have hT : fact (0 < (1:ℝ)) := fact.mk zero_lt_one,
  convert (@has_pointwise_sum_fourier_series_of_summable 1 hT F' _ 0).tsum_eq.symm using 1,
  { dsimp [F'],
    rw [←quotient_add_group.coe_zero, periodic.lift_coe, ←(shift_sum_apply hf 0).tsum_eq],
    refine tsum_congr (λ n, _),
    simp only [continuous_map.coe_mk, zero_add], },
  { congr' 1,
    ext1 n,
    simp_rw hfg,
    refine eq.trans (@fourier_coeff_F f hf hfi n).symm _,
    rw [fourier_coeff_eq_interval_integral, div_one, one_smul, zero_add, fourier_eval_zero,
      smul_eq_mul, mul_one],
    refl, },
  { convert hg,
    ext1 n,
    rw [hfg, fourier_coeff_eq_interval_integral, div_one, one_smul,
      zero_add],
    exact fourier_coeff_F hf hfi n },
end

section exp_decay
/- various lemmas about exponentially decaying functions (top, bottom, and two-sided) -/

variables {E : Type} [normed_add_comm_group E]

/-- The property of having exponential decay at `+∞`. -/
def exp_decay_at_top (f : ℝ → E) : Prop :=
∃ (b : ℝ), (0 < b) ∧ (f =O[at_top] (λ x, real.exp (-b * x)))

namespace exp_decay_at_top

lemma trans_eventually_le {f g : ℝ → E} (hf : exp_decay_at_top f)
  (hg : ∀ᶠ (x:ℝ) in at_top, ‖g x‖ ≤ ‖f x‖) : exp_decay_at_top g :=
begin
  rcases hf with ⟨b, hb1, hb2⟩,
  refine ⟨b, hb1, asymptotics.is_O.trans _ hb2⟩,
  rw [asymptotics.is_O],
  use 1,
  simpa [asymptotics.is_O_with, one_mul] using hg,
end

lemma integrable_on_Ioi {f : C(ℝ, E)} (hf : exp_decay_at_top f) (a : ℝ) :
  integrable_on f (Ioi a) :=
begin
  rcases hf with ⟨b, hb1, hb2⟩,
  exact integrable_of_is_O_exp_neg hb1 (map_continuous f).continuous_on hb2,
end

lemma shift {f : ℝ → E} (hf : exp_decay_at_top f) (t : ℝ) :
  exp_decay_at_top (λ x, f (x + t)) :=
begin
  rcases hf with ⟨b, hb1, hb2⟩,
  refine ⟨b, hb1, _⟩,
  have := hb2.comp_tendsto (tendsto_at_top_add_const_right at_top t tendsto_id),
  refine this.trans (asymptotics.is_O_of_le' _ (λ x, _)),
  show ‖real.exp ((-b) * (x + t))‖ ≤ real.exp (-b * t) * ‖real.exp (-b * x)‖,
  { rw [mul_add, real.exp_add, norm_mul],
    conv_lhs { rw mul_comm, congr, rw real.norm_of_nonneg (real.exp_pos _).le, } },
end

lemma norm_Icc {f : C(ℝ, E)} (hf : exp_decay_at_top f) (R S : ℝ) :
  exp_decay_at_top (λ x:ℝ, ‖f.restrict (Icc (x + R) (x + S))‖) :=
begin
  rcases hf with ⟨b, hb, hb'⟩, refine ⟨b, hb, _⟩,
  obtain ⟨c, hc0, hc⟩ := hb'.exists_nonneg,
  rw asymptotics.is_O,
  refine ⟨c * real.exp (-b * R), _⟩,
  rw [asymptotics.is_O_with, eventually_at_top] at hc ⊢,
  cases hc with d hd,
  refine ⟨d - R, λ y hy, _⟩,
  rw [real.norm_of_nonneg, continuous_map.norm_le],
  swap, exact mul_nonneg (mul_nonneg hc0 (real.exp_pos _).le) (norm_nonneg _),
  swap, exact norm_nonneg _,
  rintro ⟨x, hx⟩,
  rw [continuous_map.coe_restrict, comp_app, subtype.coe_mk],
  refine (hd x (by linarith [hx.1])).trans _,
  rw mul_assoc,
  apply mul_le_mul_of_nonneg_left _ hc0,
  simp_rw [real.norm_eq_abs, real.abs_exp, ←real.exp_add, real.exp_le_exp, ←mul_add,
    mul_le_mul_left_of_neg (by linarith : -b < 0)],
  rw add_comm, exact hx.1,
end

lemma summable_coe_nat [complete_space E] {f : ℝ → E} (hf : exp_decay_at_top f) :
  summable (λ x:ℕ, f x) :=
begin
  rcases hf with ⟨b, hb0, hb1⟩,
  obtain ⟨d, hd1, hd2⟩ := (hb1.comp_tendsto tendsto_coe_nat_at_top_at_top).exists_pos,
  rw [asymptotics.is_O_with, ←nat.cofinite_eq_at_top] at hd2,
  refine summable_of_norm_bounded_eventually _ ((summable_norm_iff.mpr _).mul_left _) hd2,
  apply summable_of_ratio_norm_eventually_le,
  swap 2,
  { apply eventually_of_forall,
    intro n, simp only [neg_mul, nat.cast_add, algebra_map.coe_one,
    real.norm_eq_abs, real.abs_exp],
   rw [add_comm, mul_add, neg_add, real.exp_add] },
  { rw real.exp_lt_one_iff, linarith },
end

end exp_decay_at_top

lemma norm_restrict_le_of_subset (f : C(ℝ, E)) {K L : compacts ℝ} (hKL : (K : set ℝ) ⊆ L) :
‖f.restrict K‖ ≤ ‖f.restrict L‖ :=
begin
  rcases eq_empty_or_nonempty (K : set ℝ) with h|h,
  { refine le_trans (le_of_eq _) (norm_nonneg _),
    exact @bounded_continuous_function.norm_eq_zero_of_empty _ _ _ _ _ (is_empty_coe_sort.mpr h), },
  simp_rw [continuous_map.norm_eq_supr_norm, ←Sup_range],
  apply cSup_le_cSup,
  { convert is_compact.bdd_above_image L.2 (continuous_norm.comp (map_continuous f)).continuous_on,
    rw ←range_restrict,
    refl },
  { rw range_nonempty_iff_nonempty, exact nonempty.coe_sort h, },
  { intro z,
    simp_rw [continuous_map.coe_restrict, ←restrict_eq, mem_range],
    rintro ⟨⟨y, hy⟩, rfl⟩,
    exact ⟨⟨y, hKL hy⟩, by refl⟩, }
end

/-- The property of having exponential decay at `-∞`. -/
def exp_decay_at_bot (f : ℝ → E) : Prop :=
∃ (b : ℝ), (0 < b) ∧ (f =O[at_bot] (λ x, real.exp (b * x)))

lemma exp_decay_at_bot_iff {f : ℝ → E} :
  exp_decay_at_bot f ↔ exp_decay_at_top (f ∘ has_neg.neg) :=
begin
  rw [exp_decay_at_bot, exp_decay_at_top],
  split,
  { rintro ⟨b, hb1, hb2⟩, refine ⟨b, hb1, _⟩,
    convert hb2.comp_tendsto tendsto_neg_at_top_at_bot,
    ext1, simp },
  { rintro ⟨b, hb1, hb2⟩, refine ⟨b, hb1, _⟩,
    convert hb2.comp_tendsto tendsto_neg_at_bot_at_top,
    ext1, simp,
    ext1, simp, },
end

namespace exp_decay_at_bot

lemma shift {f : ℝ → E} (hf : exp_decay_at_bot f) (t : ℝ) :
  exp_decay_at_bot (λ x, f (x + t)) :=
begin
  rw exp_decay_at_bot_iff at hf ⊢,
  convert hf.shift (-t) using 1,
  ext1 x, simp only [comp_app, neg_add, neg_neg],
end

lemma _root_.integrable_Iic_iff_integrable_Ioi_neg {f : ℝ → E} (a : ℝ) :
  integrable_on f (Iic a) ↔ integrable_on (f ∘ has_neg.neg) (Ioi (-a)) :=
begin
  let n : ℝ ≃ᵐ ℝ :=
  { to_fun := has_neg.neg,      inv_fun := has_neg.neg,
    left_inv := (λ x, by simp), right_inv := (λ x, by simp),
    measurable_to_fun :=  continuous_neg.measurable,
    measurable_inv_fun := continuous_neg.measurable },
  have : measure.map n volume = volume :=
    (measure.is_add_haar_measure.is_neg_invariant _).neg_eq_self,
  conv_lhs { rw [←this, n.measurable_embedding.integrable_on_map_iff] },
  have : n ⁻¹' (Iic a) = Ici (-a),
  { ext1 x,
    rw [mem_preimage, mem_Iic, mem_Ici, measurable_equiv.coe_mk, equiv.coe_fn_mk],
    exact neg_le },
  rw [this, integrable_on_Ici_iff_integrable_on_Ioi],
  refl,
end

lemma integrable_on_Iic {f : C(ℝ, E)} (hf : exp_decay_at_bot f) (a : ℝ) :
  integrable_on f (Iic a) :=
begin
  rcases hf with ⟨b, hb1, hb2⟩,
  rw integrable_Iic_iff_integrable_Ioi_neg,
  refine integrable_of_is_O_exp_neg hb1
    ((map_continuous f).comp continuous_neg).continuous_on _,
  convert hb2.comp_tendsto tendsto_neg_at_top_at_bot,
  ext1 x, simp,
end

lemma norm_Icc {f : C(ℝ, E)} (hf : exp_decay_at_bot f) (R S : ℝ) :
  exp_decay_at_bot (λ x:ℝ, ‖f.restrict (Icc (x + R) (x + S))‖) :=
begin
  rw exp_decay_at_bot_iff at hf ⊢,
  change exp_decay_at_top (f.comp (continuous_map.mk _ continuous_neg)) at hf,
  convert hf.norm_Icc (-S) (-R),
  ext1 x,
  simp only [continuous_map.norm_eq_supr_norm, continuous_map.coe_restrict, comp_app,
    continuous_map.coe_comp, continuous_map.coe_mk, ←Sup_range],
  congr' 1,
  ext1 z,
  split,
  all_goals { rintro ⟨⟨y, hy1⟩, hy2⟩, use -y,
    split, linarith [hy1.2], linarith [hy1.1],
    convert hy2 },
  simp,
end

lemma summable_neg_coe_nat [complete_space E] {f : ℝ → E} (hf : exp_decay_at_bot f) :
  summable (λ x:ℕ, f (-x)) := (exp_decay_at_bot_iff.mp hf).summable_coe_nat

end exp_decay_at_bot

/-- The property of having exponential decay at `+∞` and at `-∞`. -/
def exp_decay (f : ℝ → E) : Prop := (exp_decay_at_top f) ∧ (exp_decay_at_bot f)

namespace exp_decay

lemma integrable {f : C(ℝ, ℂ)} (hf : exp_decay f) : integrable f :=
begin
  have : Iic (0:ℝ) ∪ Ioi (0:ℝ) = univ := Iic_union_Ioi,
  rw [←integrable_on_univ, ←this, integrable_on_union],
  exact ⟨hf.2.integrable_on_Iic 0, hf.1.integrable_on_Ioi 0⟩,
end

lemma shift {f : ℝ → E} (hf : exp_decay f) (t : ℝ) : exp_decay (λ x, f (x + t)) :=
⟨hf.1.shift t, hf.2.shift t⟩

lemma trans_le  {f g : ℝ → E} (hf : exp_decay f)
  (hg : ∀ (x:ℝ), ‖g x‖ ≤ ‖f x‖) : exp_decay g :=
begin
  cases hf with hf1 hf2,
  refine ⟨hf1.trans_eventually_le (eventually_of_forall hg), _⟩,
  rw exp_decay_at_bot_iff at hf2 ⊢,
  refine hf2.trans_eventually_le (eventually_of_forall (λ x, hg (-x))),
end

lemma norm_Icc {f : C(ℝ, E)} (hf : exp_decay f) (R S : ℝ) :
  exp_decay (λ x:ℝ, ‖f.restrict (Icc (x + R) (x + S))‖) :=
⟨hf.1.norm_Icc R S, hf.2.norm_Icc R S⟩

lemma _root_.metric.bounded.subset_Icc {K : set ℝ} (hK : metric.bounded K) :
  ∃ (R S : ℝ), K ⊆ Icc R S :=
begin
  obtain ⟨r, hr⟩ := hK.subset_ball 0,
  rw real.closed_ball_eq_Icc at hr,
  exact ⟨0 - r, 0 + r, hr⟩,
end

lemma _root_.continuous_map.norm_comp_add_const_restrict_Icc (f : C(ℝ, E)) (R S t : ℝ) :
 ‖f.restrict (Icc (t + R) (t + S))‖ =
  ‖(f.comp (continuous_map.mk (λ x, x + t) (by continuity))).restrict (Icc R S)‖ :=
begin
  simp_rw [continuous_map.norm_eq_supr_norm, ←Sup_range],
  congr' 1,
  ext1 x,
  simp_rw [mem_range],
  split,
  { rintro ⟨⟨y, hy⟩, hy'⟩,
    use y - t,
    split, linarith [hy.1], linarith [hy.2],
    rw ←hy',
    simp only [continuous_map.coe_restrict, continuous_map.coe_comp,
      continuous_map.coe_mk, comp_app, subtype.coe_mk, sub_add_cancel] },
  { rintro ⟨⟨y, hy⟩, hy'⟩,
    use y + t,
    split, linarith [hy.1], linarith [hy.2],
    rw ←hy',
    simp only [continuous_map.coe_restrict, comp_app, subtype.coe_mk,
      continuous_map.coe_comp, continuous_map.coe_mk], },
end

lemma norm_compact {f : C(ℝ, E)} (hf : exp_decay f) (K : compacts ℝ) :
  exp_decay (λ t, ‖(f.comp (continuous_map.mk (λ x, x + t) (by continuity))).restrict K‖) :=
begin
  obtain ⟨R, S, hK⟩ := K.2.bounded.subset_Icc,
  apply (hf.norm_Icc R S).trans_le _,
  simp_rw [norm_norm, continuous_map.norm_comp_add_const_restrict_Icc],
  change (K : set ℝ) ⊆ compacts.mk (Icc R S) is_compact_Icc at hK,
  exact λ x, norm_restrict_le_of_subset _ hK,
end

lemma _root_.summable_int_iff [complete_space E] {g : ℤ → E} :
  summable g ↔ summable (λ n:ℕ, g n) ∧ summable (λ n:ℕ, g (-n)) :=
begin
  refine ⟨λ hg, ⟨hg.comp_injective nat.cast_injective,
    hg.comp_injective (neg_injective.comp nat.cast_injective)⟩,
      λ hg, (hg.1.has_sum.nonneg_add_neg (summable.has_sum _)).summable⟩,
  exact (@summable_nat_add_iff _ _ _ _ (λ n, g (-n)) 1).mpr hg.2,
end

lemma summable [complete_space E] {f : ℝ → E} (hf : exp_decay f) : summable (λ x:ℤ, f x) :=
summable_int_iff.mpr ⟨hf.1.summable_coe_nat, by exact_mod_cast hf.2.summable_neg_coe_nat⟩

end exp_decay -- (namespace)

theorem poisson_summation_of_exp_decay
  {f : C(ℝ, ℂ)} (hf_exp : exp_decay f)
  {g : C(ℝ, ℂ)} (hg_exp : exp_decay g)
  (hfg : ∀ t:ℝ, g t = ∫ x:ℝ, exp (-2 * π * I * t * x) * f x) :
  ∑' (n:ℤ), f n  = ∑' (n:ℤ), g n :=
poisson_summation (λ K, (hf_exp.norm_compact K).summable) hf_exp.integrable hg_exp.summable hfg

end exp_decay -- (section)


lemma integral_comp_mul (f : ℝ → ℂ) {a : ℝ} (ha : 0 ≤ a) :
  ∫ x:ℝ, f (a * x) = 1 / a * ∫ x:ℝ, f x :=
begin
  conv_lhs {congr, skip, funext, rw ←smul_eq_mul},
  rwa [measure.integral_comp_smul_of_nonneg, real_smul, one_div, complex.of_real_inv,
    finite_dimensional.finrank_self, pow_one],
end


section theta

def f (a : ℂ) : C(ℝ, ℂ) := ⟨λ x, exp (-π * a * x ^ 2),
  continuous_exp.comp (continuous_const.mul (is_R_or_C.continuous_of_real.pow 2))⟩

lemma exp_decay_f {a : ℂ} (ha : 0 < a.re) : exp_decay (f a) :=
begin
  -- reduce at_bot to at_top using symmetry
  have j := _, split, exact j,
  rw exp_decay_at_bot_iff, convert j using 1,
  { ext1 x, simp only [f, continuous_map.coe_mk, comp_app, of_real_neg, neg_sq], },
  { -- now at top
    refine ⟨1, zero_lt_one, _⟩,
    apply asymptotics.is_o.is_O,
    rw [f, continuous_map.coe_mk, ←asymptotics.is_o_norm_left],
    simp_rw [neg_one_mul],
    convert exp_neg_mul_sq_is_o_exp_neg (real.mul_pos real.pi_pos ha),
    ext1 x,
    rw [norm_eq_abs, abs_exp, ←of_real_neg, mul_comm, ←of_real_pow, of_real_mul_re,
    of_real_mul_re],
    congr' 1, ring },
end

lemma exp_decay_g {a : ℝ} (ha : 0 < a) : exp_decay
  (continuous_map.mk (λ x, (1 / a.sqrt : ℂ) * f (1 / a) x)
    (continuous_const.mul (map_continuous _))) :=
begin
  obtain ⟨⟨b, hb1, hb2⟩, ⟨b', hb1', hb2'⟩⟩ :=
    exp_decay_f (by rwa [one_div, ←of_real_inv, of_real_re, inv_pos]: 0 < (1/a : ℂ).re),
  exact ⟨⟨b, hb1, hb2.const_mul_left _⟩,  ⟨b', hb1', hb2'.const_mul_left _⟩ ⟩,
end

lemma fourier_transform_eq {a : ℝ} (ha : 0 < a) (t : ℝ)  :
  ∫ x:ℝ, exp (-2 * π * I * t * x) * f a x = 1 / a.sqrt * f (1 / a) t :=
begin
  unfold f,
  have h1 : 0 < π * a := real.mul_pos real.pi_pos ha,
  have h2 : ((real.sqrt (π * a)) : ℂ) ≠ 0 := of_real_ne_zero.mpr (real.sqrt_pos_of_pos h1).ne',
  let F : ℝ → ℂ := λ x, exp (-2 * π * I * t / real.sqrt(π * a) * x) * exp (-x ^ 2),
  have F_apply : ∀ (x : ℝ), F (real.sqrt (π * a) * x) = exp (-2 * π * I * t * x) * f a x,
  { intro x,
    dsimp only [F],
    congr' 2,
    { field_simp [h2], ring },
    { rw [of_real_mul, mul_pow, ←of_real_pow, real.sq_sqrt h1.le, of_real_mul],
      ring } },
  convert integral_comp_mul F (real.sqrt_nonneg (π * a)) using 1,
  { simp_rw F_apply, refl },
  { dsimp only [F],
    -- get rid of factor of `√a`
    rw [mul_comm π a, real.sqrt_mul ha.le, of_real_mul, ←div_div,
      div_eq_mul_one_div (1 / ((real.sqrt a) : ℂ)) _],
    conv_rhs { rw mul_assoc }, congr' 1,
    -- clear a `√π` from denominator
    field_simp [of_real_ne_zero.mpr (real.sqrt_pos_of_pos real.pi_pos).ne'],
    -- now massage into a case of `fourier_exp_negsq`
    convert (fourier_exp_negsq (-2 * π * t / real.sqrt (π * a))).symm using 3,
    { field_simp [complex.of_real_ne_zero.mpr ha.ne'],
      rw [mul_pow, mul_pow, pow_two (2:ℂ), ←of_real_pow (real.sqrt _), real.sq_sqrt h1.le,
        of_real_mul],
      ring },
    { ext1 x, congr' 2,
      have : ((real.sqrt a) : ℂ) * ((real.sqrt π) : ℂ) = ((real.sqrt (π * a)) : ℂ) :=
        by rw [←of_real_mul, of_real_inj, mul_comm, real.sqrt_mul real.pi_pos.le],
      rw this,
      field_simp, left, left, ring } },
end

lemma tsum_exp_neg_sq_eq {a : ℝ} (ha : 0 < a) :
  ∑' (n:ℤ), exp (-π * a * n ^ 2) =
  1 / real.sqrt a * ∑' (n:ℤ), exp (-π * (1 / a : ℝ) * n ^ 2) :=
begin
  convert poisson_summation_of_exp_decay
    (exp_decay_f (by rwa of_real_re : 0 < (a : ℂ).re))
    (exp_decay_g ha)
    (λ t, (fourier_transform_eq ha t).symm),
  conv_rhs { rw continuous_map.coe_mk, congr,  funext, rw ←smul_eq_mul},
  rw tsum_const_smul,
  { rw [f, continuous_map.coe_mk, smul_eq_mul],
    simp only [one_div, of_real_inv, of_real_int_cast] },
  { refine (exp_decay_f _).summable,
    simp only [one_div, inv_re, of_real_re, norm_sq_of_real, div_self_mul_self', inv_pos],
    exact ha,  },
end

end theta
