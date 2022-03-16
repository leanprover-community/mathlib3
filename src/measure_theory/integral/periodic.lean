/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import measure_theory.group.fundamental_domain
import measure_theory.integral.interval_integral
import topology.algebra.floor_ring

/-!
# Integrals of periodic functions

In this file we prove that `∫ x in t..t + T, f x = ∫ x in s..s + T, f x` for any (not necessarily
measurable) function periodic function with period `T`.
-/

open set function measure_theory measure_theory.measure topological_space
open_locale measure_theory

lemma is_add_fundamental_domain_Ioc {T : ℝ} (hT : 0 < T) (t : ℝ) (μ : measure ℝ . volume_tac) :
  is_add_fundamental_domain (add_subgroup.zmultiples T) (Ioc t (t + T)) μ :=
begin
  refine is_add_fundamental_domain.mk' measurable_set_Ioc (λ x, _),
  have : bijective (cod_restrict (λ n : ℤ, n • T) (add_subgroup.zmultiples T) _),
    from (equiv.of_injective (λ n : ℤ, n • T) (zsmul_strict_mono_left hT).injective).bijective,
  refine this.exists_unique_iff.2 _,
  simpa only [add_comm x] using exists_unique_add_zsmul_mem_Ioc hT x t
end

variables {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [complete_space E] [second_countable_topology E]

namespace function

namespace periodic

open interval_integral

variables {f : ℝ → E} {T : ℝ}

/-- An auxiliary lemma for a more general `function.periodic.interval_integral_add_eq`. -/
lemma interval_integral_add_eq_of_pos (hf : periodic f T)
  (hT : 0 < T) (t s : ℝ) : ∫ x in t..t + T, f x = ∫ x in s..s + T, f x :=
begin
  haveI : encodable (add_subgroup.zmultiples T) := (countable_range _).to_encodable,
  simp only [integral_of_le, hT.le, le_add_iff_nonneg_right],
  haveI : vadd_invariant_measure (add_subgroup.zmultiples T) ℝ volume :=
    ⟨λ c s hs, measure_preimage_add _ _ _⟩,
  exact (is_add_fundamental_domain_Ioc hT t).set_integral_eq
    (is_add_fundamental_domain_Ioc hT s) hf.map_vadd_zmultiples
end

/-- If `f` is a periodic function with period `T`, then its integral over `[t, t + T]` does not
depend on `t`. -/
lemma interval_integral_add_eq (hf : periodic f T)
  (t s : ℝ) : ∫ x in t..t + T, f x = ∫ x in s..s + T, f x :=
begin
  rcases lt_trichotomy 0 T with (hT|rfl|hT),
  { exact hf.interval_integral_add_eq_of_pos hT t s },
  { simp },
  { rw [← neg_inj, ← integral_symm, ← integral_symm],
    simpa only [← sub_eq_add_neg, add_sub_cancel]
      using (hf.neg.interval_integral_add_eq_of_pos (neg_pos.2 hT) (t + T) (s + T)) }
end

/-- If `f` is an integrable periodic function with period `T`, then its integral over `[t, s + T]`
is the sum of its integrals over the intervals `[t, s]` and `[t, t + T]`. -/
lemma interval_integral_add_eq_add (hf : periodic f T) (t s : ℝ)
  (h_int : ∀ t₁ t₂, interval_integrable f measure_space.volume t₁ t₂) :
  ∫ x in t..s+T, f x = (∫ x in t..s, f x) + ∫ x in t..t + T, f x :=
by rw [hf.interval_integral_add_eq t s, integral_add_adjacent_intervals (h_int t s) (h_int s _)]

/-- If `f` is an integrable periodic function with period `T`, and `n` is an integer, then its
integral over `[t, t + n • T]` is `n` times its integral over `[t, t + T]`. -/
lemma interval_integral_add_zsmul_eq (hf : periodic f T) (n : ℤ) (t : ℝ)
  (h_int : ∀ t₁ t₂, interval_integrable f measure_space.volume t₁ t₂) :
  ∫ x in t..t + n • T, f x = n • ∫ x in t..t + T, f x :=
begin
  -- Reduce to the case `b = 0`
  suffices : ∫ x in 0..n • T, f x = n • ∫ x in 0..T, f x,
  { simp only [hf.interval_integral_add_eq t 0, (hf.zsmul n).interval_integral_add_eq t 0, zero_add,
      this], },
  -- First prove it for natural numbers
  have : ∀ (m : ℕ), ∫ x in 0..m • T, f x = m • ∫ x in 0..T, f x,
  { intros,
    induction m with m ih,
    { simp, },
    { simp only [succ_nsmul', hf.interval_integral_add_eq_add 0 (m • T) h_int, ih, zero_add], }, },
  -- Then prove it for all integers
  cases n with n n,
  { simp [← this n], },
  { conv_rhs { rw zsmul_neg_succ_of_nat, },
    have h₀ : (int.neg_succ_of_nat n) • T + (n + 1) • T = 0, { simp, linarith, },
    rw [integral_symm, ← (hf.nsmul (n+1)).funext, neg_inj],
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n+1),
      add_comm T, hf.interval_integral_add_eq ((n+1) • T) 0, zero_add], },
end

section real_valued

open filter

variables {g : ℝ → ℝ}
variables (hg : periodic g T) (h_int : ∀ t₁ t₂, interval_integrable g measure_space.volume t₁ t₂)
include hg h_int

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded below by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
lemma Inf_add_zsmul_le_integral_of_pos (hT : 0 < T) (t : ℝ) :
  Inf ((λ t, ∫ x in 0..t, g x) '' (Icc 0 T)) + ⌊t/T⌋ • (∫ x in 0..T, g x) ≤ ∫ x in 0..t, g x :=
begin
  let ε := int.fract (t/T) * T,
  conv_rhs { rw [← int.fract_div_mul_self_add_zsmul_eq T t (by linarith),
    ← integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)] },
  rw [hg.interval_integral_add_zsmul_eq ⌊t/T⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_add,
    add_le_add_iff_right],
  exact (continuous_primitive h_int 0).continuous_on.Inf_image_Icc_le
    (mem_Icc_of_Ico (int.fract_div_mul_self_mem_Ico T t hT)),
end

/-- If `g : ℝ → ℝ` is periodic with period `T > 0`, then for any `t : ℝ`, the function
`t ↦ ∫ x in 0..t, g x` is bounded above by `t ↦ X + ⌊t/T⌋ • Y` for appropriate constants `X` and
`Y`. -/
lemma integral_le_Sup_add_zsmul_of_pos (hT : 0 < T) (t : ℝ) :
  ∫ x in 0..t, g x ≤ Sup ((λ t, ∫ x in 0..t, g x) '' (Icc 0 T)) + ⌊t/T⌋ • (∫ x in 0..T, g x) :=
begin
  let ε := int.fract (t/T) * T,
  conv_lhs { rw [← int.fract_div_mul_self_add_zsmul_eq T t (by linarith),
    ← integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)] },
  rw [hg.interval_integral_add_zsmul_eq ⌊t/T⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_add,
    add_le_add_iff_right],
  exact (continuous_primitive h_int 0).continuous_on.le_Sup_image_Icc
    (mem_Icc_of_Ico (int.fract_div_mul_self_mem_Ico T t hT)),
end

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `∞` as `t` tends to `∞`. -/
lemma tendsto_at_top_interval_integral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) :
  tendsto (λ t, ∫ x in 0..t, g x) at_top at_top :=
begin
  apply tendsto_at_top_mono (hg.Inf_add_zsmul_le_integral_of_pos h_int hT),
  apply at_top.tendsto_at_top_add_const_left (Inf $ (λ t, ∫ x in 0..t, g x) '' (Icc 0 T)),
  apply tendsto.at_top_zsmul_const h₀,
  exact tendsto_floor_at_top.comp (tendsto_id.at_top_mul_const (inv_pos.mpr hT)),
end

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `0 < ∫ x in 0..T, g x`, then
`t ↦ ∫ x in 0..t, g x` tends to `-∞` as `t` tends to `-∞`. -/
lemma tendsto_at_bot_interval_integral_of_pos (h₀ : 0 < ∫ x in 0..T, g x) (hT : 0 < T) :
  tendsto (λ t, ∫ x in 0..t, g x) at_bot at_bot :=
begin
  apply tendsto_at_bot_mono (hg.integral_le_Sup_add_zsmul_of_pos h_int hT),
  apply at_bot.tendsto_at_bot_add_const_left (Sup $ (λ t, ∫ x in 0..t, g x) '' (Icc 0 T)),
  apply tendsto.at_bot_zsmul_const h₀,
  exact tendsto_floor_at_bot.comp (tendsto_id.at_bot_mul_const (inv_pos.mpr hT)),
end

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `∞` as `t` tends to `∞`. -/
lemma tendsto_at_top_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
  tendsto (λ t, ∫ x in 0..t, g x) at_top at_top :=
hg.tendsto_at_top_interval_integral_of_pos h_int (interval_integral_pos_of_pos (h_int 0 T) h₀ hT) hT

/-- If `g : ℝ → ℝ` is periodic with period `T > 0` and `∀ x, 0 < g x`, then `t ↦ ∫ x in 0..t, g x`
tends to `-∞` as `t` tends to `-∞`. -/
lemma tendsto_at_bot_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (hT : 0 < T) :
  tendsto (λ t, ∫ x in 0..t, g x) at_bot at_bot :=
hg.tendsto_at_bot_interval_integral_of_pos h_int (interval_integral_pos_of_pos (h_int 0 T) h₀ hT) hT

end real_valued

end periodic

end function
