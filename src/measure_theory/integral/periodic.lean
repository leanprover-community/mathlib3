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

In this file we prove that `∫ x in b..b + a, f x = ∫ x in c..c + a, f x` for any (not necessarily
measurable) function periodic function with period `a`.
-/

open set function measure_theory measure_theory.measure topological_space
open_locale measure_theory

lemma is_add_fundamental_domain_Ioc {a : ℝ} (ha : 0 < a) (b : ℝ) (μ : measure ℝ . volume_tac) :
  is_add_fundamental_domain (add_subgroup.zmultiples a) (Ioc b (b + a)) μ :=
begin
  refine is_add_fundamental_domain.mk' measurable_set_Ioc (λ x, _),
  have : bijective (cod_restrict (λ n : ℤ, n • a) (add_subgroup.zmultiples a) _),
    from (equiv.of_injective (λ n : ℤ, n • a) (zsmul_strict_mono_left ha).injective).bijective,
  refine this.exists_unique_iff.2 _,
  simpa only [add_comm x] using exists_unique_add_zsmul_mem_Ioc ha x b
end

variables {E : Type*} [normed_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [complete_space E] [second_countable_topology E]

namespace function

namespace periodic

open interval_integral

variables {f : ℝ → E} {a : ℝ}

/-- An auxiliary lemma for a more general `function.periodic.interval_integral_add_eq`. -/
lemma interval_integral_add_eq_of_pos (hf : periodic f a)
  (ha : 0 < a) (b c : ℝ) : ∫ x in b..b + a, f x = ∫ x in c..c + a, f x :=
begin
  haveI : encodable (add_subgroup.zmultiples a) := (countable_range _).to_encodable,
  simp only [integral_of_le, ha.le, le_add_iff_nonneg_right],
  haveI : vadd_invariant_measure (add_subgroup.zmultiples a) ℝ volume :=
    ⟨λ c s hs, measure_preimage_add _ _ _⟩,
  exact (is_add_fundamental_domain_Ioc ha b).set_integral_eq
    (is_add_fundamental_domain_Ioc ha c) hf.map_vadd_zmultiples
end

/-- If `f` is a periodic function with period `a`, then its integral over `[b, b + a]` does not
depend on `b`. -/
lemma interval_integral_add_eq (hf : periodic f a)
  (b c : ℝ) : ∫ x in b..b + a, f x = ∫ x in c..c + a, f x :=
begin
  rcases lt_trichotomy 0 a with (ha|rfl|ha),
  { exact hf.interval_integral_add_eq_of_pos ha b c },
  { simp },
  { rw [← neg_inj, ← integral_symm, ← integral_symm],
    simpa only [← sub_eq_add_neg, add_sub_cancel]
      using (hf.neg.interval_integral_add_eq_of_pos (neg_pos.2 ha) (b + a) (c + a)) }
end

/-- If `f` is an integrable periodic function with period `a`, then its integral over `[b, c + a]`
is the sum of its integrals over the intervals `[b, c]` and `[b, b + a]`. -/
lemma interval_integral_add_eq_add (hf : periodic f a) (b c : ℝ)
  (h_int : ∀ t₁ t₂, interval_integrable f measure_space.volume t₁ t₂) :
  ∫ x in b..c+a, f x = (∫ x in b..c, f x) + ∫ x in b..b + a, f x :=
by rw [hf.interval_integral_add_eq b c, integral_add_adjacent_intervals (h_int b c) (h_int c _)]

/-- If `f` is an integrable periodic function with period `a`, and `n` is an integer, then its
integral over `[b, b + n • a]` is `n` times its integral over `[b, b + a]`. -/
@[simp] lemma interval_integral_add_zsmul_eq (hf : periodic f a) (n : ℤ) (b : ℝ)
  (h_int : ∀ t₁ t₂, interval_integrable f measure_space.volume t₁ t₂) :
  ∫ x in b..b + n • a, f x = n • ∫ x in b..b + a, f x :=
begin
  -- Reduce to the case `b = 0`
  suffices : ∫ x in 0..n • a, f x = n • ∫ x in 0..a, f x,
  { simp only [hf.interval_integral_add_eq b 0, (hf.zsmul n).interval_integral_add_eq b 0, zero_add,
      this], },
  -- First prove it for natural numbers
  have : ∀ (m : ℕ), ∫ x in 0..m • a, f x = m • ∫ x in 0..a, f x,
  { intros,
    induction m with m ih,
    { simp, },
    { simp only [succ_nsmul', hf.interval_integral_add_eq_add 0 (m • a) h_int, ih, zero_add], }, },
  -- Then prove it for all integers
  cases n with n n,
  { simp [← this n], },
  { conv_rhs { rw zsmul_neg_succ_of_nat, },
    have h₀ : (int.neg_succ_of_nat n) • a + (n + 1) • a = 0, { simp, linarith, },
    rw [integral_symm, ← (hf.nsmul (n+1)).funext, neg_inj],
    simp_rw [integral_comp_add_right, h₀, zero_add, this (n+1),
      add_comm a, hf.interval_integral_add_eq ((n+1) • a) 0, zero_add], },
end

section real_valued

open filter

variables {g : ℝ → ℝ}
variables (hg : periodic g a) (h_int : ∀ t₁ t₂, interval_integrable g measure_space.volume t₁ t₂)
include hg h_int

/-- If `g : ℝ → ℝ` is periodic with period `a > 0` and `0 < ∫ x in 0..a, g x`, then for any `b : ℝ`,
`∫ x in 0..b, g x` is bounded below by `X + ⌊b/a⌋ • Y` for appropriate constants `X` and `Y`. -/
lemma Inf_add_zsmul_le_integral_of_pos (ha : 0 < a) (h₀ : 0 < ∫ x in 0..a, g x) (b : ℝ) :
  Inf ((λ t, ∫ x in 0..t, g x) '' (Icc 0 a)) + ⌊b/a⌋ • (∫ x in 0..a, g x) ≤ ∫ x in 0..b, g x :=
begin
  let ε := int.fract (b/a) * a,
  conv_rhs { rw [← int.fract_div_mul_self_add_zsmul_eq a b (by linarith),
    ← integral_add_adjacent_intervals (h_int 0 ε) (h_int _ _)] },
  rw [hg.interval_integral_add_zsmul_eq ⌊b/a⌋ ε h_int, hg.interval_integral_add_eq ε 0, zero_add,
    add_le_add_iff_right],
  exact (continuous_primitive h_int 0).continuous_on.Inf_image_Icc_le
    (int.fract_div_mul_self_mem_Icc a b ha),
end

/-- If `g : ℝ → ℝ` is periodic with period `a > 0` and `0 < ∫ x in 0..a, g x`, then
`∫ x in 0..b, g x` tends to `∞` as `b` tends to `∞`. -/
lemma tendsto_at_top_interval_integral_of_pos (h₀ : 0 < ∫ x in 0..a, g x) (ha : 0 < a) :
  tendsto (λ b, ∫ x in 0..b, g x) at_top at_top :=
begin
  apply tendsto_at_top_mono (hg.Inf_add_zsmul_le_integral_of_pos h_int ha h₀),
  apply at_top.tendsto_at_top_add_const_left (Inf $ (λ t, ∫ x in 0..t, g x) '' (Icc 0 a)),
  apply tendsto.at_top_zsmul_const h₀,
  exact tendsto_floor_at_top.comp (tendsto_id.at_top_mul_const (inv_pos.mpr ha)),
end

/-- If `g : ℝ → ℝ` is periodic with period `a > 0` and `∀ x, 0 < g x`, then `∫ x in 0..b, g x` tends
to `∞` as `b` tends to `∞`. -/
lemma tendsto_at_top_interval_integral_of_pos' (h₀ : ∀ x, 0 < g x) (ha : 0 < a) :
  tendsto (λ b, ∫ x in 0..b, g x) at_top at_top :=
begin
  suffices : 0 < ∫ x in 0..a, g x,
  { exact hg.tendsto_at_top_interval_integral_of_pos h_int this ha, },
  have hg₀ : support g = univ := eq_univ_iff_forall.mpr (λ t, (h₀ t).ne.symm),
  replace h₀ : 0 ≤ᵐ[volume] g := eventually_of_forall (λ x, (h₀ x).le),
  rw interval_integral.integral_pos_iff_support_of_nonneg_ae h₀ (h_int 0 a),
  exact ⟨ha, by simp [hg₀, ha]⟩,
end

end real_valued

end periodic

end function
