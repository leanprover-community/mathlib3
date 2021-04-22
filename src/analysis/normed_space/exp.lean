/-
Copyright (c) 2021 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import analysis.analytic.basic
import analysis.specific_limits
import data.complex.is_R_or_C

open filter is_R_or_C continuous_multilinear_map
open_locale nat topological_space

section move_me

lemma coe_factorial_add_eq_zero {α : Type*} [ring α] {n : ℕ} (h : (n! : α) = 0) :
  ∀ i, ((n+i)! : α) = 0
| 0 := by simpa using h
| (i+1) := by rw [← add_assoc, nat.factorial_succ, nat.cast_mul,
                  coe_factorial_add_eq_zero i, mul_zero]

end move_me

section exp

-- Old approach : any field...

--variables {𝕂 𝔸 : Type*} [normed_field 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

--lemma summable_pow_div_fact (x : 𝔸) : summable (λ n : ℕ, (1/n! : 𝕂) • x^n) :=
--begin
--  by_cases h : ∃ n : ℕ, (1/n! : 𝕂) • x^n = 0,
--  { rcases h with ⟨n, hn⟩,
--    refine summable_of_norm_bounded_eventually 0 summable_zero _,
--    rw [nat.cofinite_eq_at_top, eventually_at_top],
--    refine ⟨n, λ i hi, _⟩,
--    rw [pi.zero_apply, norm_le_zero_iff],
--    rcases nat.exists_eq_add_of_le hi with ⟨j, rfl⟩,
--    rcases smul_eq_zero.mp hn with h | h,
--    { simp [coe_factorial_add_eq_zero (eq_zero_of_one_div_eq_zero h)] },
--    { simp [pow_add, h] } },
--  { push_neg at h,
--    refine summable_of_ratio_test_tendsto_lt_one (le_refl _) zero_lt_one
--      (eventually_of_forall $ h) _,
--    suffices : ∀ n : ℕ, ∥x∥ / ∥((n+1) : 𝕂)∥ =
--      ∥(1 / ((n+1)! : 𝕂)) • x^(n+1)∥ / ∥(1/(n! : 𝕂)) • x^n∥,
--    { refine tendsto.congr this _, },
--     }
--ends

lemma real.summable_pow_div_fact (x : ℝ) : summable (λ n : ℕ, x^n / n!) :=
begin
  by_cases h : x = 0,
  { refine summable_of_norm_bounded_eventually 0 summable_zero _,
    rw [nat.cofinite_eq_at_top, eventually_at_top],
    use 1,
    intros n hn,
    rw [h, zero_pow (nat.succ_le_iff.mp hn), zero_div, norm_zero],
    exact le_refl _ },
  { refine summable_of_ratio_test_tendsto_lt_one (le_refl _) zero_lt_one (eventually_of_forall $
      λ n, div_ne_zero (pow_ne_zero n h) (nat.cast_ne_zero.mpr n.factorial_ne_zero)) _,
    suffices : ∀ n : ℕ, ∥x^(n+1) / (n+1)!∥ / ∥x^n / n!∥ = ∥x∥ / ∥((n+1 : ℕ) : ℝ)∥,
    { conv {congr, funext, rw [this, real.norm_coe_nat] },
      exact (tendsto_const_div_at_top_nhds_0_nat _).comp (tendsto_add_at_top_nat 1) },
    intro n,
    calc ∥x^(n+1) / (n+1)!∥ / ∥x^n / n!∥
        = (∥x∥^n * ∥x∥) * (∥(n! : ℝ)∥⁻¹ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * ((∥x∥^n)⁻¹ * ∥(n! : ℝ)∥) :
          by rw [ normed_field.norm_div, normed_field.norm_div,
                  normed_field.norm_pow, normed_field.norm_pow, pow_add, pow_one,
                  div_eq_mul_inv, div_eq_mul_inv, div_eq_mul_inv, mul_inv', inv_inv',
                  nat.factorial_succ, nat.cast_mul, normed_field.norm_mul, mul_inv_rev' ]
    ... = (∥x∥ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * (∥x∥^n * (∥x∥^n)⁻¹) * (∥(n! : ℝ)∥ * ∥(n! : ℝ)∥⁻¹) :
          by linarith --faster than ac_refl !
    ... = (∥x∥ * ∥((n+1 : ℕ) : ℝ)∥⁻¹) * 1 * 1 :
          by  rw [mul_inv_cancel (pow_ne_zero _ $ λ h', h $ norm_eq_zero.mp h'), mul_inv_cancel
                    (λ h', n.factorial_ne_zero $ nat.cast_eq_zero.mp $ norm_eq_zero.mp h')];
              apply_instance
    ... = ∥x∥ / ∥((n+1 : ℕ) : ℝ)∥ : by rw [mul_one, mul_one, ← div_eq_mul_inv] }
end

variables {𝕂 𝔸 : Type*} [is_R_or_C 𝕂] [normed_ring 𝔸] [normed_algebra 𝕂 𝔸] [complete_space 𝔸]

lemma summable_pow_div_fact (x : 𝔸) :
  summable (λ n : ℕ, (1/n! : 𝕂) • x^n) :=
begin
  refine summable_of_norm_bounded_eventually (λ (n : ℕ), ∥x∥^n / n!)
    (∥x∥).summable_pow_div_fact _,
  rw [nat.cofinite_eq_at_top, eventually_at_top],
  use 1,
  intros i hi,
  rw [norm_smul, normed_field.norm_div, norm_one, one_div, is_R_or_C.norm_eq_abs,
      abs_cast_nat, mul_comm, ← div_eq_mul_inv],
  exact div_le_div (pow_nonneg (norm_nonneg _) _) (norm_pow_le' _ hi)
    (nat.cast_pos.mpr i.factorial_pos) (le_refl _)
end

--set_option profiler true
--lemma summable_pow_div_fact (x : 𝔸) : summable (λ n : ℕ, (1/n! : 𝕂) • x^n) :=
--begin
--  have : ∀ n, (n! : 𝕂) ≠ 0 :=
--    λ n, (@nat.cast_ne_zero _ _ _ char_zero_R_or_C _).mpr n.factorial_ne_zero,
--  by_cases h : ∃ n : ℕ, x^n = 0,
--  { rcases h with ⟨n, hn⟩,
--    refine summable_of_norm_bounded_eventually 0 summable_zero _,
--    rw [nat.cofinite_eq_at_top, eventually_at_top],
--    refine ⟨n, λ i hi, _⟩,
--    rw [pi.zero_apply, norm_le_zero_iff],
--    rcases nat.exists_eq_add_of_le hi with ⟨j, rfl⟩,
--    simp [pow_add, hn] },
--  { push_neg at h,
--    refine summable_of_ratio_test_tendsto_lt_one (le_refl _) zero_lt_one
--      (eventually_of_forall $ λ n, smul_ne_zero.mpr ⟨one_div_ne_zero $ this n, h n⟩) _,
--    suffices : ∀ n : ℕ, ∥(1 / ((n+1)! : 𝕂)) • x^(n+1)∥ / ∥(1/(n! : 𝕂)) • x^n∥
--      ≤ ∥x∥ / ∥((n+1 : ℕ) : 𝕂)∥,
--    { refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds _
--        (λ n, div_nonneg (norm_nonneg _) (norm_nonneg _)) this,
--      conv { congr, funext, rw [norm_eq_abs, abs_of_nat] },
--      exact (tendsto_const_div_at_top_nhds_0_nat _).comp (tendsto_add_at_top_nat 1) },
--    intro n,
--    calc ∥(1 / ((n+1)! : 𝕂)) • x^(n+1)∥ / ∥(1/(n! : 𝕂)) • x^n∥
--        = ∥((n+1 : ℕ) : 𝕂)∥⁻¹ * ∥(n! : 𝕂)∥⁻¹ * ∥x^(n+1)∥ * (∥(n! : 𝕂)∥ * ∥x^n∥⁻¹) :
--          by simp only [norm_smul, div_eq_mul_inv, mul_inv', inv_inv', one_mul,
--                        normed_field.norm_mul, nat.cast_succ, nat.factorial_succ,
--                        nat.cast_mul, normed_field.norm_inv]
--    ... = (∥(n! : 𝕂)∥ * ∥(n! : 𝕂)∥⁻¹) * (∥x^(n+1)∥ * (∥x^n∥⁻¹ * ∥((n+1 : ℕ) : 𝕂)∥⁻¹)) :
--          by linarith --faster than ac_refl !
--    ... = ∥x ^ (n + 1)∥ * (∥x ^ n∥⁻¹ * ∥((n+1 : ℕ) : 𝕂)∥⁻¹) :
--          by rw [mul_inv_cancel (norm_pos_iff.mpr $ this n).ne.symm, one_mul]
--    ... = ∥x * x ^ n∥ * (∥x ^ n∥⁻¹ * ∥((n+1 : ℕ) : 𝕂)∥⁻¹) :
--          by rw [add_comm, pow_add, pow_one]
--    ... ≤ (∥x∥ * ∥x ^ n∥) * (∥x ^ n∥⁻¹ * ∥((n+1 : ℕ) : 𝕂)∥⁻¹) :
--          mul_le_mul (norm_mul_le _ _) (le_refl _)
--            (mul_nonneg (inv_nonneg.mpr $ norm_nonneg _) (inv_nonneg.mpr $ norm_nonneg _))
--            (mul_nonneg (norm_nonneg _) (norm_nonneg _))
--    ... = ∥x∥ * (∥x ^ n∥ * ∥x ^ n∥⁻¹) * ∥((n+1 : ℕ) : 𝕂)∥⁻¹ :
--          by linarith
--    ... = ∥x∥ * ∥((n+1 : ℕ) : 𝕂)∥⁻¹ :
--          by rw [mul_inv_cancel (norm_pos_iff.mpr $ h n).ne.symm, mul_one]
--    ... = ∥x∥ / ∥↑(n + 1)∥ : by rw [mul_comm, div_eq_inv_mul]
--  }
--end

variables (𝕂 𝔸)

def exp_series : formal_multilinear_series 𝕂 𝔸 𝔸 :=
  λ n, (1/n! : 𝕂) • continuous_multilinear_map.mk_pi_algebra_fin 𝕂 n 𝔸

noncomputable def exp (x : 𝔸) : 𝔸 := (exp_series 𝕂 𝔸).sum x

variables {𝕂 𝔸}

lemma exp_radius_eq_top : (exp_series 𝕂 𝔸).radius = ⊤ :=
begin
  sorry
end

end exp
