/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.asymptotics
import analysis.asymptotics.specific_asymptotics
import data.polynomial.eval

/-!
# Negligible Functions

This file defines a predicate `negligible f` on functions `f` from `ℕ` to a normed field.

The main theorem is `negligible_polynomial_mul` that says the product of a polynomial
  and a negligible function is still a negligible function
-/

namespace asymptotics

/-- Definition of negligible functions over an arbitrary `normed_field`.
  Note that the second function always has type `ℕ → ℝ`, which generally gives better lemmas. -/
def negligible {𝕜 : Type*} [normed_field 𝕜]
  (f : ℕ → 𝕜) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) filter.at_top

variables {𝕜 : Type*} [normed_field 𝕜]
variables {f g : ℕ → 𝕜}

lemma negligible_of_is_O (hg : negligible g)
  (h : is_O f g filter.at_top) : negligible f :=
λ c, h.trans $ hg c

lemma negligible_of_eventually_le (hg : negligible g)
  (h : ∀ᶠ n in filter.at_top, ∥f n∥ ≤ ∥g n∥) : negligible f :=
negligible_of_is_O hg $ is_O_iff.2 ⟨1, by simpa only [one_mul] using h⟩

/-- It suffices to check the negligiblity condition for only sufficiently small exponents `c`.
  See `negligible_of_is_O_fpow_le` for a version with explicit bounds -/
lemma negligible_of_eventually_is_O
  (h : ∀ᶠ (c : ℤ) in filter.at_bot, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
begin
  obtain ⟨C, hC⟩ := filter.eventually_at_bot.mp h,
  intro c,
  by_cases hc : c ≤ C,
  { exact hC c hc },
  { refine (hC C le_rfl).trans (is_O.of_bound 1 (filter.eventually_at_top.2 ⟨1, (λ b hb, _)⟩)),
    simp_rw [one_mul, normed_field.norm_fpow, real.norm_coe_nat],
    have hb : 1 ≤ (b : ℝ) := le_trans (le_of_eq nat.cast_one.symm) (nat.cast_le.2 hb),
    exact fpow_le_of_le hb (le_of_not_le hc) }
end

lemma negligible_of_is_O_fpow_le (C : ℤ)
  (h : ∀ c ≤ C, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
negligible_of_eventually_is_O (filter.eventually_at_bot.2 ⟨C, h⟩)

lemma negligible_of_is_O_fpow_lt (C : ℤ)
  (h : ∀ c < C, is_O f (λ n, (n : ℝ) ^ c) filter.at_top) :
  negligible f :=
negligible_of_is_O_fpow_le C.pred
  (λ c hc, h c (lt_of_le_of_lt hc (int.pred_self_lt C)))

lemma tendsto_zero_of_negligible (hf : negligible f) :
  filter.tendsto f filter.at_top (nhds 0) :=
begin
  refine is_O.trans_tendsto (hf (-1)) _,
  have : (λ (n : ℕ), (n : ℝ) ^ (-1 : ℤ)) = (has_inv.inv : ℝ → ℝ) ∘ (coe : ℕ → ℝ),
  by simp only [gpow_one, fpow_neg],
  rw this,
  refine filter.tendsto.comp (tendsto_inv_at_top_zero) (nat_coe_tendsto_at_top ℝ),
end

lemma norm_eventually_le_of_negligible
  (hf : negligible f) (x₀ : ℝ) (hx₀ : 0 < x₀) :
  ∀ᶠ (n : ℕ) in filter.at_top, ∥f n∥ ≤ x₀ :=
begin
  obtain ⟨c, hc⟩ := is_O_iff.1 (hf (-1)),
  have : ∀ᶠ (n : ℕ) in filter.at_top, c * ∥(n : ℝ) ^ (-1 : ℤ)∥ ≤ x₀,
  { obtain ⟨a, ha⟩ := exists_nat_ge (c * x₀⁻¹),
    refine filter.eventually_at_top.2 ⟨max a 1, λ b hb, _⟩,
    have hb0 : 0 < (b : ℝ) := nat.cast_pos.2 (le_trans (le_max_right a 1) hb),
    have hba : (a : ℝ) ≤ (b : ℝ) := nat.cast_le.2 (le_trans (le_max_left a 1) hb),
    rw [fpow_neg, gpow_one, normed_field.norm_inv, real.norm_coe_nat,
      mul_inv_le_iff hb0, mul_comm _ x₀],
    calc c ≤ x₀ * (a : ℝ) : (mul_inv_le_iff hx₀).1 ha
      ... ≤ x₀ * (b : ℝ) : mul_le_mul le_rfl hba (nat.cast_nonneg a) (le_of_lt hx₀) },
  refine filter.eventually.mp hc (filter.eventually.mono this (λ x hx hx', le_trans hx' hx)),
end

@[simp]
lemma negligible_zero : negligible (function.const ℕ (0 : 𝕜)) :=
λ c, is_O_zero _ _

lemma negligible_add (hf : negligible f) (hg : negligible g) :
  negligible (f + g) :=
λ c, is_O.add (hf c) (hg c)

lemma negligible_mul (hf : negligible f) (hg : negligible g) :
  negligible (f * g) :=
begin
  suffices : is_O (f * g) f filter.at_top,
  from λ c, this.trans (hf c),
  refine is_O.of_bound 1 ((norm_eventually_le_of_negligible hg 1 (zero_lt_one)).mono (λ x hx, _)),
  rw [pi.mul_apply, normed_field.norm_mul, mul_comm 1 ∥f x∥],
  exact mul_le_mul le_rfl hx (norm_nonneg $ g x) (norm_nonneg $ f x),
end

@[simp]
lemma negligible_const_iff [t1_space 𝕜] (x : 𝕜) :
  negligible (function.const ℕ x) ↔ x = 0 :=
begin
  refine ⟨λ h, not_not.1 (λ hx, _), λ h, h.symm ▸ negligible_zero⟩,
  have : (function.const ℕ x ⁻¹' {x}ᶜ) ∈ filter.at_top :=
    (tendsto_nhds.1 $ tendsto_zero_of_negligible h) {x}ᶜ (is_open_ne) (ne.symm hx),
  rw [set.preimage_const_of_not_mem (by simp : x ∉ ({x} : set 𝕜)ᶜ)] at this,
  exact filter.at_top.empty_not_mem this,
end

lemma negligible_const_mul (hf : negligible f) (c : 𝕜) :
  negligible (λ n, c * f n) :=
(negligible_of_is_O hf (is_O_const_mul_self c f filter.at_top))

@[simp]
lemma negligible_const_mul_iff (f : ℕ → 𝕜) (c : 𝕜) :
  negligible (λ n, c * f n) ↔ (c = 0) ∨ (negligible f) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { by_cases hc : c = 0,
    { exact or.inl hc },
    { exact or.inr (negligible_of_is_O h (is_O_self_const_mul c hc f filter.at_top)) } },
  { cases h,
    { simp only [h, zero_mul, negligible_const_iff] },
    { exact negligible_const_mul h c } }
end

-- TODO: The lemmas below can be generalized to `iff` statements if `∥(n : 𝕜)∥` doesn't tend to 0

lemma negligible_coe_nat_mul (hf : negligible f) :
  negligible (λ n, (n : 𝕜) * f n) :=
begin
  refine negligible_of_is_O_fpow_lt 0 (λ c hc, _),
  refine is_O.trans (is_O.mul (coe_nat_is_O_coe_nat_real 𝕜) (hf (c - 1)))
    (is_O_of_le _ (λ x, le_of_eq (congr_arg _ _))),
  by_cases hx : (x : ℝ) = 0,
  { simp_rw [hx, zero_mul],
    refine symm (zero_fpow c (ne_of_lt hc)) },
  { calc (x : ℝ) * ↑x ^ (c - 1) = (↑x ^ (1 : ℤ)) * (↑x ^ (c - 1)) : by rw gpow_one
      ... = ↑x ^ (1 + (c - 1)) : (fpow_add hx 1 (c - 1)).symm
      ... = ↑x ^ c : congr_arg (λ g, gpow g (x : ℝ)) (by linarith) }
end

lemma negligible_coe_nat_pow_mul (hf : negligible f) (p : ℕ) :
  negligible (λ n, (n : 𝕜) ^ p * f n) :=
begin
  induction p with p hp,
  { simp_rw [pow_zero, one_mul],
    exact hf },
  { simp_rw [pow_succ, mul_assoc],
    exact negligible_coe_nat_mul hp }
end

lemma negligible_nsmul (hf : negligible f) :
  negligible (λ n, n • f n) :=
by simpa [nsmul_eq_mul] using negligible_coe_nat_mul hf

lemma negligible_pow_nsmul (hf : negligible f) (p : ℕ) :
  negligible (λ n, (n ^ p) • f n) :=
by simpa [nsmul_eq_mul] using negligible_coe_nat_pow_mul hf p

theorem negligible_polynomial_mul {𝕜 : Type*} [normed_field 𝕜]
  {f : ℕ → 𝕜} (hf : negligible f) (p : polynomial 𝕜) :
  negligible (λ n, (p.eval n) * f n) :=
begin
  refine polynomial.induction_on' p (λ p q hp hq, _) (λ m x, _),
  { simp_rw [polynomial.eval_add, add_mul],
    exact negligible_add hp hq },
  { simp_rw [polynomial.eval_monomial, mul_assoc],
    exact negligible_const_mul (negligible_coe_nat_pow_mul hf m) x }
end

end asymptotics
