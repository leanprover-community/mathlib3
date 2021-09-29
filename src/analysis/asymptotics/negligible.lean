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

This file defines a predicate `negligible f` for a function satisfying
  one of following equivalent definitions (The definition is in terms of the first condition):

* `f` is `O(x ^ c)` for all (or equivalently sufficiently small) integers `c`
* `f` is `O(p(x)⁻¹)` for all (or equivalently sufficiently large) polynomials `p`
* `p(x) * f` is bounded for all polynomials `p`
* `p(x) * f` tends to `𝓝 0` for all polynomials `p`

The main theorem is `negligible_polynomial_mul` that says the product of a polynomial
  and a negligible function is still a negligible function.
-/

namespace asymptotics

open_locale topological_space
open filter

/-- Definition of negligible functions over an arbitrary `normed_field`.
  Note that the second function always has type `ℕ → ℝ`, which generally gives better lemmas. -/
def negligible {𝕜 : Type*} [has_norm 𝕜] (f : ℕ → 𝕜) :=
∀ (c : ℤ), is_O f (λ n, (n : ℝ) ^ c) at_top

lemma negligible.ext {𝕜 : Type*} [has_norm 𝕜] {f g : ℕ → 𝕜}
  (hf : negligible f) (h : ∀ x, f x = g x) : negligible g :=
(funext h : f = g) ▸ hf

section normed_group

variables {R : Type*} [normed_group R]
variables {f g : ℕ → R}

lemma is_O.trans_negligible (h : is_O f g at_top)
  (hg : negligible g) : negligible f :=
λ c, h.trans $ hg c

alias is_O.trans_negligible ← negligible.is_O_mono

lemma negligible.mono (hf : negligible f)
  (h : ∀ n, ∥g n∥ ≤ ∥f n∥) : negligible g :=
(is_O_of_le at_top h).trans_negligible hf

lemma negligible.eventually_mono (hf : negligible f)
  (h : ∀ᶠ n in at_top, ∥g n∥ ≤ ∥f n∥) : negligible g :=
(is_O_iff.2 ⟨1, by simpa only [one_mul] using h⟩).trans_negligible hf

/-- It suffices to check the negligiblity condition for only sufficiently small exponents `c`.
  See `negligible_of_is_O_fpow_le` for a version with explicit bounds -/
lemma negligible_of_eventually_is_O (h : ∀ᶠ (c : ℤ) in at_bot, is_O f (λ n, (n : ℝ) ^ c) at_top) :
  negligible f :=
begin
  obtain ⟨C, hC⟩ := eventually_at_bot.mp h,
  intro c,
  by_cases hc : c ≤ C,
  { exact hC c hc },
  { refine (hC C le_rfl).trans (is_O.of_bound 1 (eventually_at_top.2 ⟨1, (λ b hb, _)⟩)),
    simp_rw [one_mul, normed_field.norm_fpow, real.norm_coe_nat],
    have hb : 1 ≤ (b : ℝ) := le_trans (le_of_eq nat.cast_one.symm) (nat.cast_le.2 hb),
    exact fpow_le_of_le hb (le_of_not_le hc) }
end

lemma negligible_of_is_O_fpow_le (C : ℤ)
  (h : ∀ c ≤ C, is_O f (λ n, (n : ℝ) ^ c) at_top) :
  negligible f :=
negligible_of_eventually_is_O (eventually_at_bot.2 ⟨C, h⟩)

lemma negligible_of_is_O_fpow_lt (C : ℤ)
  (h : ∀ c < C, is_O f (λ n, (n : ℝ) ^ c) at_top) :
  negligible f :=
negligible_of_is_O_fpow_le C.pred
  (λ c hc, h c (lt_of_le_of_lt hc (int.pred_self_lt C)))

/-- A negligible function must tend to zero in the base ring (not just in norm) -/
lemma negligible.tendsto_zero (hf : negligible f) :
  tendsto f at_top (𝓝 0) :=
begin
  refine is_O.trans_tendsto (hf (-1)) _,
  have : (has_inv.inv : ℝ → ℝ) ∘ (coe : ℕ → ℝ) = (λ (n : ℕ), (n : ℝ) ^ (-1 : ℤ)),
  by simp only [gpow_one, fpow_neg],
  exact this ▸ (tendsto_inv_at_top_zero).comp (coe_nat_tendsto_at_top ℝ),
end

/-- A negligible function eventually has norm less than any positive bound -/
lemma negligible.eventually_le (hf : negligible f) (ε : ℝ) (hε : 0 < ε) :
  ∀ᶠ (n : ℕ) in at_top, ∥f n∥ ≤ ε :=
by simpa only [dist_zero_right] using
  hf.tendsto_zero.eventually (metric.closed_ball_mem_nhds (0 : R) hε)

@[simp]
lemma negligible_zero : negligible (0 : ℕ → R) :=
λ c, is_O_zero _ _

lemma negligible.add (hf : negligible f) (hg : negligible g) :
  negligible (f + g) :=
λ c, is_O.add (hf c) (hg c)

@[simp]
lemma negligible_const_iff [t1_space R] (x : R) :
  negligible (function.const ℕ x) ↔ x = 0 :=
begin
  refine ⟨λ h, not_not.1 (λ hx, _), λ h, by simp [h]⟩,
  have : (function.const ℕ x ⁻¹' {x}ᶜ) ∈ at_top :=
    (tendsto_nhds.1 $ h.tendsto_zero) {x}ᶜ (is_open_ne) (ne.symm hx),
  rw [set.preimage_const_of_not_mem (by simp : x ∉ ({x} : set R)ᶜ)] at this,
  exact at_top.empty_not_mem this,
end

end normed_group

section normed_ring

variables {R : Type*} [normed_ring R]
variables {f g : ℕ → R}

lemma negligible.const_mul (hf : negligible f) (c : R) :
  negligible (λ n, c * f n) :=
(is_O_const_mul_self c f at_top).trans_negligible hf

lemma negligible_const_mul_iff_of_is_unit {c : R} (hc : is_unit c) :
  negligible (λ n, c * f n) ↔ (negligible f) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { exact (is_O_self_const_mul' hc f at_top).trans_negligible h },
  { exact h.const_mul c },
end

end normed_ring

section normed_field

variables {𝕜 : Type*} [normed_field 𝕜]
variables {f g : ℕ → 𝕜}

@[simp]
lemma negligible_const_mul_iff (f : ℕ → 𝕜) (c : 𝕜) :
  negligible (λ n, c * f n) ↔ (c = 0) ∨ (negligible f) :=
begin
  by_cases hc0 : c = 0,
  { simp [hc0] },
  { exact (negligible_const_mul_iff_of_is_unit (is_unit.mk0 c hc0)).trans
      ⟨or.inr, or.rec (λ hc0', absurd hc0' hc0) id⟩ }
end

-- TODO: The lemmas below can be generalized to `iff` statements if `∥(n : 𝕜)∥` doesn't tend to 0

lemma negligible.coe_nat_mul (hf : negligible f) :
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

lemma negligible.coe_nat_pow_mul (hf : negligible f) (p : ℕ) :
  negligible (λ n, (n : 𝕜) ^ p * f n) :=
begin
  induction p with p hp,
  { simp_rw [pow_zero, one_mul],
    exact hf },
  { simp_rw [pow_succ, mul_assoc],
    exact hp.coe_nat_mul }
end

lemma negligible.nsmul (hf : negligible f) :
  negligible (λ n, n • f n) :=
by simpa [nsmul_eq_mul] using hf.coe_nat_mul

lemma negligible.pow_nsmul (hf : negligible f) (p : ℕ) :
  negligible (λ n, (n ^ p) • f n) :=
by simpa [nsmul_eq_mul] using hf.coe_nat_pow_mul p

theorem negligible.polynomial_mul {𝕜 : Type*} [normed_field 𝕜]
  {f : ℕ → 𝕜} (hf : negligible f) (p : polynomial 𝕜) :
  negligible (λ n, (p.eval n) * f n) :=
begin
  refine polynomial.induction_on' p (λ p q hp hq, _) (λ m x, _),
  { simp_rw [polynomial.eval_add, add_mul],
    exact hp.add hq },
  { simp_rw [polynomial.eval_monomial, mul_assoc],
    exact (hf.coe_nat_pow_mul m).const_mul x }
end

lemma negligible.mul_is_O_polynomial (hf : negligible f) (p : polynomial 𝕜)
  (hg : is_O g (λ n, p.eval n) filter.at_top) : negligible (f * g) :=
(is_O.mul (is_O_refl f at_top) hg).trans_negligible
  ((hf.polynomial_mul p).ext $ λ x, mul_comm _ _)

lemma negligible.mul_is_O (hf : negligible f) (c : ℕ)
  (hg : is_O g (λ n, (n : 𝕜) ^ c) at_top) : negligible (f * g) :=
(is_O.mul (is_O_refl f at_top) hg).trans_negligible
  ((hf.coe_nat_pow_mul c).ext $ λ x, mul_comm _ _)

lemma negligible.mul (hf : negligible f) (hg : negligible g) :
  negligible (f * g) :=
begin
  refine hf.mul_is_O 0 (is_O_of_div_tendsto_nhds (by simp) 0 _),
  convert hg.tendsto_zero,
  exact funext (λ x, by simp),
end

end normed_field

end asymptotics
