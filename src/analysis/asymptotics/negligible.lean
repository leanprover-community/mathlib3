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

-/

namespace asymptotics

open_locale topological_space
open filter

/-- A function `f` from an `ordered_comm_semiring` to a `normed_field` is negligible
  iff `f(x)` is `O(x ^ c)` for all integers `c`. -/
def negligible {α 𝕜 : Type*} [ordered_comm_semiring α] [normed_field 𝕜] [algebra α 𝕜]
  (f : α → 𝕜) :=
∀ (c : ℤ), is_O f (λ x, (algebra_map α 𝕜 x) ^ c) filter.at_top

section normed_field

variables {α 𝕜 : Type*} [ordered_comm_semiring α] [normed_field 𝕜] [algebra α 𝕜]
variables {f g : α → 𝕜}

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

@[simp]
lemma negligible_zero : negligible (0 : α → 𝕜) :=
λ c, is_O_zero _ _

@[simp]
lemma negligible_zero' : negligible (λ (x : α), (0 : 𝕜)) :=
negligible_zero

lemma negligible.add (hf : negligible f) (hg : negligible g) :
  negligible (f + g) :=
λ c, is_O.add (hf c) (hg c)

lemma negligible.const_mul (hf : negligible f) (c : 𝕜) :
  negligible (λ n, c * f n) :=
(is_O_const_mul_self c f at_top).trans_negligible hf

lemma negligible.mul_const (hf : negligible f) (c : 𝕜) :
  negligible (λ n, f n * c) :=
by simpa [mul_comm _ c] using negligible.const_mul hf c

lemma negligible_const_mul_iff_of_ne_zero {c : 𝕜} (hc : c ≠ 0) :
  negligible (λ n, c * f n) ↔ negligible f :=
⟨λ h, (is_O_self_const_mul c hc f at_top).trans_negligible h, λ h, h.const_mul c ⟩

lemma negligible_mul_const_iff_of_ne_zero {c : 𝕜} (hc : c ≠ 0) :
  negligible (λ n, f n * c) ↔ negligible f :=
by simpa [mul_comm _ c] using negligible_const_mul_iff_of_ne_zero hc

@[simp]
lemma negligible_const_mul_iff (c : 𝕜) :
  negligible (λ n, c * f n) ↔ c = 0 ∨ negligible f :=
begin
  by_cases hc0 : c = 0,
  { simp [hc0] },
  { exact (negligible_const_mul_iff_of_ne_zero hc0).trans
      ⟨or.inr, or.rec (λ hc0', absurd hc0' hc0) id⟩ }
end

@[simp]
lemma negligible_mul_const_iff (c : 𝕜) :
  negligible (λ n, f n * c) ↔ c = 0 ∨ negligible f :=
by simp [mul_comm _ c]

section no_zero_smul_divisors

variables [nontrivial α] [no_zero_smul_divisors α 𝕜]

lemma negligible.coe_nat_mul (hf : negligible f) :
  negligible (λ n, (algebra_map α 𝕜 n) * f n) :=
begin
  refine λ c, (is_O.mul (is_O_refl (algebra_map α 𝕜) at_top) (hf (c - 1))).trans _,
  refine is_O_of_div_tendsto_nhds (eventually_of_forall
    (λ x hx, mul_eq_zero_of_left (fpow_eq_zero hx) _)) 1 (tendsto_nhds.2 _),
  refine λ s hs hs', at_top.sets_of_superset (mem_at_top 1) (λ x hx, set.mem_preimage.2 _),
  have hx' : algebra_map α 𝕜 x ≠ 0 := λ hx', (ne_of_lt $ lt_of_lt_of_le zero_lt_one hx).symm
    (by simpa [algebra.algebra_map_eq_smul_one, smul_eq_zero] using hx'),
  convert hs',
  rw [pi.div_apply, div_eq_one_iff_eq (fpow_ne_zero c hx'), fpow_sub_one hx' c,
    mul_comm (algebra_map α 𝕜 x), mul_assoc, inv_mul_cancel hx', mul_one],
end

lemma negligible.coe_nat_pow_mul (hf : negligible f) (p : ℕ) :
  negligible (λ n, (algebra_map α 𝕜 n) ^ p * f n) :=
begin
  induction p with p hp,
  { simp_rw [pow_zero, one_mul],
    exact hf },
  { simp_rw [pow_succ, mul_assoc],
    exact hp.coe_nat_mul }
end

theorem negligible.polynomial_mul (hf : negligible f) (p : polynomial 𝕜) :
  negligible (λ n, (p.eval (algebra_map α 𝕜 n)) * f n) :=
begin
  refine polynomial.induction_on' p (λ p q hp hq, _) (λ m x, _),
  { simp_rw [polynomial.eval_add, add_mul],
    exact hp.add hq },
  { simp_rw [polynomial.eval_monomial, mul_assoc],
    exact (hf.coe_nat_pow_mul m).const_mul x }
end

/-- If `f` is negligible, and `g` is `O(p)` for some polynomial `p`, then `f * g` is negligible -/
lemma negligible.mul_is_O_polynomial (hf : negligible f) (p : polynomial 𝕜)
  (hg : is_O g (λ n, p.eval (algebra_map α 𝕜 n)) filter.at_top) : negligible (f * g) :=
(is_O.mul (is_O_refl f at_top) hg).trans_negligible
  ((hf.polynomial_mul p).mono $ λ x, le_of_eq (congr_arg _ $ mul_comm _ _))

/-- If `f` is negligible, and `g` is `O(n ^ c)` for some integer `c`, then `f * g` is negligible-/
lemma negligible.mul_is_O (hf : negligible f) (c : ℕ)
  (hg : is_O g (λ n, (algebra_map α 𝕜 n) ^ c) at_top) : negligible (f * g) :=
(is_O.mul (is_O_refl f at_top) hg).trans_negligible
  ((hf.coe_nat_pow_mul c).mono $ λ x, le_of_eq (congr_arg _ $ mul_comm _ _))

lemma negligible.mul (hf : negligible f) (hg : negligible g) :
  negligible (f * g) :=
hf.mul_is_O 0 (by simpa using hg 0)

end no_zero_smul_divisors

end normed_field

section normed_linear_ordered_field

variables {α 𝕜 : Type*} [ordered_comm_semiring α] [normed_linear_ordered_field 𝕜] [algebra α 𝕜]
variables {f g : α → 𝕜}

/-- It suffices to check the negligiblity condition for only sufficiently small exponents `c`,
  assuing algebra_map eventually has norm at least `1` -/
lemma negligible_of_eventually_is_O (hα : ∀ᶠ (x : α) in at_top, 1 ≤ ∥algebra_map α 𝕜 x∥)
  (h : ∀ᶠ (c : ℤ) in at_bot, is_O f (λ x, (algebra_map α 𝕜 x) ^ c) at_top) :
  negligible f :=
begin
  obtain ⟨C, hC⟩ := eventually_at_bot.mp h,
  intro c,
  by_cases hc : c ≤ C,
  { exact hC c hc },
  { refine (hC C le_rfl).trans (is_O.of_bound 1 (_)),
    refine at_top.sets_of_superset hα (λ x hx, _),
    simp only [one_mul, normed_field.norm_fpow, set.mem_set_of_eq],
    refine fpow_le_of_le hx (le_of_not_le hc) }
end

lemma negligible_of_is_O_fpow_le (hα : ∀ᶠ (x : α) in at_top, 1 ≤ ∥algebra_map α 𝕜 x∥)
  (C : ℤ) (h : ∀ c ≤ C, is_O f (λ n, (algebra_map α 𝕜 n) ^ c) at_top) :
  negligible f :=
negligible_of_eventually_is_O hα (eventually_at_bot.2 ⟨C, h⟩)

lemma negligible_of_is_O_fpow_lt (hα : ∀ᶠ (x : α) in at_top, 1 ≤ ∥algebra_map α 𝕜 x∥)
  (C : ℤ) (h : ∀ c < C, is_O f (λ n, (algebra_map α 𝕜 n) ^ c) at_top) :
  negligible f :=
negligible_of_is_O_fpow_le hα C.pred
  (λ c hc, h c (lt_of_le_of_lt hc (int.pred_self_lt C)))

section order_topology

variable [order_topology 𝕜]

/-- A negligible function must tend to zero in the base ring (not just in norm),
  assuming `algebra_map α 𝕜` tends to `at_top` -/
lemma negligible.tendsto_zero (hα : tendsto (algebra_map α 𝕜) at_top at_top)
  (hf : negligible f) : tendsto f at_top (𝓝 0) :=
begin
  refine is_O.trans_tendsto (hf (-1)) _,
  have : (has_inv.inv : 𝕜 → 𝕜) ∘ (algebra_map α 𝕜 : α → 𝕜) = (λ (n : α), (algebra_map α 𝕜 n) ^ (-1 : ℤ)),
  by simp only [gpow_one, fpow_neg],
  refine this ▸ (tendsto_inv_at_top_zero).comp (hα),
end

/-- A negligible function eventually has norm less than any positive bound,
  assuming the algebra map tendsto to `at_top` -/
lemma negligible.eventually_le (hα : tendsto (algebra_map α 𝕜) at_top at_top)
  (hf : negligible f) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ (n : α) in at_top, ∥f n∥ ≤ ε :=
by simpa only [dist_zero_right] using
  (hf.tendsto_zero hα).eventually (metric.closed_ball_mem_nhds (0 : 𝕜) hε)

@[simp]
lemma negligible_const_iff [(at_top : filter α).ne_bot]
  (hα : tendsto (algebra_map α 𝕜) at_top at_top)
  (x : 𝕜) : negligible (function.const α x) ↔ x = 0 :=
begin
  refine ⟨λ h, not_not.1 (λ hx, _), λ h, by simp [h]⟩,
  have : (function.const α x ⁻¹' {x}ᶜ) ∈ at_top :=
    (tendsto_nhds.1 $ h.tendsto_zero hα) {x}ᶜ (is_open_ne) (ne.symm hx),
  rw [set.preimage_const_of_not_mem (by simp : x ∉ ({x} : set 𝕜)ᶜ)] at this,
  exact at_top.empty_not_mem this,
end

end order_topology

end normed_linear_ordered_field

end asymptotics
