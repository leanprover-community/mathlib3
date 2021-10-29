/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.asymptotics
import analysis.asymptotics.specific_asymptotics
import data.polynomial.eval

/-!
# Super-Polynomial Function Decay

This file defines a predicate `asymptotics.superpolynomial_decay f` for a function satisfying
  one of following equivalent definitions (The definition is in terms of the first condition):

* `f` is `O(x ^ c)` for all (or sufficiently small) integers `c`
* `x ^ c * f` is bounded for all (or sufficiently large) integers `c`
* `x ^ c * f` tends to `𝓝 0` for all (or sufficiently large) integers `c`
* `f` is `o(x ^ c)` for all (or sufficiently small) integers `c`

The equivalence between the first two is given by in `superpolynomial_decay_iff_is_bounded_under`.
The equivalence between the first and third is given in `superpolynomial_decay_iff_tendsto_zero`.
The equivalence between the first and fourth is given in `superpolynomial_decay_iff_is_o`.

These conditions are all equivalent to conditions in terms of polynomials, replacing `x ^ c` with
  `p(x)` or `p(x)⁻¹` as appropriate, since asymptotically `p(x)` behaves like `X ^ p.nat_degree`.
These further equivalences are not proven in mathlib but would be good future projects.

The definition of superpolynomial decay for a function `f : α → 𝕜`
  is made relative to an algebra structure `[algebra α 𝕜]`.
Super-polynomial decay then means the function `f x` decays faster than
  `(p.eval (algebra_map α 𝕜 x))⁻¹` for all polynomials `p : polynomial 𝕜`.

When the algebra structure is given by `n ↦ ↑n : ℕ → ℝ` this defines negligible functions:
https://en.wikipedia.org/wiki/Negligible_function

When the algebra structure is given by `(r₁,...,rₙ) ↦ r₁*...*rₙ : ℝⁿ → ℝ` this is equivalent
  to the definition of rapidly decreasing functions given here:
https://ncatlab.org/nlab/show/rapidly+decreasing+function

# Main Theorems

* `superpolynomial_decay.polynomial_mul` says that if `f(x)` is negligible,
    then so is `p(x) * f(x)` for any polynomial `p`.
* `superpolynomial_decay_iff_is_bounded_under` says that `f` is negligible iff
    `p(x) * f(x)` has bounded norm for all polynomials `p(x)`.
* `superpolynomial_decay_of_eventually_is_O` says that it suffices to check `f(x)` is `O(x ^ c)`
    for only sufficiently small `c`, rather than all integers `c`.
-/

namespace asymptotics

open_locale topological_space
open filter

/-- A function `f` from an `ordered_comm_semiring` to a `normed_field` has superpolynomial decay
  iff `f(x)` is `O(x ^ c)` for all integers `c`. -/
def superpolynomial_decay {α 𝕜 : Type*} [ordered_comm_semiring α] [normed_field 𝕜] [algebra α 𝕜]
  (f : α → 𝕜) :=
∀ (c : ℤ), is_O f (λ x, (algebra_map α 𝕜 x) ^ c) filter.at_top

section normed_field

variables {α 𝕜 : Type*} [ordered_comm_semiring α] [normed_field 𝕜] [algebra α 𝕜]
variables {f g : α → 𝕜}

theorem superpolynomial_decay_iff_is_bounded_under (f : α → 𝕜)
  (hα : ∀ᶠ (x : α) in at_top, (algebra_map α 𝕜 x) ≠ 0) :
  superpolynomial_decay f ↔
    ∀ (c : ℤ), is_bounded_under has_le.le at_top (λ x, ∥f x * (algebra_map α 𝕜 x) ^ c∥) :=
begin
  split; intros h c; specialize h (-c),
  { simpa [div_eq_mul_inv] using div_is_bounded_under_of_is_O h },
  { refine (is_O_iff_div_is_bounded_under _).2 _,
    { exact hα.mono (λ x hx hx', absurd (zpow_eq_zero hx') hx) },
    { simpa [div_eq_mul_inv] using h } }
end

theorem superpolynomial_decay_iff_is_o (f : α → 𝕜)
  (hα : tendsto (λ x, ∥algebra_map α 𝕜 x∥) at_top at_top) :
  superpolynomial_decay f ↔
    ∀ (c : ℤ), is_o f (λ x, (algebra_map α 𝕜 x) ^ c) at_top :=
begin
  refine ⟨λ h c, _, λ h c, (h c).is_O⟩,
  have hα' : ∀ᶠ (x : α) in at_top, (algebra_map α 𝕜 x) ≠ 0,
  from (eventually_ne_of_tendsto_norm_at_top hα 0).mono (λ x hx hx', absurd hx' hx),
  have : is_o (λ x, 1 : α → 𝕜) (λ x, (algebra_map α 𝕜 x)) at_top,
  { refine is_o_of_tendsto' (hα'.mono $ λ x hx hx', absurd hx' hx)
      (tendsto_zero_iff_norm_tendsto_zero.2 _),
    simp only [one_div, normed_field.norm_inv],
    exact tendsto.comp tendsto_inv_at_top_zero hα },
  have := this.mul_is_O (h $ c - 1),
  simp only [one_mul] at this,
  refine this.trans_is_O (is_O.of_bound 1 (hα'.mono (λ x hx, le_of_eq _))),
  rw [zpow_sub_one₀ hx, mul_comm, mul_assoc, inv_mul_cancel hx, one_mul, mul_one]
end

theorem superpolynomial_decay_iff_norm_tendsto_zero (f : α → 𝕜)
  (hα : tendsto (λ x, ∥algebra_map α 𝕜 x∥) at_top at_top) :
  superpolynomial_decay f ↔
    ∀ (c : ℤ), tendsto (λ x, ∥f x * (algebra_map α 𝕜 x) ^ c∥) at_top (𝓝 0) :=
begin
  refine ⟨λ h c, _, λ h, _⟩,
  { refine tendsto_zero_iff_norm_tendsto_zero.1 _,
    rw (superpolynomial_decay_iff_is_o f hα) at h,
    simpa [div_eq_mul_inv] using (h $ -c).tendsto_0 },
  { have hα' : ∀ᶠ (x : α) in at_top, (algebra_map α 𝕜 x) ≠ 0,
    from (eventually_ne_of_tendsto_norm_at_top hα 0).mono (λ x hx hx', absurd hx' hx),
    exact (superpolynomial_decay_iff_is_bounded_under f hα').2
      (λ c, is_bounded_under_of_tendsto (tendsto_zero_iff_norm_tendsto_zero.2 $ h c)) }
end

lemma superpolynomial_decay_iff_tendsto_zero (f : α → 𝕜)
  (hα : tendsto (λ x, ∥algebra_map α 𝕜 x∥) at_top at_top) :
  superpolynomial_decay f ↔
    ∀ (c : ℤ), tendsto (λ x, f x * (algebra_map α 𝕜 x) ^ c) at_top (𝓝 0) :=
(superpolynomial_decay_iff_norm_tendsto_zero f hα).trans
  (by simp [tendsto_zero_iff_norm_tendsto_zero])

lemma is_O.trans_superpolynomial_decay (h : is_O f g at_top)
  (hg : superpolynomial_decay g) : superpolynomial_decay f :=
λ c, h.trans $ hg c

alias is_O.trans_superpolynomial_decay ← superpolynomial_decay.is_O_mono

lemma superpolynomial_decay.mono (hf : superpolynomial_decay f)
  (h : ∀ n, ∥g n∥ ≤ ∥f n∥) : superpolynomial_decay g :=
(is_O_of_le at_top h).trans_superpolynomial_decay hf

lemma superpolynomial_decay.eventually_mono (hf : superpolynomial_decay f)
  (h : ∀ᶠ n in at_top, ∥g n∥ ≤ ∥f n∥) : superpolynomial_decay g :=
(is_O_iff.2 ⟨1, by simpa only [one_mul] using h⟩).trans_superpolynomial_decay hf

@[simp]
lemma superpolynomial_decay_zero : superpolynomial_decay (0 : α → 𝕜) :=
λ c, is_O_zero _ _

@[simp]
lemma superpolynomial_decay_zero' : superpolynomial_decay (λ (x : α), (0 : 𝕜)) :=
superpolynomial_decay_zero

lemma superpolynomial_decay.add (hf : superpolynomial_decay f) (hg : superpolynomial_decay g) :
  superpolynomial_decay (f + g) :=
λ c, is_O.add (hf c) (hg c)

lemma superpolynomial_decay.const_mul (hf : superpolynomial_decay f) (c : 𝕜) :
  superpolynomial_decay (λ n, c * f n) :=
(is_O_const_mul_self c f at_top).trans_superpolynomial_decay hf

lemma superpolynomial_decay.mul_const (hf : superpolynomial_decay f) (c : 𝕜) :
  superpolynomial_decay (λ n, f n * c) :=
by simpa [mul_comm _ c] using superpolynomial_decay.const_mul hf c

lemma superpolynomial_decay_const_mul_iff_of_ne_zero {c : 𝕜} (hc : c ≠ 0) :
  superpolynomial_decay (λ n, c * f n) ↔ superpolynomial_decay f :=
⟨λ h, (is_O_self_const_mul c hc f at_top).trans_superpolynomial_decay h, λ h, h.const_mul c ⟩

lemma superpolynomial_decay_mul_const_iff_of_ne_zero {c : 𝕜} (hc : c ≠ 0) :
  superpolynomial_decay (λ n, f n * c) ↔ superpolynomial_decay f :=
by simpa [mul_comm _ c] using superpolynomial_decay_const_mul_iff_of_ne_zero hc

@[simp]
lemma superpolynomial_decay_const_mul_iff (c : 𝕜) :
  superpolynomial_decay (λ n, c * f n) ↔ c = 0 ∨ superpolynomial_decay f :=
begin
  by_cases hc0 : c = 0,
  { simp [hc0] },
  { exact (superpolynomial_decay_const_mul_iff_of_ne_zero hc0).trans
      ⟨or.inr, or.rec (λ hc0', absurd hc0' hc0) id⟩ }
end

@[simp]
lemma superpolynomial_decay_mul_const_iff (c : 𝕜) :
  superpolynomial_decay (λ n, f n * c) ↔ c = 0 ∨ superpolynomial_decay f :=
by simp [mul_comm _ c]

section no_zero_smul_divisors

variables [no_zero_smul_divisors α 𝕜]

lemma superpolynomial_decay.algebra_map_mul (hf : superpolynomial_decay f) :
  superpolynomial_decay (λ n, (algebra_map α 𝕜 n) * f n) :=
begin
  haveI : nontrivial α := (algebra_map α 𝕜).domain_nontrivial,
  refine λ c, (is_O.mul (is_O_refl (algebra_map α 𝕜) at_top) (hf (c - 1))).trans _,
  refine is_O_of_div_tendsto_nhds (eventually_of_forall
    (λ x hx, mul_eq_zero_of_left (zpow_eq_zero hx) _)) 1 (tendsto_nhds.2 _),
  refine λ s hs hs', at_top.sets_of_superset (mem_at_top 1) (λ x hx, set.mem_preimage.2 _),
  have hx' : algebra_map α 𝕜 x ≠ 0 := λ hx', (ne_of_lt $ lt_of_lt_of_le zero_lt_one hx).symm
    (by simpa [algebra.algebra_map_eq_smul_one, smul_eq_zero] using hx'),
  convert hs',
  rw [pi.div_apply, div_eq_one_iff_eq (zpow_ne_zero c hx'), zpow_sub_one₀ hx' c,
    mul_comm (algebra_map α 𝕜 x), mul_assoc, inv_mul_cancel hx', mul_one],
end

lemma superpolynomial_decay.algebra_map_pow_mul (hf : superpolynomial_decay f) (p : ℕ) :
  superpolynomial_decay (λ n, (algebra_map α 𝕜 n) ^ p * f n) :=
begin
  induction p with p hp,
  { simp_rw [pow_zero, one_mul],
    exact hf },
  { simp_rw [pow_succ, mul_assoc],
    exact hp.algebra_map_mul }
end

theorem superpolynomial_decay.polynomial_mul (hf : superpolynomial_decay f) (p : polynomial 𝕜) :
  superpolynomial_decay (λ n, (p.eval (algebra_map α 𝕜 n)) * f n) :=
begin
  refine polynomial.induction_on' p (λ p q hp hq, _) (λ m x, _),
  { simp_rw [polynomial.eval_add, add_mul],
    exact hp.add hq },
  { simp_rw [polynomial.eval_monomial, mul_assoc],
    exact (hf.algebra_map_pow_mul m).const_mul x }
end

/-- If `f` has superpolynomial decay, and `g` is `O(p)` for some polynomial `p`,
  then `f * g` has superpolynomial decay -/
lemma superpolynomial_decay.mul_is_O_polynomial (hf : superpolynomial_decay f) (p : polynomial 𝕜)
  (hg : is_O g (λ n, p.eval (algebra_map α 𝕜 n)) filter.at_top) : superpolynomial_decay (f * g) :=
(is_O.mul (is_O_refl f at_top) hg).trans_superpolynomial_decay
  ((hf.polynomial_mul p).mono $ λ x, le_of_eq (congr_arg _ $ mul_comm _ _))

/-- If `f` has superpolynomial decay, and `g` is `O(n ^ c)` for some integer `c`,
  then `f * g` has has superpolynomial decay-/
lemma superpolynomial_decay.mul_is_O (hf : superpolynomial_decay f) (c : ℕ)
  (hg : is_O g (λ n, (algebra_map α 𝕜 n) ^ c) at_top) : superpolynomial_decay (f * g) :=
(is_O.mul (is_O_refl f at_top) hg).trans_superpolynomial_decay
  ((hf.algebra_map_pow_mul c).mono $ λ x, le_of_eq (congr_arg _ $ mul_comm _ _))

lemma superpolynomial_decay.mul (hf : superpolynomial_decay f) (hg : superpolynomial_decay g) :
  superpolynomial_decay (f * g) :=
hf.mul_is_O 0 (by simpa using hg 0)

end no_zero_smul_divisors

end normed_field

section normed_linear_ordered_field

variables {α 𝕜 : Type*} [ordered_comm_semiring α] [normed_linear_ordered_field 𝕜] [algebra α 𝕜]
variables {f g : α → 𝕜}

/-- It suffices to check the decay condition for only sufficiently small exponents `c`,
  assuing algebra_map eventually has norm at least `1` -/
lemma superpolynomial_decay_of_eventually_is_O (hα : ∀ᶠ (x : α) in at_top, 1 ≤ ∥algebra_map α 𝕜 x∥)
  (h : ∀ᶠ (c : ℤ) in at_bot, is_O f (λ x, (algebra_map α 𝕜 x) ^ c) at_top) :
  superpolynomial_decay f :=
begin
  obtain ⟨C, hC⟩ := eventually_at_bot.mp h,
  intro c,
  by_cases hc : c ≤ C,
  { exact hC c hc },
  { refine (hC C le_rfl).trans (is_O.of_bound 1 (_)),
    refine at_top.sets_of_superset hα (λ x hx, _),
    simp only [one_mul, normed_field.norm_zpow, set.mem_set_of_eq],
    exact zpow_le_of_le hx (le_of_not_le hc) }
end

lemma superpolynomial_decay_of_is_O_zpow_le (hα : ∀ᶠ (x : α) in at_top, 1 ≤ ∥algebra_map α 𝕜 x∥)
  (C : ℤ) (h : ∀ c ≤ C, is_O f (λ n, (algebra_map α 𝕜 n) ^ c) at_top) :
  superpolynomial_decay f :=
superpolynomial_decay_of_eventually_is_O hα (eventually_at_bot.2 ⟨C, h⟩)

lemma superpolynomial_decay_of_is_O_zpow_lt (hα : ∀ᶠ (x : α) in at_top, 1 ≤ ∥algebra_map α 𝕜 x∥)
  (C : ℤ) (h : ∀ c < C, is_O f (λ n, (algebra_map α 𝕜 n) ^ c) at_top) :
  superpolynomial_decay f :=
superpolynomial_decay_of_is_O_zpow_le hα C.pred
  (λ c hc, h c (lt_of_le_of_lt hc (int.pred_self_lt C)))

section order_topology

variable [order_topology 𝕜]

/-- A function with superpolynomial decay must tend to zero in the base ring (not just in norm),
  assuming `algebra_map α 𝕜` tends to `at_top` -/
lemma superpolynomial_decay.tendsto_zero (hα : tendsto (algebra_map α 𝕜) at_top at_top)
  (hf : superpolynomial_decay f) : tendsto f at_top (𝓝 0) :=
begin
  refine is_O.trans_tendsto (hf (-1)) _,
  have : (has_inv.inv : 𝕜 → 𝕜) ∘ (algebra_map α 𝕜 : α → 𝕜)
    = (λ (n : α), (algebra_map α 𝕜 n) ^ (-1 : ℤ)),
  by simp only [zpow_one, zpow_neg₀],
  exact this ▸ (tendsto_inv_at_top_zero).comp (hα)
end

/-- A function with superpolynomial decay eventually has norm less than any positive bound,
  assuming the algebra map tendsto to `at_top` -/
lemma superpolynomial_decay.eventually_le (hα : tendsto (algebra_map α 𝕜) at_top at_top)
  (hf : superpolynomial_decay f) (ε : ℝ) (hε : 0 < ε) : ∀ᶠ (n : α) in at_top, ∥f n∥ ≤ ε :=
by simpa only [dist_zero_right] using
  (hf.tendsto_zero hα).eventually (metric.closed_ball_mem_nhds (0 : 𝕜) hε)

lemma superpolynomial_decay_const_iff [(at_top : filter α).ne_bot]
  (hα : tendsto (algebra_map α 𝕜) at_top at_top)
  (x : 𝕜) : superpolynomial_decay (function.const α x) ↔ x = 0 :=
begin
  refine ⟨λ h, not_not.1 (λ hx, _), λ h, by simp [h]⟩,
  have : (function.const α x ⁻¹' {x}ᶜ) ∈ at_top :=
    (tendsto_nhds.1 $ h.tendsto_zero hα) {x}ᶜ (is_open_ne) (ne.symm hx),
  rw [set.preimage_const_of_not_mem (by simp : x ∉ ({x} : set 𝕜)ᶜ)] at this,
  exact at_top.empty_not_mem this
end

end order_topology

end normed_linear_ordered_field

end asymptotics
