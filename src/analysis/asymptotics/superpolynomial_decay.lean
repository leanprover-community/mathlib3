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

TODO: Update all of this

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

/-- `f` has superpolynomial decay in parameter `k` along filter `l` if
  `k ^ z * f` tends to zero for all integers `z`
  TODO: Try to get this working with `group_with_zero 𝕜` -/
def superpolynomial_decay {α 𝕜 : Type*} [group_with_zero 𝕜] [topological_space 𝕜]
  (l : filter α) (k : α → 𝕜) (f : α → 𝕜) :=
∀ (n : ℕ), tendsto (λ (a : α), (k a) ^ n * f a) l (𝓝 0)

section equivalent_definitions

variables {α 𝕜 : Type*} [normed_linear_ordered_field 𝕜] {l : filter α} {k : α → 𝕜}
variables {f g : α → 𝕜}

-- TODO: move this somewhere else
lemma tendsto_zero_iff_abs_tendsto_zero {α β : Type*} [topological_space β] [linear_ordered_field β]
  [order_topology β] {l : filter α} (f : α → β) :
  tendsto f l (𝓝 0) ↔ tendsto (abs ∘ f) l (𝓝 0) :=
begin
  refine ⟨λ h, (abs_zero : |(0 : β)| = 0) ▸ h.abs, λ h, _⟩,
  have : tendsto (λ a, -|f a|) l (𝓝 0) := (neg_zero : -(0 : β) = 0) ▸ h.neg,
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le this h
    (λ x, neg_abs_le_self $ f x) (λ x, le_abs_self $ f x),
end

-- TODO: Move this somewhere else
lemma eventually_ne_of_tendsto_at_top {α β : Type*} [ordered_semiring β] [nontrivial β]
  {l : filter α} {f : α → β} (hf : tendsto f l at_top)
  (c : β) :  ∀ᶠ x in l, f x ≠ c :=
(tendsto_at_top.1 hf $ (c + 1)).mono (λ x hx, ne_of_gt (lt_of_lt_of_le (lt_add_one c) hx))

-- TODO: move this
lemma fpow_neg_succ_mul_fpow_self_eq_inv {α : Type*} [group_with_zero α]
  (x : α) (z : ℤ) :
  x ^ -(z + 1) * x ^ z = x⁻¹ :=
begin
  by_cases hka : x = 0,
  { simp only [hka, inv_zero, neg_add_rev, mul_eq_zero],
    by_cases hz : z = 0,
    { simp [hz] },
    { refine or.inr (zero_fpow z hz) } },
  { rw [fpow_neg, fpow_add_one hka, mul_inv_rev₀, mul_assoc,
      inv_mul_cancel (fpow_ne_zero z hka), mul_one] }
end

section tendsto_ish

lemma superpolynomial_decay_iff_norm_tendsto_zero :
  superpolynomial_decay l k f ↔
    ∀ (n : ℕ), tendsto (λ (a : α), ∥(k a) ^ n * f a∥) l (𝓝 0) :=
⟨λ h z, tendsto_zero_iff_norm_tendsto_zero.1 (h z),
  λ h z, tendsto_zero_iff_norm_tendsto_zero.2 (h z)⟩

lemma superpolynomial_decay_iff_abs_tendsto_zero [order_topology 𝕜] :
  superpolynomial_decay l k f ↔
    ∀ (n : ℕ), tendsto (λ (a : α), |(k a) ^ n * f a|) l (𝓝 0) :=
⟨λ h z, (tendsto_zero_iff_abs_tendsto_zero _).1 (h z),
  λ h z, (tendsto_zero_iff_abs_tendsto_zero _).2 (h z)⟩

lemma superpolynomial_decay_iff_abs_is_bounded_under [order_topology 𝕜] (hk : tendsto k l at_top) :
  superpolynomial_decay l k f ↔
    ∀ (z : ℕ), is_bounded_under (≤) l (λ (a : α), |(k a) ^ z * f a|) :=
begin
  refine ⟨λ h z, (h z).abs.is_bounded_under_le,
    λ h, superpolynomial_decay_iff_abs_tendsto_zero.2 (λ z, _)⟩,
  obtain ⟨m, hm⟩ := h (z + 1),
  have h1 : tendsto (λ (a : α), (0 : 𝕜)) l (𝓝 0) := tendsto_const_nhds,
  have h2 : tendsto (λ (a : α), |(k a)⁻¹| * m) l (𝓝 0) := (zero_mul m) ▸ tendsto.mul_const m
    ((tendsto_zero_iff_abs_tendsto_zero _).1 hk.inv_tendsto_at_top),
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' h1 h2
    (eventually_of_forall (λ x, abs_nonneg _)) ((eventually_map.1 hm).mp _),
  refine ((eventually_ne_of_tendsto_at_top hk 0).mono $ λ x hk0 hx, _),
  refine le_trans (le_of_eq _) (mul_le_mul_of_nonneg_left hx $ abs_nonneg (k x)⁻¹),
  rw [← abs_mul, ← mul_assoc, pow_succ, ← mul_assoc, inv_mul_cancel hk0, one_mul],
end

end tendsto_ish

section all_integers


lemma superpolynomial_decay_iff_fpow_tendsto_zero {α 𝕜 : Type*}
  [linear_ordered_field 𝕜] [topological_space 𝕜] [order_topology 𝕜]
  {l : filter α} {k : α → 𝕜} (f : α → 𝕜) (hk : tendsto k l at_top):
  superpolynomial_decay l k f ↔
    ∀ (z : ℤ), tendsto (λ (a : α), (k a) ^ z * f a) l (𝓝 0) :=
begin
  refine ⟨λ h z, _, λ h n, _⟩,
  { by_cases hz : 0 ≤ z,
    { lift z to ℕ using hz,
      convert h z,
      simp },
    { rw not_le at hz,
      specialize h 0,
      simp at h,
      have : tendsto (λ a, (k a) ^ z) l (𝓝 0) := tendsto.comp (tendsto_fpow_at_top_zero hz) hk,
      exact (zero_mul (0 : 𝕜)) ▸ this.mul h } },
  { specialize h (n : ℤ),
    simp at h,
    exact h }
end

lemma superpolynomial_decay_iff_is_O [order_topology 𝕜] (hk : tendsto k l at_top) :
  superpolynomial_decay l k f ↔
    ∀ (z : ℤ), is_O f (λ (a : α), (k a) ^ z) l :=
begin
  refine (superpolynomial_decay_iff_fpow_tendsto_zero f hk).trans _,
  refine ⟨λ h z, _, λ h z, _⟩,
  { have : ∀ᶠ x in l, k x ≠ 0 := eventually_ne_of_tendsto_at_top hk 0,
    refine is_O_of_div_tendsto_nhds (this.mono (λ x hx hxz, absurd (fpow_eq_zero hxz) hx)) 0 _,
    have : (λ (a : α), k a ^ z)⁻¹ = (λ (a : α), k a ^ (- z)) := funext (λ x, by simp),
    rw [div_eq_mul_inv, mul_comm f, this],
    exact h (-z) },
  { suffices : is_O (λ (a : α), k a ^ z * f a) (λ (a : α), (k a)⁻¹) l,
    from is_O.trans_tendsto this hk.inv_tendsto_at_top,
    convert (h (-(z + 1))).mul (is_O_refl (λ a, (k a) ^ z) l),
    { exact funext (λ _, mul_comm _ _) },
    { exact funext (λ a, (fpow_neg_succ_mul_fpow_self_eq_inv (k a) z).symm) } }
end

lemma superpolynomial_decay_iff_is_o [order_topology 𝕜] (hk : tendsto k l at_top) :
  superpolynomial_decay l k f ↔
    ∀ (z : ℤ), is_o f (λ (a : α), (k a) ^ z) l :=
begin
  refine ⟨λ h z, _, λ h, (superpolynomial_decay_iff_is_O hk).2 (λ z, (h z).is_O)⟩,
  have hk0 : ∀ᶠ x in l, k x ≠ 0 := eventually_ne_of_tendsto_at_top hk 0,
  have : is_o (λ (x : α), (1 : 𝕜)) k l,
  from is_o_of_tendsto' (hk0.mono (λ x hkx hkx', absurd hkx' hkx))
    (by simpa using hk.inv_tendsto_at_top),
  have : is_o f (λ (x : α), k x * k x ^ (z - 1)) l,
  by simpa using this.mul_is_O (((superpolynomial_decay_iff_is_O hk).1 h) $ z - 1),
  refine this.trans_is_O (is_O.of_bound 1 (hk0.mono $ λ x hkx, le_of_eq _)),
  rw [one_mul, fpow_sub_one hkx, mul_comm (k x), mul_assoc, inv_mul_cancel hkx, mul_one],
end

end all_integers


end equivalent_definitions

section polynomial

-- TODO: Generalize these to appropriate spaces
variables {α 𝕜 : Type*} [field 𝕜] [topological_space 𝕜] {l : filter α} {k : α → 𝕜}
variables {f g : α → 𝕜}

@[simp]
lemma superpolynomial_decay_zero (l : filter α) (k : α → 𝕜) : superpolynomial_decay l k 0 :=
λ z, by simpa only [pi.zero_apply, mul_zero] using tendsto_const_nhds

lemma superpolynomial_decay.add [has_continuous_add 𝕜] (hf : superpolynomial_decay l k f)
  (hg : superpolynomial_decay l k g) : superpolynomial_decay l k (f + g) :=
λ z, by simpa only [mul_add, add_zero, pi.add_apply] using (hf z).add (hg z)

lemma superpolynomial_decay.mul [has_continuous_mul 𝕜] (hf : superpolynomial_decay l k f)
  (hg : superpolynomial_decay l k g) : superpolynomial_decay l k (f * g) :=
λ z, by simpa only [mul_assoc, one_mul, mul_zero, pow_zero] using (hf z).mul (hg 0)

lemma superpolynomial_decay.mul_const [has_continuous_mul 𝕜] (hf : superpolynomial_decay l k f)
  (c : 𝕜) : superpolynomial_decay l k (λ n, f n * c) :=
λ z, by simpa only [←mul_assoc, zero_mul] using tendsto.mul_const c (hf z)

lemma superpolynomial_decay.const_mul [has_continuous_mul 𝕜] (hf : superpolynomial_decay l k f)
  (c : 𝕜) : superpolynomial_decay l k (λ n, c * f n) :=
by simpa only [mul_comm c] using hf.mul_const c

lemma superpolynomial_decay.parameter_mul (hf : superpolynomial_decay l k f) :
  superpolynomial_decay l k (k * f) :=
begin
  intro z,
  specialize hf (z + 1),
  rw tendsto_nhds at ⊢ hf,
  refine λ s hs hs0, l.sets_of_superset (hf s hs hs0) (λ x hx, _),
  simp at ⊢ hx,
  rwa [pow_succ (k x) z, mul_comm (k x), mul_assoc] at hx,
end

lemma superpolynomial_decay.mul_parameter (hf : superpolynomial_decay l k f) :
  superpolynomial_decay l k (f * k) :=
by simpa only [mul_comm f k] using hf.parameter_mul

lemma superpolynomial_decay.parameter_pow_mul (hf : superpolynomial_decay l k f)
  (n : ℕ) : superpolynomial_decay l k (k ^ n * f) :=
begin
  induction n with n hn,
  { simpa only [one_mul, pow_zero] using hf },
  { simpa only [pow_succ, mul_assoc] using hn.parameter_mul }
end

lemma superpolynomial_decay.mul_parameter_pow (hf : superpolynomial_decay l k f)
  (n : ℕ) : superpolynomial_decay l k (f * k ^ n) :=
by simpa only [mul_comm f] using hf.parameter_pow_mul n

lemma superpolynomial_decay.polynomial_mul [has_continuous_add 𝕜] [has_continuous_mul 𝕜]
  (hf : superpolynomial_decay l k f) (p : polynomial 𝕜) :
  superpolynomial_decay l k (λ x, (p.eval $ k x) * f x) :=
polynomial.induction_on' p (λ p q hp hq, by simpa [add_mul] using hp.add hq)
  (λ n c, by simpa [mul_assoc] using (hf.parameter_pow_mul n).const_mul c)

lemma superpolynomial_decay.mul_polynomial [has_continuous_add 𝕜] [has_continuous_mul 𝕜]
  (hf : superpolynomial_decay l k f) (p : polynomial 𝕜) :
  superpolynomial_decay l k (λ x, f x * (p.eval $ k x)) :=
begin
  convert hf.polynomial_mul p,
  exact funext (λ x, mul_comm _ _)
end

end polynomial

end asymptotics
