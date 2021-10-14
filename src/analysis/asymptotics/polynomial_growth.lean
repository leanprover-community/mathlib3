/-
Copyright (c) 2021 Devon Tuma. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/
import analysis.asymptotics.asymptotics
import analysis.asymptotics.superpolynomial_decay
import analysis.special_functions.polynomials

/-!
# Polynomial Growth

This file defines polynomial growth of functions as `asymptotics.polynomial_growth l k f`.
A function `f : α → E` has polynomial growth in the parameter `k : α → S` on the filter `l` if
  there exists `n : ℕ` such that `f(x)` is `O(k(x) ^ n)`.
Note `f` and `k` may have different domains, and only the domain of `k` needs a ring structure.
Most theorems assume little about the domain of `f`, so the file is organized by the domain of `k`.

Equivalently `f(x)` is polynomial growth in `k` if `f` is `O(p(k(x)))` for some polynomial `p`
  (see `polynomial_growth_iff_is_O_polynomial`).

When the parameter is a linear inclusion, this gives standard polynomial growth.
When the parameter is logarithmic, it gives polylogarithmic growth as described here:
https://en.wikipedia.org/wiki/Polylogarithmic_function

# Main Theorems

* `polynomial_growth.polynomial_eval`: A polynomial evaluated at a polynomial growth function
    is also polynomial growth, assuming `∥k x∥` is eventually bounded below by `1`.
* `polynomial_growth_of_norm_bdd_above`: A function with bounded norm must have polynomial growth
-/

namespace asymptotics

open filter polynomial

/-- A function `f` has polynomial growth in parameter `k` if `f` is `O(k(x)^n)` for some `n : ℕ`.
  The domain of `f` can be any normed space, but the domain of `k` must be a normed ring. -/
def polynomial_growth {α E K : Type*} [has_norm E] [normed_ring K]
  (l : filter α) (k : α → K) (f : α → E) :=
∃ (n : ℕ), is_O f (λ x, (k x) ^ n) l

variables {α : Type*} {l : filter α}
variables {E E' S S' R R' : Type*} [has_norm E] [has_norm E']
   [normed_group S] [normed_group S'] [normed_ring R] [normed_ring R']

section normed_ring

variables {K : Type*} [normed_ring K] {k : α → K}

lemma polynomial_growth.mono {f : α → S} {g : α → E}
  (hf : polynomial_growth l k f) (hfg : ∀ x, ∥g x∥ ≤ ∥f x∥) :
  polynomial_growth l k g :=
let ⟨n, hn⟩ := hf in ⟨n, (is_O_of_le l hfg).trans hn⟩

lemma polynomial_growth.is_O_trans {f : α → S} {g : α → E}
  (hf : polynomial_growth l k f) (h : is_O g f l) :
  polynomial_growth l k g :=
let ⟨n, hn⟩ := hf in ⟨n, h.trans hn⟩

lemma polynomial_growth.eventually_trans {f : α → S} {g : α → E}
  (hf : polynomial_growth l k f) (h : ∀ᶠ x in l, ∥g x∥ ≤ ∥f x∥) :
  polynomial_growth l k g :=
hf.is_O_trans $ is_O_iff.2 ⟨1, by simpa using h⟩

variables (l k)

/-- For any parameter `k`, it is polynomial growth in itself. -/
@[simp]
lemma polynomial_growth_parameter :
  polynomial_growth l k k :=
⟨1, by simpa only [pow_one] using is_O_refl k l⟩

@[simp]
lemma polynomial_growth_const [norm_one_class K] (x : E) :
  polynomial_growth l k (λ _, x) :=
⟨0, is_O_of_le' l (λ x, by simp only [mul_one, norm_one, pow_zero])⟩

lemma polynomial_growth_zero [norm_one_class K] [has_zero S] :
  polynomial_growth l k (0 : α → S) :=
polynomial_growth_const l k 0

lemma polynomial_growth_one [norm_one_class K] [has_one S] :
  polynomial_growth l k (1 : α → S) :=
polynomial_growth_const l k 1

variables {l k}

end normed_ring

lemma polynomial_growth_of_superpolynomial_decay {α 𝕜 : Type*} [ordered_comm_semiring α]
  [normed_field 𝕜] [algebra α 𝕜] (f : α → 𝕜) (hf : superpolynomial_decay f) :
  polynomial_growth at_top (algebra_map α 𝕜) f :=
⟨0, by simpa only [gpow_zero, pow_zero] using hf 0⟩

section normed_field

variables {K : Type*} [normed_field K] {k : α → K}

/-- Polynomial growth in `k` is additive if `k` eventually has norm at least `1` -/
lemma polynomial_growth.add {f g : α → S}
  (hf : polynomial_growth l k f) (hg : polynomial_growth l k g)
  (hk : ∀ᶠ x in l, 1 ≤ ∥k x∥) : polynomial_growth l k (f + g) :=
let ⟨n, hn⟩ := hf in let ⟨m, hm⟩ := hg in
⟨max n m, is_O.add (hn.trans $ is_O_pow_pow_of_le hk (le_max_left n m))
  (hm.trans $ is_O_pow_pow_of_le hk (le_max_right n m))⟩

/-- Polynomial growth is multiplicative for arbitrary parameters -/
lemma polynomial_growth.mul {f g : α → R}
  (hf : polynomial_growth l k f) (hg : polynomial_growth l k g) :
  polynomial_growth l k (f * g) :=
let ⟨n, hn⟩ := hf in let ⟨m, hm⟩ := hg in
⟨n + m, (is_O.mul hn hm).trans $ is_O_of_le l (λ x, (pow_add (k x) n m) ▸ le_rfl)⟩

lemma polynomial_growth.pow {f : α → R}
  (hf : polynomial_growth l k f) (n : ℕ) :
  polynomial_growth l k (f ^ n) :=
let ⟨m, hm⟩ := hf in
  ⟨m * n, (is_O.pow hm n).trans $ is_O_of_le l (λ x, (pow_mul (k x) m n) ▸ le_rfl)⟩

/-- A polynomial evaluated at a polynomial growth function is polynomial growth,
  assuming `k` eventually has norm at least `1` -/
theorem polynomial_growth.polynomial_eval {f : α → R}
  (hf : polynomial_growth l k f) (hk : ∀ᶠ x in l, 1 ≤ ∥k x∥)
  (p : polynomial R) : polynomial_growth l k (λ x, eval (f x) p) :=
begin
  refine p.induction_on (λ c, _) (λ p q hp hq, _) (λ n c h, _),
  { exact (polynomial_growth_const l k c).mono (λ x, le_of_eq $ congr_arg _ eval_C) },
  { exact (hp.add hq hk).mono (λ x, le_of_eq $ congr_arg _ eval_add) },
  { exact (h.mul (hf)).mono (λ x, le_of_eq $ congr_arg _ $
      by simp only [eval_C, eval_mul_X_pow, pi.mul_apply, pow_add (f x) n 1, mul_assoc, pow_one]) }
end

end normed_field

section nondiscrete_normed_field

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜] {k : α → 𝕜}

/-- If the norm of `f` is bounded above then it has polynomial growth,
  assuming `k` maps into a `nondiscrete_normed_field` -/
lemma polynomial_growth_of_norm_bdd_above
  {f : α → E} (hf : bdd_above (set.range (λ x, ∥f x∥))) :
  polynomial_growth l k f :=
let ⟨c, hc⟩ := hf in
let ⟨y, hy⟩ := normed_field.exists_lt_norm 𝕜 c in
(polynomial_growth_const l k y).mono $
  λ x, ((mem_upper_bounds.1 hc) (∥f x∥) (set.mem_range_self x)).trans (le_of_lt hy)

lemma polynomial_growth_of_norm_eventually_le
  {f : α → E} (b : ℝ) (hf : ∀ᶠ x in l, ∥f x∥ ≤ b) :
  polynomial_growth l k f :=
let ⟨y, hy⟩ := normed_field.exists_lt_norm 𝕜 b in
(polynomial_growth_const l k y).eventually_trans $
  sets_of_superset l hf (λ x hx, (le_trans hx (le_of_lt hy) : ∥f x∥ ≤ ∥y∥))

end nondiscrete_normed_field

section normed_linear_ordered_field

variables {𝕜 : Type*} [normed_linear_ordered_field 𝕜] [order_topology 𝕜] {k : α → 𝕜}

/-- Equivalence of definition in terms of powers and polynomials, assuming order topology on `𝕜`,
  and that the parameter tendsto to `at_top` -/
theorem polynomial_growth_iff_is_O_polynomial (hk : tendsto k l at_top)
  (f : α → E) : polynomial_growth l k f ↔
    ∃ (p : polynomial 𝕜), is_O f (λ x, eval (k x) p) l :=
begin
  refine ⟨λ h, let ⟨n, hn⟩ := h in ⟨X ^ n, by simpa⟩, _⟩,
  rintro ⟨p, hp⟩,
  refine ⟨p.nat_degree, is_O.trans hp _⟩,
  have : is_O ((λ a, eval a p) ∘ k) ((λ a, eval a (X ^ p.nat_degree)) ∘ k) l,
  from is_O.comp_tendsto (polynomial.is_O_of_degree_le p (X ^ p.nat_degree) (by simp)) hk,
  simpa only [eval_X, eval_pow] using this,
end

lemma polynomial_growth_of_is_O_polynomial (hk : tendsto k l at_top)
  (f : α → E) (p : polynomial 𝕜) (h : is_O f (λ x, eval (k x) p) l) :
  polynomial_growth l k f :=
(polynomial_growth_iff_is_O_polynomial hk f).2 ⟨p, h⟩

end normed_linear_ordered_field

end asymptotics
