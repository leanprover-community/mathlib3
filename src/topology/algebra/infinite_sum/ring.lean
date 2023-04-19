/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl
-/
import algebra.big_operators.nat_antidiagonal
import topology.algebra.infinite_sum.basic
import topology.algebra.ring.basic

/-!
# Infinite sum in a ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file provides lemmas about the interaction between infinite sums and multiplication.

## Main results

* `tsum_mul_tsum_eq_tsum_sum_antidiagonal`: Cauchy product formula
-/

open filter finset function
open_locale big_operators classical

variables {ι κ R α : Type*}

section non_unital_non_assoc_semiring
variables [non_unital_non_assoc_semiring α] [topological_space α] [topological_semiring α]
  {f g : ι → α} {a a₁ a₂ : α}

lemma has_sum.mul_left (a₂) (h : has_sum f a₁) : has_sum (λ i, a₂ * f i) (a₂ * a₁) :=
by simpa only using h.map (add_monoid_hom.mul_left a₂) (continuous_const.mul continuous_id)

lemma has_sum.mul_right (a₂) (hf : has_sum f a₁) : has_sum (λ i, f i * a₂) (a₁ * a₂) :=
by simpa only using hf.map (add_monoid_hom.mul_right a₂) (continuous_id.mul continuous_const)

lemma summable.mul_left (a) (hf : summable f) : summable (λ i, a * f i) :=
(hf.has_sum.mul_left _).summable

lemma summable.mul_right (a) (hf : summable f) : summable (λ i, f i * a) :=
(hf.has_sum.mul_right _).summable

section tsum
variables [t2_space α]

lemma summable.tsum_mul_left (a) (hf : summable f) : ∑' i, a * f i = a * ∑' i, f i :=
(hf.has_sum.mul_left _).tsum_eq

lemma summable.tsum_mul_right (a) (hf : summable f) : ∑' i, f i * a = (∑' i, f i) * a :=
(hf.has_sum.mul_right _).tsum_eq

lemma commute.tsum_right (a) (h : ∀ i, commute a (f i)) : commute a (∑' i, f i) :=
if hf : summable f then
  (hf.tsum_mul_left a).symm.trans ((congr_arg _ $ funext h).trans (hf.tsum_mul_right a))
else
  (tsum_eq_zero_of_not_summable hf).symm ▸ commute.zero_right _

lemma commute.tsum_left (a) (h : ∀ i, commute (f i) a) : commute (∑' i, f i) a :=
(commute.tsum_right _ $ λ i, (h i).symm).symm

end tsum
end non_unital_non_assoc_semiring

section division_semiring
variables [division_semiring α] [topological_space α] [topological_semiring α] {f g : ι → α}
  {a a₁ a₂ : α}

lemma has_sum.div_const (h : has_sum f a) (b : α) : has_sum (λ i, f i / b) (a / b) :=
by simp only [div_eq_mul_inv, h.mul_right b⁻¹]

lemma summable.div_const (h : summable f) (b : α) : summable (λ i, f i / b) :=
(h.has_sum.div_const _).summable

lemma has_sum_mul_left_iff (h : a₂ ≠ 0) : has_sum (λ i, a₂ * f i) (a₂ * a₁) ↔ has_sum f a₁ :=
⟨λ H, by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a₂⁻¹, has_sum.mul_left _⟩

lemma has_sum_mul_right_iff (h : a₂ ≠ 0) : has_sum (λ i, f i * a₂) (a₁ * a₂) ↔ has_sum f a₁ :=
⟨λ H, by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a₂⁻¹, has_sum.mul_right _⟩

lemma has_sum_div_const_iff (h : a₂ ≠ 0) : has_sum (λ i, f i / a₂) (a₁ / a₂) ↔ has_sum f a₁ :=
by simpa only [div_eq_mul_inv] using has_sum_mul_right_iff (inv_ne_zero h)

lemma summable_mul_left_iff (h : a ≠ 0) : summable (λ i, a * f i) ↔ summable f :=
⟨λ H, by simpa only [inv_mul_cancel_left₀ h] using H.mul_left a⁻¹, λ H, H.mul_left _⟩

lemma summable_mul_right_iff (h : a ≠ 0) : summable (λ i, f i * a) ↔ summable f :=
⟨λ H, by simpa only [mul_inv_cancel_right₀ h] using H.mul_right a⁻¹, λ H, H.mul_right _⟩

lemma summable_div_const_iff (h : a ≠ 0) : summable (λ i, f i / a) ↔ summable f :=
by simpa only [div_eq_mul_inv] using summable_mul_right_iff (inv_ne_zero h)

lemma tsum_mul_left [t2_space α] : (∑' x, a * f x) = a * ∑' x, f x :=
if hf : summable f then hf.tsum_mul_left a
else if ha : a = 0 then by simp [ha]
else by rw [tsum_eq_zero_of_not_summable hf,
  tsum_eq_zero_of_not_summable (mt (summable_mul_left_iff ha).mp hf), mul_zero]

lemma tsum_mul_right [t2_space α] : (∑' x, f x * a) = (∑' x, f x) * a :=
if hf : summable f then hf.tsum_mul_right a
else if ha : a = 0 then by simp [ha]
else by rw [tsum_eq_zero_of_not_summable hf,
  tsum_eq_zero_of_not_summable (mt (summable_mul_right_iff ha).mp hf), zero_mul]

lemma tsum_div_const [t2_space α] : (∑' x, f x / a) = (∑' x, f x) / a :=
by simpa only [div_eq_mul_inv] using tsum_mul_right

end division_semiring

/-!
### Multipliying two infinite sums

In this section, we prove various results about `(∑' x : ι, f x) * (∑' y : κ, g y)`. Note that we
always assume that the family `λ x : ι × κ, f x.1 * g x.2` is summable, since there is no way to
deduce this from the summmabilities of `f` and `g` in general, but if you are working in a normed
space, you may want to use the analogous lemmas in `analysis/normed_space/basic`
(e.g `tsum_mul_tsum_of_summable_norm`).

We first establish results about arbitrary index types, `ι` and `κ`, and then we specialize to
`ι = κ = ℕ` to prove the Cauchy product formula (see `tsum_mul_tsum_eq_tsum_sum_antidiagonal`).

#### Arbitrary index types
-/

section tsum_mul_tsum
variables [topological_space α] [t3_space α] [non_unital_non_assoc_semiring α]
  [topological_semiring α] {f : ι → α} {g : κ → α} {s t u : α}

lemma has_sum.mul_eq (hf : has_sum f s) (hg : has_sum g t)
  (hfg : has_sum (λ (x : ι × κ), f x.1 * g x.2) u) :
  s * t = u :=
have key₁ : has_sum (λ i, f i * t) (s * t),
  from hf.mul_right t,
have this : ∀ i : ι, has_sum (λ c : κ, f i * g c) (f i * t),
  from λ i, hg.mul_left (f i),
have key₂ : has_sum (λ i, f i * t) u,
  from has_sum.prod_fiberwise hfg this,
key₁.unique key₂

lemma has_sum.mul (hf : has_sum f s) (hg : has_sum g t)
  (hfg : summable (λ (x : ι × κ), f x.1 * g x.2)) :
  has_sum (λ (x : ι × κ), f x.1 * g x.2) (s * t) :=
let ⟨u, hu⟩ := hfg in
(hf.mul_eq hg hu).symm ▸ hu

/-- Product of two infinites sums indexed by arbitrary types.
    See also `tsum_mul_tsum_of_summable_norm` if `f` and `g` are abolutely summable. -/
lemma tsum_mul_tsum (hf : summable f) (hg : summable g)
  (hfg : summable (λ (x : ι × κ), f x.1 * g x.2)) :
  (∑' x, f x) * (∑' y, g y) = (∑' z : ι × κ, f z.1 * g z.2) :=
hf.has_sum.mul_eq hg.has_sum hfg.has_sum

end tsum_mul_tsum

/-!
#### `ℕ`-indexed families (Cauchy product)

We prove two versions of the Cauchy product formula. The first one is
`tsum_mul_tsum_eq_tsum_sum_range`, where the `n`-th term is a sum over `finset.range (n+1)`
involving `nat` subtraction.
In order to avoid `nat` subtraction, we also provide `tsum_mul_tsum_eq_tsum_sum_antidiagonal`,
where the `n`-th term is a sum over all pairs `(k, l)` such that `k+l=n`, which corresponds to the
`finset` `finset.nat.antidiagonal n`
-/

section cauchy_product
variables [topological_space α] [non_unital_non_assoc_semiring α] {f g : ℕ → α}

/- The family `(k, l) : ℕ × ℕ ↦ f k * g l` is summable if and only if the family
`(n, k, l) : Σ (n : ℕ), nat.antidiagonal n ↦ f k * g l` is summable. -/
lemma summable_mul_prod_iff_summable_mul_sigma_antidiagonal :
  summable (λ x : ℕ × ℕ, f x.1 * g x.2) ↔
    summable (λ x : (Σ (n : ℕ), nat.antidiagonal n), f (x.2 : ℕ × ℕ).1 * g (x.2 : ℕ × ℕ).2) :=
nat.sigma_antidiagonal_equiv_prod.summable_iff.symm

variables [t3_space α] [topological_semiring α]

lemma summable_sum_mul_antidiagonal_of_summable_mul (h : summable (λ x : ℕ × ℕ, f x.1 * g x.2)) :
  summable (λ n, ∑ kl in nat.antidiagonal n, f kl.1 * g kl.2) :=
begin
  rw summable_mul_prod_iff_summable_mul_sigma_antidiagonal at h,
  conv {congr, funext, rw [← finset.sum_finset_coe, ← tsum_fintype]},
  exact h.sigma' (λ n, (has_sum_fintype _).summable),
end

/-- The **Cauchy product formula** for the product of two infinites sums indexed by `ℕ`, expressed
by summing on `finset.nat.antidiagonal`.

See also `tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm` if `f` and `g` are absolutely
summable. -/
lemma tsum_mul_tsum_eq_tsum_sum_antidiagonal (hf : summable f) (hg : summable g)
  (hfg : summable (λ (x : ℕ × ℕ), f x.1 * g x.2)) :
  (∑' n, f n) * (∑' n, g n) = (∑' n, ∑ kl in nat.antidiagonal n, f kl.1 * g kl.2) :=
begin
  conv_rhs {congr, funext, rw [← finset.sum_finset_coe, ← tsum_fintype]},
  rw [tsum_mul_tsum hf hg hfg, ← nat.sigma_antidiagonal_equiv_prod.tsum_eq (_ : ℕ × ℕ → α)],
  exact tsum_sigma' (λ n, (has_sum_fintype _).summable)
    (summable_mul_prod_iff_summable_mul_sigma_antidiagonal.mp hfg)
end

lemma summable_sum_mul_range_of_summable_mul (h : summable (λ x : ℕ × ℕ, f x.1 * g x.2)) :
  summable (λ n, ∑ k in range (n+1), f k * g (n - k)) :=
begin
  simp_rw ← nat.sum_antidiagonal_eq_sum_range_succ (λ k l, f k * g l),
  exact summable_sum_mul_antidiagonal_of_summable_mul h
end

/-- The **Cauchy product formula** for the product of two infinites sums indexed by `ℕ`, expressed
by summing on `finset.range`.

See also `tsum_mul_tsum_eq_tsum_sum_range_of_summable_norm` if `f` and `g` are absolutely summable.
-/
lemma tsum_mul_tsum_eq_tsum_sum_range (hf : summable f) (hg : summable g)
  (hfg : summable (λ (x : ℕ × ℕ), f x.1 * g x.2)) :
  (∑' n, f n) * (∑' n, g n) = ∑' n, ∑ k in range (n + 1), f k * g (n - k) :=
begin
  simp_rw ← nat.sum_antidiagonal_eq_sum_range_succ (λ k l, f k * g l),
  exact tsum_mul_tsum_eq_tsum_sum_antidiagonal hf hg hfg
end

end cauchy_product
