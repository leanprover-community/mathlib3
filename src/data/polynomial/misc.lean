/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.algebra_map
-- import data.polynomial.division
import data.polynomial.derivative

/-!
# Theory of univariate polynomials

Polynomials are represented as `add_monoid_algebra R ℕ`, where `R` is a commutative semiring.
-/

noncomputable theory
local attribute [instance, priority 100] classical.prop_decidable

local attribute [instance, priority 10] is_semiring_hom.comp is_ring_hom.comp

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v w x y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z}
  {a b : R} {m n : ℕ}



section identities

/- @TODO: pow_add_expansion and pow_sub_pow_factor are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring

Maybe use data.nat.choose to prove it.
 -/

def pow_add_expansion {R : Type*} [comm_semiring R] (x y : R) : ∀ (n : ℕ),
  {k // (x + y)^n = x^n + n*x^(n-1)*y + k * y^2}
| 0 := ⟨0, by simp⟩
| 1 := ⟨0, by simp⟩
| (n+2) :=
  begin
    cases pow_add_expansion (n+1) with z hz,
    existsi x*z + (n+1)*x^n+z*y,
    calc (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) : by ring_exp
    ... = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) : by rw hz
    ... = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x*z + (n+1)*x^n+z*y) * y ^ 2 :
      by { push_cast, ring_exp! }
  end

variables [comm_ring R]

private def poly_binom_aux1 (x y : R) (e : ℕ) (a : R) :
  {k : R // a * (x + y)^e = a * (x^e + e*x^(e-1)*y + k*y^2)} :=
begin
  existsi (pow_add_expansion x y e).val,
  congr,
  apply (pow_add_expansion _ _ _).property
end

private lemma poly_binom_aux2 (f : polynomial R) (x y : R) :
  f.eval (x + y) = f.sum (λ e a, a * (x^e + e*x^(e-1)*y + (poly_binom_aux1 x y e a).val*y^2)) :=
begin
  unfold eval eval₂, congr, ext,
  apply (poly_binom_aux1 x y _ _).property
end

private lemma poly_binom_aux3 (f : polynomial R) (x y : R) : f.eval (x + y) =
  f.sum (λ e a, a * x^e) +
  f.sum (λ e a, (a * e * x^(e-1)) * y) +
  f.sum (λ e a, (a *(poly_binom_aux1 x y e a).val)*y^2) :=
by rw poly_binom_aux2; simp [left_distrib, finsupp.sum_add, mul_assoc]

def binom_expansion (f : polynomial R) (x y : R) :
  {k : R // f.eval (x + y) = f.eval x + (f.derivative.eval x) * y + k * y^2} :=
begin
  existsi f.sum (λ e a, a *((poly_binom_aux1 x y e a).val)),
  rw poly_binom_aux3,
  congr,
  { rw derivative_eval, symmetry,
    apply finsupp.sum_mul },
  { symmetry, apply finsupp.sum_mul }
end

def pow_sub_pow_factor (x y : R) : Π (i : ℕ), {z : R // x^i - y^i = z * (x - y)}
| 0 := ⟨0, by simp⟩
| 1 := ⟨1, by simp⟩
| (k+2) :=
  begin
    cases @pow_sub_pow_factor (k+1) with z hz,
    existsi z*x + y^(k+1),
    calc x ^ (k + 2) - y ^ (k + 2)
        = x * (x ^ (k + 1) - y ^ (k + 1)) + (x * y ^ (k + 1) - y ^ (k + 2)) : by ring_exp
    ... = x * (z * (x - y)) + (x * y ^ (k + 1) - y ^ (k + 2)) : by rw hz
    ... = (z * x + y ^ (k + 1)) * (x - y) : by ring_exp
  end

def eval_sub_factor (f : polynomial R) (x y : R) :
  {z : R // f.eval x - f.eval y = z * (x - y)} :=
begin
  refine ⟨f.sum (λ i r, r * (pow_sub_pow_factor x y i).val), _⟩,
  delta eval eval₂,
  rw ← finsupp.sum_sub,
  rw finsupp.sum_mul,
  delta finsupp.sum,
  congr, ext i r, dsimp,
  rw [mul_assoc, ←(pow_sub_pow_factor x y _).prop, mul_sub],
end

end identities

section integral_normalization

section semiring
variables [semiring R]

/-- If `f : polynomial R` is a nonzero polynomial with root `z`, `integral_normalization f` is
a monic polynomial with root `leading_coeff f * z`.

Moreover, `integral_normalization 0 = 0`.
-/
noncomputable def integral_normalization (f : polynomial R) : polynomial R :=
on_finset f.support
  (λ i, if f.degree = i then 1 else coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i))
  begin
    intros i h,
    apply mem_support_iff.mpr,
    split_ifs at h with hi,
    { exact coeff_ne_zero_of_eq_degree hi },
    { exact left_ne_zero_of_mul h },
  end

lemma integral_normalization_coeff_degree {f : polynomial R} {i : ℕ} (hi : f.degree = i) :
  (integral_normalization f).coeff i = 1 :=
if_pos hi

lemma integral_normalization_coeff_nat_degree {f : polynomial R} (hf : f ≠ 0) :
  (integral_normalization f).coeff (nat_degree f) = 1 :=
integral_normalization_coeff_degree (degree_eq_nat_degree hf)

lemma integral_normalization_coeff_ne_degree {f : polynomial R} {i : ℕ} (hi : f.degree ≠ i) :
  coeff (integral_normalization f) i = coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i) :=
if_neg hi

lemma integral_normalization_coeff_ne_nat_degree {f : polynomial R} {i : ℕ} (hi : i ≠ nat_degree f) :
  coeff (integral_normalization f) i = coeff f i * f.leading_coeff ^ (f.nat_degree - 1 - i) :=
integral_normalization_coeff_ne_degree (degree_ne_of_nat_degree_ne hi.symm)

lemma monic_integral_normalization {f : polynomial R} (hf : f ≠ 0) :
  monic (integral_normalization f) :=
begin
  apply monic_of_degree_le f.nat_degree,
  { refine finset.sup_le (λ i h, _),
    rw [integral_normalization, mem_support_iff, on_finset_apply] at h,
    split_ifs at h with hi,
    { exact le_trans (le_of_eq hi.symm) degree_le_nat_degree },
    { erw [with_bot.some_le_some],
      apply le_nat_degree_of_ne_zero,
      exact left_ne_zero_of_mul h } },
  { exact integral_normalization_coeff_nat_degree hf }
end

end semiring

variables [integral_domain R]

@[simp] lemma support_integral_normalization {f : polynomial R} (hf : f ≠ 0) :
  (integral_normalization f).support = f.support :=
begin
  ext i,
  simp only [integral_normalization, on_finset_apply, mem_support_iff],
  split_ifs with hi,
  { simp only [ne.def, not_false_iff, true_iff, one_ne_zero, hi],
    exact coeff_ne_zero_of_eq_degree hi },
  split,
  { intro h,
    exact left_ne_zero_of_mul h },
  { intro h,
    refine mul_ne_zero h (pow_ne_zero _ _),
    exact λ h, hf (leading_coeff_eq_zero.mp h) }
end

variables [comm_ring S]

lemma integral_normalization_eval₂_eq_zero {p : polynomial R} (hp : p ≠ 0) (f : R →+* S)
  {z : S} (hz : eval₂ f z p = 0) (inj : ∀ (x : R), f x = 0 → x = 0) :
  eval₂ f (z * f p.leading_coeff) (integral_normalization p) = 0 :=
calc eval₂ f (z * f p.leading_coeff) (integral_normalization p)
    = p.support.attach.sum
        (λ i, f (coeff (integral_normalization p) i.1 * p.leading_coeff ^ i.1) * z ^ i.1) :
      by { rw [eval₂, finsupp.sum, support_integral_normalization hp],
           simp only [mul_comm z, mul_pow, mul_assoc, ring_hom.map_pow, ring_hom.map_mul],
           exact finset.sum_attach.symm }
... = p.support.attach.sum
        (λ i, f (coeff p i.1 * p.leading_coeff ^ (nat_degree p - 1)) * z ^ i.1) :
      begin
        have one_le_deg : 1 ≤ nat_degree p :=
          nat.succ_le_of_lt (nat_degree_pos_of_eval₂_root hp f hz inj),
        congr,
        ext i,
        congr' 2,
        by_cases hi : i.1 = nat_degree p,
        { rw [hi, integral_normalization_coeff_degree, one_mul, leading_coeff, ←pow_succ,
              nat.sub_add_cancel one_le_deg],
          exact degree_eq_nat_degree hp },
        { have : i.1 ≤ p.nat_degree - 1 := nat.le_pred_of_lt (lt_of_le_of_ne
            (le_nat_degree_of_ne_zero (finsupp.mem_support_iff.mp i.2)) hi),
          rw [integral_normalization_coeff_ne_nat_degree hi, mul_assoc, ←pow_add,
              nat.sub_add_cancel this] }
      end
... = f p.leading_coeff ^ (nat_degree p - 1) * eval₂ f z p :
      by { simp_rw [eval₂, finsupp.sum, λ i, mul_comm (coeff p i), ring_hom.map_mul,
                    ring_hom.map_pow, mul_assoc, ←finset.mul_sum],
           congr' 1,
           exact @finset.sum_attach _ _ p.support _ (λ i, f (p.coeff i) * z ^ i) }
... = 0 : by rw [hz, _root_.mul_zero]

lemma integral_normalization_aeval_eq_zero [algebra R S] {f : polynomial R} (hf : f ≠ 0)
  {z : S} (hz : aeval R S z f = 0) (inj : ∀ (x : R), algebra_map R S x = 0 → x = 0) :
  aeval R S (z * algebra_map R S f.leading_coeff) (integral_normalization f) = 0 :=
integral_normalization_eval₂_eq_zero hf (algebra_map R S) hz inj

end integral_normalization

end polynomial

namespace is_integral_domain

variables {R : Type*} [comm_ring R]

/-- Lift evidence that `is_integral_domain R` to `is_integral_domain (polynomial R)`. -/
lemma polynomial (h : is_integral_domain R) : is_integral_domain (polynomial R) :=
@integral_domain.to_is_integral_domain _ (@polynomial.integral_domain _ (h.to_integral_domain _))

end is_integral_domain
