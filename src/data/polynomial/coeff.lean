/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.monomial
import data.finset.nat_antidiagonal

/-!
# Theory of univariate polynomials

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/

noncomputable theory

open finsupp finset add_monoid_algebra
open_locale big_operators

namespace polynomial
universes u v
variables {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variables [semiring R] {p q r : polynomial R}

section coeff

lemma coeff_one (n : ℕ) : coeff (1 : polynomial R) n = if 0 = n then 1 else 0 :=
coeff_monomial

@[simp]
lemma coeff_add (p q : polynomial R) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n := rfl

lemma coeff_sum [semiring S] (n : ℕ) (f : ℕ → R → polynomial S) :
  coeff (p.sum f) n = p.sum (λ a b, coeff (f a b) n) := finsupp.sum_apply

@[simp] lemma coeff_smul (p : polynomial R) (r : R) (n : ℕ) :
coeff (r • p) n = r * coeff p n := finsupp.smul_apply

variable (R)
/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : polynomial R →ₗ[R] R :=
{ to_fun := λ f, coeff f n,
  map_add' := λ f g, coeff_add f g n,
  map_smul' := λ r p, coeff_smul p r n }
variable {R}

@[simp] lemma lcoeff_apply (n : ℕ) (f : polynomial R) : lcoeff R n f = coeff f n := rfl

@[simp] lemma finset_sum_coeff {ι : Type*} (s : finset ι) (f : ι → polynomial R) (n : ℕ) :
  coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
(s.sum_hom (λ q : polynomial R, lcoeff R n q)).symm

lemma coeff_mul (p q : polynomial R) (n : ℕ) :
  coeff (p * q) n = ∑ x in nat.antidiagonal n, coeff p x.1 * coeff q x.2 :=
have hite : ∀ a : ℕ × ℕ, ite (a.1 + a.2 = n) (coeff p (a.fst) * coeff q (a.snd)) 0 ≠ 0
    → a.1 + a.2 = n, from λ a ha, by_contradiction
  (λ h, absurd (eq.refl (0 : R)) (by rwa if_neg h at ha)),
calc coeff (p * q) n = ∑ a in p.support, ∑ b in q.support,
    ite (a + b = n) (coeff p a * coeff q b) 0 :
  by { simp only [mul_def, coeff_sum, coeff_single], refl }
... = ∑ v in p.support.product q.support, ite (v.1 + v.2 = n) (coeff p v.1 * coeff q v.2) 0 :
  by rw sum_product
... = ∑ x in nat.antidiagonal n, coeff p x.1 * coeff q x.2 :
begin
  refine sum_bij_ne_zero (λ x _ _, x)
  (λ x _ hx, nat.mem_antidiagonal.2 (hite x hx)) (λ _ _ _ _ _ _ h, h)
  (λ x h₁ h₂, ⟨x, _, _, rfl⟩) _,
  { rw [mem_product, mem_support_iff, mem_support_iff],
    exact ne_zero_and_ne_zero_of_mul h₂ },
  { rw nat.mem_antidiagonal at h₁, rwa [if_pos h₁] },
  { intros x h hx, rw [if_pos (hite x hx)] }
end

@[simp] lemma mul_coeff_zero (p q : polynomial R) : coeff (p * q) 0 = coeff p 0 * coeff q 0 :=
by simp [coeff_mul]

lemma coeff_mul_X_zero (p : polynomial R) : coeff (p * X) 0 = 0 :=
by simp

lemma coeff_X_mul_zero (p : polynomial R) : coeff (X * p) 0 = 0 :=
by simp

lemma coeff_C_mul_X (x : R) (k n : ℕ) :
  coeff (C x * X^k : polynomial R) n = if n = k then x else 0 :=
by rw [← single_eq_C_mul_X]; simp [monomial, single, eq_comm, coeff]; congr

@[simp] lemma coeff_C_mul (p : polynomial R) : coeff (C a * p) n = a * coeff p n :=
begin
  conv in (a * _) { rw [← @sum_single _ _ _ p, coeff_sum] },
  rw [mul_def, ←monomial_zero_left, monomial, sum_single_index],
  { simp only [coeff_single, finsupp.mul_sum, coeff_sum],
    apply sum_congr rfl,
    assume i hi, by_cases i = n; simp [h] },
  { simp [finsupp.sum] }
end

lemma C_mul' (a : R) (f : polynomial R) : C a * f = a • f :=
ext $ λ n, coeff_C_mul f

@[simp] lemma coeff_mul_C (p : polynomial R) (n : ℕ) (a : R) :
  coeff (p * C a) n = coeff p n * a :=
begin
  conv_rhs { rw [← @finsupp.sum_single _ _ _ p, coeff_sum] },
  rw [mul_def, ←monomial_zero_left], simp_rw [sum_single_index],
  { simp only [coeff_single, finsupp.sum_mul, coeff_sum],
    apply sum_congr rfl,
    assume i hi, by_cases i = n; simp [h], },
end

lemma monomial_one_eq_X_pow : ∀{n}, monomial n (1 : R) = X^n
| 0     := rfl
| (n+1) :=
  calc monomial (n + 1) (1 : R) = monomial n 1 * X : by rw [X, monomial_mul_monomial, mul_one]
    ... = X^n * X : by rw [monomial_one_eq_X_pow]
    ... = X^(n+1) : by simp only [pow_add, pow_one]

lemma monomial_eq_smul_X {n} : monomial n (a : R) = a • X^n :=
begin
  calc monomial n a = monomial n (a * 1) : by simp
    ... = a • monomial n 1 : (smul_single' _ _ _).symm
    ... = a • X^n  : by rw monomial_one_eq_X_pow
end

lemma coeff_X_pow (k n : ℕ) :
  coeff (X^k : polynomial R) n = if n = k then 1 else 0 :=
by rw [← monomial_one_eq_X_pow]; simp [monomial, single, eq_comm, coeff]; congr

@[simp]
lemma coeff_X_pow_self (n : ℕ) :
  coeff (X^n : polynomial R) n = 1 :=
by simp [coeff_X_pow]

theorem coeff_mul_X_pow (p : polynomial R) (n d : ℕ) :
  coeff (p * polynomial.X ^ n) (d + n) = coeff p d :=
begin
  rw [coeff_mul, sum_eq_single (d,n), coeff_X_pow, if_pos rfl, mul_one],
  { rintros ⟨i,j⟩ h1 h2, rw [coeff_X_pow, if_neg, mul_zero], rintro rfl, apply h2,
    rw [nat.mem_antidiagonal, add_right_cancel_iff] at h1, subst h1 },
  { exact λ h1, (h1 (nat.mem_antidiagonal.2 rfl)).elim }
end

@[simp] theorem coeff_mul_X (p : polynomial R) (n : ℕ) :
  coeff (p * X) (n + 1) = coeff p n :=
by simpa only [pow_one] using coeff_mul_X_pow p 1 n

theorem mul_X_pow_eq_zero {p : polynomial R} {n : ℕ}
  (H : p * X ^ n = 0) : p = 0 :=
ext $ λ k, (coeff_mul_X_pow p n k).symm.trans $ ext_iff.1 H (k+n)

end coeff

end polynomial
