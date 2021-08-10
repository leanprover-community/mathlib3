/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.finset.nat_antidiagonal
import data.polynomial.basic

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
lemma coeff_add (p q : polynomial R) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n :=
by { rcases p, rcases q, simp [coeff, add_to_finsupp] }

@[simp] lemma coeff_smul [monoid S] [distrib_mul_action S R] (r : S) (p : polynomial R) (n : ℕ) :
  coeff (r • p) n = r • coeff p n :=
by { rcases p, simp [coeff, smul_to_finsupp] }

lemma support_smul [monoid S] [distrib_mul_action S R] (r : S) (p : polynomial R) :
  support (r • p) ⊆ support p :=
begin
  assume i hi,
  simp [mem_support_iff] at hi ⊢,
  contrapose! hi,
  simp [hi]
end

variable (R)
/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : polynomial R →ₗ[R] R :=
{ to_fun := λ p, coeff p n,
  map_add' := λ p q, coeff_add p q n,
  map_smul' := λ r p, coeff_smul r p n }

variable {R}

@[simp] lemma lcoeff_apply (n : ℕ) (f : polynomial R) : lcoeff R n f = coeff f n := rfl

@[simp] lemma finset_sum_coeff {ι : Type*} (s : finset ι) (f : ι → polynomial R) (n : ℕ) :
  coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
(lcoeff R n).map_sum

lemma coeff_sum [semiring S] (n : ℕ) (f : ℕ → R → polynomial S) :
  coeff (p.sum f) n = p.sum (λ a b, coeff (f a b) n) :=
by { rcases p, simp [polynomial.sum, support, coeff] }

/-- Decomposes the coefficient of the product `p * q` as a sum
over `nat.antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `finset.nat.sum_antidiagonal_eq_sum_range_succ`. -/
lemma coeff_mul (p q : polynomial R) (n : ℕ) :
  coeff (p * q) n = ∑ x in nat.antidiagonal n, coeff p x.1 * coeff q x.2 :=
begin
  rcases p, rcases q,
  simp only [coeff, mul_to_finsupp],
  exact add_monoid_algebra.mul_apply_antidiagonal p q n _ (λ x, nat.mem_antidiagonal)
end

@[simp] lemma mul_coeff_zero (p q : polynomial R) : coeff (p * q) 0 = coeff p 0 * coeff q 0 :=
by simp [coeff_mul]

lemma coeff_mul_X_zero (p : polynomial R) : coeff (p * X) 0 = 0 :=
by simp

lemma coeff_X_mul_zero (p : polynomial R) : coeff (X * p) 0 = 0 :=
by simp

lemma coeff_C_mul_X (x : R) (k n : ℕ) :
  coeff (C x * X^k : polynomial R) n = if n = k then x else 0 :=
by { rw [← monomial_eq_C_mul_X, coeff_monomial], congr' 1, simp [eq_comm] }

@[simp] lemma coeff_C_mul (p : polynomial R) : coeff (C a * p) n = a * coeff p n :=
by { rcases p, simp only [C, monomial, monomial_fun, mul_to_finsupp, ring_hom.coe_mk,
  coeff, add_monoid_algebra.single_zero_mul_apply p a n] }

lemma C_mul' (a : R) (f : polynomial R) : C a * f = a • f :=
by { ext, rw [coeff_C_mul, coeff_smul, smul_eq_mul] }

@[simp] lemma coeff_mul_C (p : polynomial R) (n : ℕ) (a : R) :
  coeff (p * C a) n = coeff p n * a :=
by { rcases p, simp only [C, monomial, monomial_fun, mul_to_finsupp, ring_hom.coe_mk,
  coeff, add_monoid_algebra.mul_single_zero_apply p a n] }

lemma coeff_X_pow (k n : ℕ) :
  coeff (X^k : polynomial R) n = if n = k then 1 else 0 :=
by simp only [one_mul, ring_hom.map_one, ← coeff_C_mul_X]

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

lemma coeff_mul_X_pow' (p : polynomial R) (n d : ℕ) :
  (p * X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 :=
begin
  split_ifs,
  { rw [←@nat.sub_add_cancel d n h, coeff_mul_X_pow, nat.add_sub_cancel] },
  { refine (coeff_mul _ _ _).trans (finset.sum_eq_zero (λ x hx, _)),
    rw [coeff_X_pow, if_neg, mul_zero],
    exact ne_of_lt (lt_of_le_of_lt (nat.le_of_add_le_right
      (le_of_eq (finset.nat.mem_antidiagonal.mp hx))) (not_le.mp h)) },
end

@[simp] theorem coeff_mul_X (p : polynomial R) (n : ℕ) :
  coeff (p * X) (n + 1) = coeff p n :=
by simpa only [pow_one] using coeff_mul_X_pow p 1 n

theorem mul_X_pow_eq_zero {p : polynomial R} {n : ℕ}
  (H : p * X ^ n = 0) : p = 0 :=
ext $ λ k, (coeff_mul_X_pow p n k).symm.trans $ ext_iff.1 H (k+n)

lemma C_mul_X_pow_eq_monomial (c : R) (n : ℕ) : C c * X^n = monomial n c :=
by { ext1, rw [monomial_eq_smul_X, coeff_smul, coeff_C_mul, smul_eq_mul] }

lemma support_mul_X_pow (c : R) (n : ℕ) (H : c ≠ 0) : (C c * X^n).support = singleton n :=
by rw [C_mul_X_pow_eq_monomial, support_monomial n c H]

lemma support_C_mul_X_pow' {c : R} {n : ℕ} : (C c * X^n).support ⊆ singleton n :=
by { rw [C_mul_X_pow_eq_monomial], exact support_monomial' n c }

lemma C_dvd_iff_dvd_coeff (r : R) (φ : polynomial R) :
  C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i :=
begin
  split,
  { rintros ⟨φ, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
  { intro h,
    choose c hc using h,
    classical,
    let c' : ℕ → R := λ i, if i ∈ φ.support then c i else 0,
    let ψ : polynomial R := ∑ i in φ.support, monomial i (c' i),
    use ψ,
    ext i,
    simp only [ψ, c', coeff_C_mul, mem_support_iff, coeff_monomial,
               finset_sum_coeff, finset.sum_ite_eq'],
    split_ifs with hi hi,
    { rw hc },
    { rw [not_not] at hi, rwa mul_zero } },
end

lemma coeff_bit0_mul (P Q : polynomial R) (n : ℕ) :
  coeff (bit0 P * Q) n = 2 * coeff (P * Q) n :=
by simp [bit0, add_mul]

lemma coeff_bit1_mul (P Q : polynomial R) (n : ℕ) :
  coeff (bit1 P * Q) n = 2 * coeff (P * Q) n + coeff Q n :=
by simp [bit1, add_mul, coeff_bit0_mul]

end coeff

section cast

@[simp] lemma nat_cast_coeff_zero {n : ℕ} {R : Type*} [semiring R] :
  (n : polynomial R).coeff 0 = n :=
begin
  induction n with n ih,
  { simp, },
  { simp [ih], },
end

@[simp, norm_cast] theorem nat_cast_inj
  {m n : ℕ} {R : Type*} [semiring R] [char_zero R] : (↑m : polynomial R) = ↑n ↔ m = n :=
begin
  fsplit,
  { intro h,
    apply_fun (λ p, p.coeff 0) at h,
    simpa using h, },
  { rintro rfl, refl, },
end

@[simp] lemma int_cast_coeff_zero {i : ℤ} {R : Type*} [ring R] :
  (i : polynomial R).coeff 0 = i :=
by cases i; simp

@[simp, norm_cast] theorem int_cast_inj
  {m n : ℤ} {R : Type*} [ring R] [char_zero R] : (↑m : polynomial R) = ↑n ↔ m = n :=
begin
  fsplit,
  { intro h,
    apply_fun (λ p, p.coeff 0) at h,
    simpa using h, },
  { rintro rfl, refl, },
end

end cast

end polynomial
