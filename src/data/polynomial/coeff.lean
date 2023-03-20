/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/

import data.polynomial.basic
import data.finset.nat_antidiagonal
import data.nat.choose.sum

/-!
# Theory of univariate polynomials

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

The theorems include formulas for computing coefficients, such as
`coeff_add`, `coeff_sum`, `coeff_mul`

-/

noncomputable theory

open finsupp finset add_monoid_algebra
open_locale big_operators polynomial

namespace polynomial
universes u v
variables {R : Type u} {S : Type v} {a b : R} {n m : ℕ}

variables [semiring R] {p q r : R[X]}

section coeff

lemma coeff_one (n : ℕ) : coeff (1 : R[X]) n = if 0 = n then 1 else 0 :=
coeff_monomial

@[simp]
lemma coeff_add (p q : R[X]) (n : ℕ) : coeff (p + q) n = coeff p n + coeff q n :=
by { rcases p, rcases q, simp_rw [←of_finsupp_add, coeff], exact finsupp.add_apply _ _ _ }

@[simp] lemma coeff_bit0 (p : R[X]) (n : ℕ) : coeff (bit0 p) n = bit0 (coeff p n) := by simp [bit0]

@[simp] lemma coeff_smul [monoid S] [distrib_mul_action S R] (r : S) (p : R[X]) (n : ℕ) :
  coeff (r • p) n = r • coeff p n :=
by { rcases p, simp_rw [←of_finsupp_smul, coeff], exact finsupp.smul_apply _ _ _ }

lemma support_smul [monoid S] [distrib_mul_action S R] (r : S) (p : R[X]) :
  support (r • p) ⊆ support p :=
begin
  assume i hi,
  simp [mem_support_iff] at hi ⊢,
  contrapose! hi,
  simp [hi]
end

/-- `polynomial.sum` as a linear map. -/
@[simps] def lsum {R A M : Type*} [semiring R] [semiring A] [add_comm_monoid M]
  [module R A] [module R M] (f : ℕ → A →ₗ[R] M) :
  A[X] →ₗ[R] M :=
{ to_fun := λ p, p.sum (λ n r, f n r),
  map_add' := λ p q, sum_add_index p q _ (λ n, (f n).map_zero) (λ n _ _, (f n).map_add _ _),
  map_smul' := λ c p,
  begin
    rw [sum_eq_of_subset _ (λ n r, f n r) (λ n, (f n).map_zero) _ (support_smul c p)],
    simp only [sum_def, finset.smul_sum, coeff_smul, linear_map.map_smul, ring_hom.id_apply]
  end }

variable (R)
/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : R[X] →ₗ[R] R :=
{ to_fun := λ p, coeff p n,
  map_add' := λ p q, coeff_add p q n,
  map_smul' := λ r p, coeff_smul r p n }

variable {R}

@[simp] lemma lcoeff_apply (n : ℕ) (f : R[X]) : lcoeff R n f = coeff f n := rfl

@[simp] lemma finset_sum_coeff {ι : Type*} (s : finset ι) (f : ι → R[X]) (n : ℕ) :
  coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
(lcoeff R n).map_sum

lemma coeff_sum [semiring S] (n : ℕ) (f : ℕ → R → S[X]) :
  coeff (p.sum f) n = p.sum (λ a b, coeff (f a b) n) :=
by { rcases p, simp [polynomial.sum, support, coeff] }

/-- Decomposes the coefficient of the product `p * q` as a sum
over `nat.antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `finset.nat.sum_antidiagonal_eq_sum_range_succ`. -/
lemma coeff_mul (p q : R[X]) (n : ℕ) :
  coeff (p * q) n = ∑ x in nat.antidiagonal n, coeff p x.1 * coeff q x.2 :=
begin
  rcases p, rcases q,
  simp_rw [←of_finsupp_mul, coeff],
  exact add_monoid_algebra.mul_apply_antidiagonal p q n _ (λ x, nat.mem_antidiagonal)
end

@[simp] lemma mul_coeff_zero (p q : R[X]) : coeff (p * q) 0 = coeff p 0 * coeff q 0 :=
by simp [coeff_mul]

/-- `constant_coeff p` returns the constant term of the polynomial `p`,
  defined as `coeff p 0`. This is a ring homomorphism. -/
@[simps] def constant_coeff : R[X] →+* R :=
{ to_fun := λ p, coeff p 0,
  map_one' := coeff_one_zero,
  map_mul' := mul_coeff_zero,
  map_zero' := coeff_zero 0,
  map_add' :=  λ p q, coeff_add p q 0 }

lemma is_unit_C {x : R} : is_unit (C x) ↔ is_unit x :=
⟨λ h, (congr_arg is_unit coeff_C_zero).mp (h.map $ @constant_coeff R _), λ h, h.map C⟩

lemma coeff_mul_X_zero (p : R[X]) : coeff (p * X) 0 = 0 := by simp

lemma coeff_X_mul_zero (p : R[X]) : coeff (X * p) 0 = 0 := by simp

lemma coeff_C_mul_X_pow (x : R) (k n : ℕ) : coeff (C x * X ^ k : R[X]) n = if n = k then x else 0 :=
by { rw [C_mul_X_pow_eq_monomial, coeff_monomial], congr' 1, simp [eq_comm] }

lemma coeff_C_mul_X (x : R) (n : ℕ) : coeff (C x * X : R[X]) n = if n = 1 then x else 0 :=
by rw [← pow_one X, coeff_C_mul_X_pow]

@[simp] lemma coeff_C_mul (p : R[X]) : coeff (C a * p) n = a * coeff p n :=
begin
  rcases p,
  simp_rw [←monomial_zero_left, ←of_finsupp_single, ←of_finsupp_mul, coeff],
  exact add_monoid_algebra.single_zero_mul_apply p a n
end

lemma C_mul' (a : R) (f : R[X]) : C a * f = a • f :=
by { ext, rw [coeff_C_mul, coeff_smul, smul_eq_mul] }

@[simp] lemma coeff_mul_C (p : R[X]) (n : ℕ) (a : R) :
  coeff (p * C a) n = coeff p n * a :=
begin
  rcases p,
  simp_rw [←monomial_zero_left, ←of_finsupp_single, ←of_finsupp_mul, coeff],
  exact add_monoid_algebra.mul_single_zero_apply p a n
end

lemma coeff_X_pow (k n : ℕ) :
  coeff (X^k : R[X]) n = if n = k then 1 else 0 :=
by simp only [one_mul, ring_hom.map_one, ← coeff_C_mul_X_pow]

@[simp]
lemma coeff_X_pow_self (n : ℕ) :
  coeff (X^n : R[X]) n = 1 :=
by simp [coeff_X_pow]

section fewnomials

open finset

lemma support_binomial {k m : ℕ} (hkm : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
  (C x * X ^ k + C y * X ^ m).support = {k, m} :=
begin
  apply subset_antisymm (support_binomial' k m x y),
  simp_rw [insert_subset, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm, if_neg hkm.symm,
    mul_zero, zero_add, add_zero, ne.def, hx, hy, and_self, not_false_iff],
end

lemma support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
  (hy : y ≠ 0) (hz : z ≠ 0) : (C x * X ^ k + C y * X ^ m + C z * X ^ n).support = {k, m, n} :=
begin
  apply subset_antisymm (support_trinomial' k m n x y z),
  simp_rw [insert_subset, singleton_subset_iff, mem_support_iff, coeff_add, coeff_C_mul,
    coeff_X_pow_self, mul_one, coeff_X_pow, if_neg hkm.ne, if_neg hkm.ne', if_neg hmn.ne,
    if_neg hmn.ne', if_neg (hkm.trans hmn).ne, if_neg (hkm.trans hmn).ne',
    mul_zero, add_zero, zero_add, ne.def, hx, hy, hz, and_self, not_false_iff],
end

lemma card_support_binomial {k m : ℕ} (h : k ≠ m) {x y : R} (hx : x ≠ 0) (hy : y ≠ 0) :
  (C x * X ^ k + C y * X ^ m).support.card = 2 :=
by rw [support_binomial h hx hy, card_insert_of_not_mem (mt mem_singleton.mp h), card_singleton]

lemma card_support_trinomial {k m n : ℕ} (hkm : k < m) (hmn : m < n) {x y z : R} (hx : x ≠ 0)
  (hy : y ≠ 0) (hz : z ≠ 0) : (C x * X ^ k + C y * X ^ m + C z * X ^ n).support.card = 3 :=
by rw [support_trinomial hkm hmn hx hy hz, card_insert_of_not_mem
  (mt mem_insert.mp (not_or hkm.ne (mt mem_singleton.mp (hkm.trans hmn).ne))),
  card_insert_of_not_mem (mt mem_singleton.mp hmn.ne), card_singleton]

end fewnomials

@[simp]
theorem coeff_mul_X_pow (p : R[X]) (n d : ℕ) :
  coeff (p * polynomial.X ^ n) (d + n) = coeff p d :=
begin
  rw [coeff_mul, sum_eq_single (d,n), coeff_X_pow, if_pos rfl, mul_one],
  { rintros ⟨i,j⟩ h1 h2, rw [coeff_X_pow, if_neg, mul_zero], rintro rfl, apply h2,
    rw [nat.mem_antidiagonal, add_right_cancel_iff] at h1, subst h1 },
  { exact λ h1, (h1 (nat.mem_antidiagonal.2 rfl)).elim }
end

@[simp]
theorem coeff_X_pow_mul (p : R[X]) (n d : ℕ) :
  coeff (polynomial.X ^ n * p) (d + n) = coeff p d :=
by rw [(commute_X_pow p n).eq, coeff_mul_X_pow]

lemma coeff_mul_X_pow' (p : R[X]) (n d : ℕ) :
  (p * X ^ n).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 :=
begin
  split_ifs,
  { rw [← tsub_add_cancel_of_le h, coeff_mul_X_pow, add_tsub_cancel_right] },
  { refine (coeff_mul _ _ _).trans (finset.sum_eq_zero (λ x hx, _)),
    rw [coeff_X_pow, if_neg, mul_zero],
    exact ((le_of_add_le_right (finset.nat.mem_antidiagonal.mp hx).le).trans_lt $ not_le.mp h).ne }
end

lemma coeff_X_pow_mul' (p : R[X]) (n d : ℕ) :
  (X ^ n * p).coeff d = ite (n ≤ d) (p.coeff (d - n)) 0 :=
by rw [(commute_X_pow p n).eq, coeff_mul_X_pow']

@[simp] theorem coeff_mul_X (p : R[X]) (n : ℕ) :
  coeff (p * X) (n + 1) = coeff p n :=
by simpa only [pow_one] using coeff_mul_X_pow p 1 n

@[simp] theorem coeff_X_mul (p : R[X]) (n : ℕ) :
  coeff (X * p) (n + 1) = coeff p n := by rw [(commute_X p).eq, coeff_mul_X]

theorem coeff_mul_monomial (p : R[X]) (n d : ℕ) (r : R) :
  coeff (p * monomial n r) (d + n) = coeff p d * r :=
by rw [← C_mul_X_pow_eq_monomial, ←X_pow_mul, ←mul_assoc, coeff_mul_C, coeff_mul_X_pow]

theorem coeff_monomial_mul (p : R[X]) (n d : ℕ) (r : R) :
  coeff (monomial n r * p) (d + n) = r * coeff p d :=
by rw [← C_mul_X_pow_eq_monomial, mul_assoc, coeff_C_mul, X_pow_mul, coeff_mul_X_pow]

-- This can already be proved by `simp`.
theorem coeff_mul_monomial_zero (p : R[X]) (d : ℕ) (r : R) :
  coeff (p * monomial 0 r) d = coeff p d * r :=
coeff_mul_monomial p 0 d r

-- This can already be proved by `simp`.
theorem coeff_monomial_zero_mul (p : R[X]) (d : ℕ) (r : R) :
  coeff (monomial 0 r * p) d = r * coeff p d :=
coeff_monomial_mul p 0 d r

theorem mul_X_pow_eq_zero {p : R[X]} {n : ℕ}
  (H : p * X ^ n = 0) : p = 0 :=
ext $ λ k, (coeff_mul_X_pow p n k).symm.trans $ ext_iff.1 H (k+n)

lemma mul_X_pow_injective (n : ℕ) : function.injective (λ P : R[X], X ^ n * P) :=
begin
  intros P Q hPQ,
  simp only at hPQ,
  ext i,
  rw [← coeff_X_pow_mul P n i, hPQ, coeff_X_pow_mul Q n i]
end

lemma mul_X_injective : function.injective (λ P : R[X], X * P) :=
pow_one (X : R[X]) ▸ mul_X_pow_injective 1

lemma coeff_X_add_C_pow (r : R) (n k : ℕ) :
  ((X + C r) ^ n).coeff k = r ^ (n - k) * (n.choose k : R) :=
begin
  rw [(commute_X (C r : R[X])).add_pow, ← lcoeff_apply, linear_map.map_sum],
  simp only [one_pow, mul_one, lcoeff_apply, ← C_eq_nat_cast, ←C_pow, coeff_mul_C, nat.cast_id],
  rw [finset.sum_eq_single k, coeff_X_pow_self, one_mul],
  { intros _ _ h,
    simp [coeff_X_pow, h.symm] },
  { simp only [coeff_X_pow_self, one_mul, not_lt, finset.mem_range],
    intro h, rw [nat.choose_eq_zero_of_lt h, nat.cast_zero, mul_zero] }
end

lemma coeff_X_add_one_pow (R : Type*) [semiring R] (n k : ℕ) :
  ((X + 1) ^ n).coeff k = (n.choose k : R) :=
by rw [←C_1, coeff_X_add_C_pow, one_pow, one_mul]

lemma coeff_one_add_X_pow (R : Type*) [semiring R] (n k : ℕ) :
  ((1 + X) ^ n).coeff k = (n.choose k : R) :=
by rw [add_comm _ X, coeff_X_add_one_pow]

lemma C_dvd_iff_dvd_coeff (r : R) (φ : R[X]) :
  C r ∣ φ ↔ ∀ i, r ∣ φ.coeff i :=
begin
  split,
  { rintros ⟨φ, rfl⟩ c, rw coeff_C_mul, apply dvd_mul_right },
  { intro h,
    choose c hc using h,
    classical,
    let c' : ℕ → R := λ i, if i ∈ φ.support then c i else 0,
    let ψ : R[X] := ∑ i in φ.support, monomial i (c' i),
    use ψ,
    ext i,
    simp only [ψ, c', coeff_C_mul, mem_support_iff, coeff_monomial,
               finset_sum_coeff, finset.sum_ite_eq'],
    split_ifs with hi hi,
    { rw hc },
    { rw [not_not] at hi, rwa mul_zero } },
end

lemma coeff_bit0_mul (P Q : R[X]) (n : ℕ) :
  coeff (bit0 P * Q) n = 2 * coeff (P * Q) n :=
by simp [bit0, add_mul]

lemma coeff_bit1_mul (P Q : R[X]) (n : ℕ) :
  coeff (bit1 P * Q) n = 2 * coeff (P * Q) n + coeff Q n :=
by simp [bit1, add_mul, coeff_bit0_mul]

lemma smul_eq_C_mul (a : R) : a • p = C a * p := by simp [ext_iff]

lemma update_eq_add_sub_coeff {R : Type*} [ring R] (p : R[X]) (n : ℕ) (a : R) :
  p.update n a = p + (polynomial.C (a - p.coeff n) * polynomial.X ^ n) :=
begin
  ext,
  rw [coeff_update_apply, coeff_add, coeff_C_mul_X_pow],
  split_ifs with h;
  simp [h]
end

end coeff

section cast

@[simp] lemma nat_cast_coeff_zero {n : ℕ} {R : Type*} [semiring R] :
  (n : R[X]).coeff 0 = n :=
begin
  induction n with n ih,
  { simp, },
  { simp [ih], },
end

@[simp, norm_cast] theorem nat_cast_inj
  {m n : ℕ} {R : Type*} [semiring R] [char_zero R] : (↑m : R[X]) = ↑n ↔ m = n :=
begin
  fsplit,
  { intro h,
    apply_fun (λ p, p.coeff 0) at h,
    simpa using h, },
  { rintro rfl, refl, },
end

@[simp] lemma int_cast_coeff_zero {i : ℤ} {R : Type*} [ring R] :
  (i : R[X]).coeff 0 = i :=
by cases i; simp

@[simp, norm_cast] theorem int_cast_inj
  {m n : ℤ} {R : Type*} [ring R] [char_zero R] : (↑m : R[X]) = ↑n ↔ m = n :=
begin
  fsplit,
  { intro h,
    apply_fun (λ p, p.coeff 0) at h,
    simpa using h, },
  { rintro rfl, refl, },
end

end cast

instance [char_zero R] : char_zero R[X] :=
{ cast_injective := λ x y, nat_cast_inj.mp }

end polynomial
