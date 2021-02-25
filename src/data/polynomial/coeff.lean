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

lemma mem_support_iff_coeff_ne_zero : n ∈ p.support ↔ p.coeff n ≠ 0 :=
by { rw mem_support_to_fun, refl }

lemma not_mem_support_iff_coeff_zero : n ∉ p.support ↔ p.coeff n = 0 :=
by { rw [mem_support_to_fun, not_not], refl, }

variable (R)
/-- The nth coefficient, as a linear map. -/
def lcoeff (n : ℕ) : polynomial R →ₗ[R] R :=
finsupp.lapply n
variable {R}

@[simp] lemma lcoeff_apply (n : ℕ) (f : polynomial R) : lcoeff R n f = coeff f n := rfl

@[simp] lemma finset_sum_coeff {ι : Type*} (s : finset ι) (f : ι → polynomial R) (n : ℕ) :
  coeff (∑ b in s, f b) n = ∑ b in s, coeff (f b) n :=
(s.sum_hom (λ q : polynomial R, lcoeff R n q)).symm

/-- Decomposes the coefficient of the product `p * q` as a sum
over `nat.antidiagonal`. A version which sums over `range (n + 1)` can be obtained
by using `finset.nat.sum_antidiagonal_eq_sum_range_succ`. -/
lemma coeff_mul (p q : polynomial R) (n : ℕ) :
  coeff (p * q) n = ∑ x in nat.antidiagonal n, coeff p x.1 * coeff q x.2 :=
add_monoid_algebra.mul_apply_antidiagonal p q n _ (λ x, nat.mem_antidiagonal)

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
add_monoid_algebra.single_zero_mul_apply p a n

lemma C_mul' (a : R) (f : polynomial R) : C a * f = a • f :=
ext $ λ n, coeff_C_mul f

lemma smul_mul_smul {R : Type*} [comm_semiring R] (r s : R) (p q : polynomial R) :
  (r • p) * (s • q) = (r * s) • (p * q) :=
by rw [←C_mul', ←C_mul', ←C_mul', C_mul, ←mul_assoc,
  mul_assoc (C r), mul_comm p, ←mul_assoc, ←mul_assoc]

@[simp] lemma coeff_mul_C (p : polynomial R) (n : ℕ) (a : R) :
  coeff (p * C a) n = coeff p n * a :=
add_monoid_algebra.mul_single_zero_apply p a n

lemma coeff_X_pow (k n : ℕ) :
  coeff (X^k : polynomial R) n = if n = k then 1 else 0 :=
by { simp only [X_pow_eq_monomial, monomial, single, eq_comm], congr }

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

lemma C_mul_X_pow_eq_monomial (c : R) (n : ℕ) : C c * X^n = monomial n c :=
by { ext1, rw [monomial_eq_smul_X, coeff_smul, coeff_C_mul] }

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

end coeff

open submodule polynomial set

variables {f : polynomial R} {I : submodule (polynomial R) (polynomial R)}

/--  If the coefficients of a polynomial belong to n ideal contains the submodule span of the
coefficients of a polynomial. -/
lemma span_le_of_coeff_mem_C_inverse (cf : ∀ (i : ℕ), f.coeff i ∈ (C ⁻¹' I.carrier)) :
  (span (polynomial R) {g | ∃ i, g = C (f.coeff i)}) ≤ I :=
begin
  refine bInter_subset_of_mem _,
  rintros _ ⟨i, rfl⟩,
  exact (mem_coe _).mpr (cf i),
end

lemma mem_span_C_coeff :
  f ∈ span (polynomial R) {g : polynomial R | ∃ i : ℕ, g = (C (coeff f i))} :=
begin
  rw [← f.sum_single] {occs := occurrences.pos [1]},
  refine sum_mem _ (λ i hi, _),
  change monomial i _ ∈ span _ _,
  rw [← C_mul_X_pow_eq_monomial, ← X_pow_mul],
  exact smul_mem _ _ (subset_span ⟨i, rfl⟩),
end

lemma exists_coeff_not_mem_C_inverse :
  f ∉ I → ∃ i : ℕ , coeff f i ∉ (C ⁻¹'  I.carrier) :=
imp_of_not_imp_not _ _
  (λ cf, not_not.mpr ((span_le_of_coeff_mem_C_inverse (not_exists_not.mp cf)) mem_span_C_coeff))

end polynomial
