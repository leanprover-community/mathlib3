/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.algebra_map
import data.polynomial.denoms_clearable

/-!  # Laurent polynomials

Following a suggestion by Eric, they are defined via `add_monoid_algebra R ℤ`.
Thus, they are essentially `finsupp`s `ℤ →₀ R `.

This means that they play well with polynomials, but there is a little roughness in establishing
the API, since the `finsupp` implementation of `polynomial R` is well-shielded.

## Notation
The symbol `R[T;T⁻¹]` stands for `laurent_polynomial R`.

## Implementation notes
* `C : R →+* R[T;T⁻¹]` is the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` is the sequence of powers of the variable `T`.
Unlike the case of polynomials, I felt that the exponent notation was not too easy to use, as only
natural exponents would be allowed.  Moreover, in the end, it seems likely that we should aim to
performing computations on exponents in `ℤ` anyway and separating this via the symbol `T` seems
convenient.

I made some *heavy* use of `simp` lemmas, aiming to bring Laurent polynomials to the form
`C a * T n`.  Any comments or suggestions for improvements is greatly appreciated!

##  Future work
Lots is missing!  I would certainly like to show that `R[T;T⁻¹]` is the localization of `R[X]`
inverting `X`.  This should be mostly in place, given `exists_X_pow`.
-/

open_locale polynomial big_operators
open polynomial add_monoid_algebra multiplicative
noncomputable theory

variables {R N Z : Type*}

/--  The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials. -/
abbreviation laurent_polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℤ

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R

/--  The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def polynomial.to_laurent_polynomial {R : Type*} [semiring R] :
  R[X] →+* R[T;T⁻¹] :=
begin
  refine ring_hom.comp _ (to_finsupp_iso R).to_ring_hom,
  exact (add_monoid_algebra.add_monoid_ring_hom_map R (nat.cast_add_monoid_hom ℤ)),
end

/--  The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def polynomial.to_laurent_polynomial_alg {R : Type*} [comm_semiring R] :
  R[X] →ₐ[R] R[T;T⁻¹] :=
begin
  refine alg_hom.comp _ (to_finsupp_iso_alg R).to_alg_hom,
  exact (add_monoid_algebra.add_monoid_alg_hom_map R (nat.cast_add_monoid_hom ℤ)),
end

namespace laurent_polynomial

section semiring
variables [semiring R]

lemma single_zero_one_eq_one : (finsupp.single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) := rfl

/-!  ### The functions `C` and `T`. -/
/--  The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[T;T⁻¹] :=
{ to_fun    := finsupp.single 0,
  map_one'  := rfl,
  map_mul'  := λ x y, by simp only [add_monoid_algebra.single_mul_single, add_zero],
  map_zero' := finsupp.single_zero,
  map_add'  := λ x y, finsupp.single_add }

lemma single_eq_C (r : R) : finsupp.single 0 r = C r := rfl

/--  The variable of the ring of Laurent polynomials. -/
def T' : R[T;T⁻¹] := finsupp.single 1 1

/--  The function `n ↦ T ^ n`, implemented as a sequence `ℤ ↦ R[T;T⁻¹]`. -/
def T (n : ℤ) : R[T;T⁻¹] := finsupp.single n 1

@[simp]
lemma T_zero : (T 0 : R[T;T⁻¹]) = 1 := rfl

lemma T_add (m n : ℤ) : (T (m + n) : R[T;T⁻¹]) = T m * T n :=
by {convert single_mul_single.symm, simp [T] }

@[simp]
lemma T_pow (m : ℤ) (n : ℕ) : (T m ^ n : R[T;T⁻¹]) = T (n * m) :=
by rw [T, T, single_pow n, one_pow, nsmul_eq_mul, int.nat_cast_eq_coe_nat]

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
lemma mul_T_assoc (f : R[T;T⁻¹]) (m n : ℤ) : f * T m * T n = f * T (m + n) :=
by simp [← T_add, mul_assoc]

@[simp]
lemma single_eq_C_mul_T (r : R) (n : ℤ) :
  (finsupp.single n r : R[T;T⁻¹]) = (C r * T n : R[T;T⁻¹]) :=
by convert add_monoid_algebra.single_mul_single.symm; simp

-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `C a * T n`, whenever it can be reached.
@[simp]
lemma monomial_eq_C_mul_T (n : ℕ) (r : R) :
  ((polynomial.monomial n r).to_laurent_polynomial : R[T;T⁻¹]) = C r * T n :=
begin
  show finsupp.map_domain (nat.cast_add_monoid_hom ℤ) ((to_finsupp_iso R) (monomial n r)) =
    (C r * T n : R[T;T⁻¹]),
  convert (finsupp.map_domain_single : _ = finsupp.single (nat.cast_add_monoid_hom ℤ n) r),
  { exact to_finsupp_monomial n r },
  { simp only [nat.coe_cast_add_monoid_hom, int.nat_cast_eq_coe_nat, single_eq_C_mul_T] },
end

@[simp]
lemma C_eq_C (r : R) :
  (polynomial.C r).to_laurent_polynomial = C r :=
begin
  convert monomial_eq_C_mul_T 0 r,
  simp only [int.coe_nat_zero, T_zero, mul_one],
end

@[simp]
lemma X_eq_T :
  (polynomial.X.to_laurent_polynomial : R[T;T⁻¹]) = T 1 :=
begin
  have : (polynomial.X : R[X]) = monomial 1 1,
  { simp [monomial_eq_C_mul_X] },
  simp [this, monomial_eq_C_mul_T],
end

@[simp] lemma polynomial_one_eq_one : (polynomial.to_laurent_polynomial : R[X] → R[T;T⁻¹]) 1 = 1 :=
C_eq_C (1 : R)

@[simp]
lemma polynomial_C_mul_eq (r : R) (f : R[X]):
  (polynomial.C r * f).to_laurent_polynomial = C r * f.to_laurent_polynomial :=
by simp only [_root_.map_mul, C_eq_C]

@[simp]
lemma X_pow_eq_T (n : ℕ) :
  (X ^ n : R[X]).to_laurent_polynomial = T n :=
by simp only [map_pow, X_eq_T, T_pow, mul_one]

@[simp]
lemma C_mul_X_pow (n : ℕ) (r : R) :
  (polynomial.C r * X ^ n).to_laurent_polynomial = C r * T n :=
by simp only [_root_.map_mul, C_eq_C, X_pow_eq_T]

lemma is_unit_T (n : ℤ) : is_unit (T n : R[T;T⁻¹]) :=
by refine ⟨⟨T n, T (- n), _, _⟩, _⟩; simp [← T_add]

lemma is_regular_T (n : ℤ) : is_regular (T n : R[T;T⁻¹]) :=
⟨is_left_regular_of_mul_eq_one (by simp [← T_add] : T (-n) * T n = 1),
  is_right_regular_of_mul_eq_one (by simp [← T_add] : T n * T (-n) = 1)⟩

@[elab_as_eliminator] protected lemma induction_on {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
  (h_C         : ∀ a, M (C a))
  (h_add       : ∀ {p q}, M p → M q → M (p + q))
  (h_C_mul_T   : ∀ (n : ℕ) (a : R), M (C a * T n) → M (C a * T (n + 1)))
  (h_C_mul_T_Z : ∀ (n : ℕ) (a : R), M (C a * T (- n)) → M (C a * T (- n - 1))) :
  M p :=
begin
  have A : ∀ {n : ℤ} {a : R}, M (C a * T n),
  { assume n a,
    apply n.induction_on,
    { simpa only [T_zero, mul_one] using h_C a },
    { exact λ m, h_C_mul_T m a },
    { exact λ m, h_C_mul_T_Z m a } },
  have B : ∀ (s : finset ℤ), M (s.sum (λ (n : ℤ), C (p.to_fun n) * T n)),
  { apply finset.induction,
    { convert h_C 0, simp only [finset.sum_empty, _root_.map_zero] },
    { assume n s ns ih, rw finset.sum_insert ns,
    { exact h_add A ih } } },
  convert B p.support,
  ext a,
  simp_rw [← single_eq_C_mul_T, finset.sum_apply', finsupp.single_apply, finset.sum_ite_eq'],
  split_ifs with h h,
  { refl },
  { exact finsupp.not_mem_support_iff.mp h }
end

/--  To prove something about Laurent polynomials, it suffices to show that
* the condition is closed under taking sums, and
* it holds for monomials.
-/
@[elab_as_eliminator] protected lemma induction_on' {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
  (h_add     : ∀p q, M p → M q → M (p + q))
  (h_C_mul_T : ∀(n : ℤ) (a : R), M (C a * T n)) :
  M p :=
begin
  refine p.induction_on (λ a, _) h_add _ _;
  try { exact λ n f Mf, h_C_mul_T _ f },
  convert h_C_mul_T 0 a,
  exact (mul_one _).symm,
end

lemma commute_T (n : ℤ) (f : R[T;T⁻¹]) : commute (T n) f :=
f.induction_on' (λ p q Tp Tq, commute.add_right Tp Tq) $ λ m a,
show T n * _ = _, by
{ rw [T, T, ← single_eq_C, single_mul_single, single_mul_single, single_mul_single],
  simp [add_comm] }

@[simp]
lemma T_mul (n : ℤ) (f : R[T;T⁻¹]) : T n * f = f * T n :=
(commute_T n f).eq

lemma exists_X_pow (f : R[T;T⁻¹]) : ∃ (n : ℕ) (f' : R[X]), f'.to_laurent_polynomial = f * T n :=
begin
  apply f.induction_on' _ (λ n a, _); clear f,
  { rintros f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩,
    by_cases h : m ≤ n;
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, _⟩;
    simp only [hf, hg, add_mul, add_comm (n : ℤ), int.coe_nat_add, _root_.map_add,
      _root_.map_mul, map_pow, X_eq_T, T_pow, mul_one, mul_T_assoc]  },
  { cases n with n n,
    { exact ⟨0, polynomial.C a * X ^ n, by simp⟩ },
    { refine ⟨n + 1, polynomial.C a, _⟩,
      simp only [int.neg_succ_of_nat_eq, neg_add_self, int.coe_nat_succ, mul_T_assoc, T_zero,
        mul_one, C_eq_C] } }
end

lemma exists_X_pow_T' (f : R[T;T⁻¹]) :
  ∃ (n : ℕ) (f' : R[X]), f'.to_laurent_polynomial = f * T' ^ n :=
begin
  rcases exists_X_pow f with ⟨n, f', hf⟩,
  refine ⟨n, f', _⟩,
  rwa [T', ← T, T_pow, mul_one],
end

/--  This version of `exists_X_pow` can be called as `rcases f.exists_X_pow' with ⟨n, f', rfl⟩`. -/
lemma exists_X_pow' (f : R[T;T⁻¹]) : ∃ (n : ℤ) (f' : R[X]),
  f = f'.to_laurent_polynomial * T n :=
begin
  rcases f.exists_X_pow with ⟨n, f', hf⟩,
  exact ⟨(- n), f', by simp [hf]⟩,
end

/--  Suppose that `Q` is a statement about Laurent polynomials such that
* `Q` is true on ~~Laurent~~ polynomials;
* `Q (f * T)` implies `Q f`;

is true on all Laurent polynomials. -/
lemma proprop (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
  (PQ : ∀ (f : R[X]), Q f.to_laurent_polynomial)
  (Tn : ∀ f, Q (f * T 1) → Q f) :
  Q f :=
begin
  rcases f.exists_X_pow' with ⟨n, f', rfl⟩,
  cases n with n n,
  { simpa using PQ (f' * X ^ n) },
  { induction n with n hn,
    { refine Tn _ _,
      simpa [int.neg_succ_of_nat_eq] using PQ f' },
    { convert Tn _ _,
      simpa using hn } }
end

instance : module R[X] R[T;T⁻¹] :=
{ smul      := λ f l, f.to_laurent_polynomial * l,
  one_smul  := λ f, by simp only [polynomial_one_eq_one, one_mul],
  mul_smul  := λ f g l, by simp only [mul_assoc, _root_.map_mul],
  smul_add  := λ f x y, by simp only [mul_add],
  smul_zero := λ f, by simp only [mul_zero],
  add_smul  := λ f g x, by simp only [add_mul, _root_.map_add],
  zero_smul := λ f, by simp only [_root_.map_zero, zero_mul] }

end semiring

/-
section comm_semiring
variable [comm_semiring R]

instance : algebra R[X] R[T;T⁻¹] :=
{ commutes' := λ f l, by simp [mul_comm],
  smul_def' := λ f l, rfl,
  .. ((add_monoid_alg_hom_map R (nat.cast_add_monoid_hom ℤ)).to_ring_hom.comp
    (to_finsupp_iso R).to_ring_hom : R[X] →+* R[T;T⁻¹]) }

end comm_semiring
-/

end laurent_polynomial
