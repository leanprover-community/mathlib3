/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.algebra_map

/-!  # Laurent polynomials

Following a suggestion by Eric, Laurent polynomials are defined via `add_monoid_algebra R ℤ`.
Thus, they are essentially `finsupp`s `ℤ →₀ R`.

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
inverting `X`.  This should be mostly in place, given `exists_T_pow`.
-/

open_locale polynomial big_operators
open polynomial add_monoid_algebra finsupp
noncomputable theory

variables {R N Z : Type*}

/--  The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials. -/
abbreviation laurent_polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℤ

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R

/--  The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def polynomial.to_laurent [semiring R] :
  R[X] →+* R[T;T⁻¹] :=
begin
  refine ring_hom.comp _ (to_finsupp_iso R).to_ring_hom,
  exact (map_domain_ring_hom R (nat.cast_add_monoid_hom ℤ)),
end

/--  The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def polynomial.to_laurent_alg [comm_semiring R] :
  R[X] →ₐ[R] R[T;T⁻¹] :=
begin
  refine alg_hom.comp _ (to_finsupp_iso_alg R).to_alg_hom,
  exact (map_domain_alg_hom R R (nat.cast_add_monoid_hom ℤ)),
end

namespace laurent_polynomial

section semiring
variables [semiring R]

lemma single_zero_one_eq_one : (single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) := rfl

/-!  ### The functions `C` and `T`. -/
/--  The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[T;T⁻¹] :=
add_monoid_algebra.single_zero_ring_hom

lemma single_eq_C (r : R) : single 0 r = C r := rfl

/--  The function `n ↦ T ^ n`, implemented as a sequence `ℤ → R[T;T⁻¹]`.

Using directly `T ^ n` does not work, since we want the exponents to be of Type `ℤ` and there
is no `ℤ`-power defined on `R[T;T⁻¹]`.  Using that `T` is a unit introduces extra coercions.
For these reasons, the definition of `T` is as a sequence. -/
def T (n : ℤ) : R[T;T⁻¹] := single n 1

@[simp]
lemma T_zero : (T 0 : R[T;T⁻¹]) = 1 := rfl

lemma T_add (m n : ℤ) : (T (m + n) : R[T;T⁻¹]) = T m * T n :=
by { convert single_mul_single.symm, simp [T] }

@[simp]
lemma T_pow (m : ℤ) (n : ℕ) : (T m ^ n : R[T;T⁻¹]) = T (n * m) :=
by rw [T, T, single_pow n, one_pow, nsmul_eq_mul, int.nat_cast_eq_coe_nat]

/-- The `simp` version of `mul_assoc`, in the presence of `T`'s. -/
@[simp]
lemma mul_T_assoc (f : R[T;T⁻¹]) (m n : ℤ) : f * T m * T n = f * T (m + n) :=
by simp [← T_add, mul_assoc]

@[simp]
lemma single_eq_C_mul_T (r : R) (n : ℤ) :
  (single n r : R[T;T⁻¹]) = (C r * T n : R[T;T⁻¹]) :=
by convert single_mul_single.symm; simp

-- This lemma locks in the right changes and is what Lean proved directly.
-- The actual `simp`-normal form of a Laurent monomial is `C a * T n`, whenever it can be reached.
@[simp]
lemma _root_.polynomial.to_laurent_C_mul_T (n : ℕ) (r : R) :
  ((polynomial.monomial n r).to_laurent : R[T;T⁻¹]) = C r * T n :=
begin
  show map_domain (nat.cast_add_monoid_hom ℤ) ((to_finsupp_iso R) (monomial n r)) =
    (C r * T n : R[T;T⁻¹]),
  convert (map_domain_single : _ = single (nat.cast_add_monoid_hom ℤ n) r),
  { exact to_finsupp_monomial n r },
  { simp only [nat.coe_cast_add_monoid_hom, int.nat_cast_eq_coe_nat, single_eq_C_mul_T] },
end

@[simp]
lemma _root_.polynomial.to_laurent_C (r : R) :
  (polynomial.C r).to_laurent = C r :=
begin
  convert polynomial.to_laurent_C_mul_T 0 r,
  simp only [int.coe_nat_zero, T_zero, mul_one],
end

@[simp]
lemma _root_.polynomial.to_laurent_X :
  (polynomial.X.to_laurent : R[T;T⁻¹]) = T 1 :=
begin
  have : (polynomial.X : R[X]) = monomial 1 1,
  { simp [monomial_eq_C_mul_X] },
  simp [this, polynomial.to_laurent_C_mul_T],
end

@[simp] lemma _root_.polynomial.to_laurent_one : (polynomial.to_laurent : R[X] → R[T;T⁻¹]) 1 = 1 :=
map_one polynomial.to_laurent

@[simp]
lemma _root_.polynomial.to_laurent_C_mul_eq (r : R) (f : R[X]):
  (polynomial.C r * f).to_laurent = C r * f.to_laurent :=
by simp only [_root_.map_mul, polynomial.to_laurent_C]

@[simp]
lemma _root_.polynomial.to_laurent_X_pow (n : ℕ) :
  (X ^ n : R[X]).to_laurent = T n :=
by simp only [map_pow, polynomial.to_laurent_X, T_pow, mul_one]

@[simp]
lemma _root_.polynomial.to_laurent_C_mul_X_pow (n : ℕ) (r : R) :
  (polynomial.C r * X ^ n).to_laurent = C r * T n :=
by simp only [_root_.map_mul, polynomial.to_laurent_C, polynomial.to_laurent_X_pow]

lemma is_unit_T (n : ℤ) : is_unit (T n : R[T;T⁻¹]) :=
by refine ⟨⟨T n, T (- n), _, _⟩, _⟩; simp [← T_add]

lemma is_regular_T (n : ℤ) : is_regular (T n : R[T;T⁻¹]) :=
⟨is_left_regular_of_mul_eq_one (by simp [← T_add] : T (-n) * T n = 1),
  is_right_regular_of_mul_eq_one (by simp [← T_add] : T n * T (-n) = 1)⟩

end semiring

end laurent_polynomial
