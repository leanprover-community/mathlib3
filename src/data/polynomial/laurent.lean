/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.algebra_map

/-!  # Laurent polynomials

We introduce Laurent polynomials over a semiring `R`.  Mathematically, they are expressions of the
form
$$
\sum_{i \in \mathbb{Z}} a_i T ^ i
$$
where the sum extends over a finite subset of `ℤ`.  Thus, negative exponents are allowed.  The
coefficients come from the semiring `R` and the variable `T` commutes with everything.

Since we are going to convert back and forth between polynomials and Laurent polynomials, we
decided to maintain some distinction by using the symbol `T`, rather than `X`, as the variable for
Laurent polynomials

## Notation
The symbol `R[T;T⁻¹]` stands for `laurent_polynomial R`.  We also define

* `C : R →+* R[T;T⁻¹]` is the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` is the sequence of powers of the variable `T`.

## Implementation notes

We define Laurent polynomials as `add_monoid_algebra R ℤ`.
Thus, they are essentially `finsupp`s `ℤ →₀ R`.
This choice differs from the current irreducible design of `polynomial`, that instead shields away
the implementation via `finsupp`s.  It is closer to the original definition of polynomials.

As a consequence, `laurent_polynomials` play well with polynomials, but there is a little roughness
in establishing the API, since the `finsupp` implementation of `polynomial R` is well-shielded.

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

variables {R : Type*}

/--  The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials. -/
abbreviation laurent_polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℤ

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R

/--  The ring homomorphism, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def polynomial.to_laurent [semiring R] : R[X] →+* R[T;T⁻¹] :=
(map_domain_ring_hom R int.of_nat_hom).comp (to_finsupp_iso R)

/-- This is not a simp lemma, as it is usually preferable to use the lemmas about `C` and `X`
instead. -/
lemma polynomial.to_laurent_apply [semiring R] (p : R[X]) :
  p.to_laurent = p.to_finsupp.map_domain coe := rfl

/--  The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def polynomial.to_laurent_alg [comm_semiring R] :
  R[X] →ₐ[R] R[T;T⁻¹] :=
begin
  refine alg_hom.comp _ (to_finsupp_iso_alg R).to_alg_hom,
  exact (map_domain_alg_hom R R int.of_nat_hom),
end

@[simp]
lemma polynomial.to_laurent_alg_apply [comm_semiring R] (f : R[X]) :
  f.to_laurent_alg = f.to_laurent := rfl

namespace laurent_polynomial

section semiring
variables [semiring R]

lemma single_zero_one_eq_one : (single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) := rfl

/-!  ### The functions `C` and `T`. -/
/--  The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[T;T⁻¹] :=
single_zero_ring_hom

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
show map_domain coe (monomial n r).to_finsupp = (C r * T n : R[T;T⁻¹]),
by rw [to_finsupp_monomial, map_domain_single, single_eq_C_mul_T]

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

instance invertible_T (n : ℤ) : invertible (T n : R[T;T⁻¹]) :=
{ inv_of := T (- n),
  inv_of_mul_self := by rw [← T_add, add_left_neg, T_zero],
  mul_inv_of_self := by rw [← T_add, add_right_neg, T_zero] }

@[simp]
lemma inv_of_T (n : ℤ) : ⅟ (T n : R[T;T⁻¹]) = T (- n) := rfl

lemma is_unit_T (n : ℤ) : is_unit (T n : R[T;T⁻¹]) :=
is_unit_of_invertible _

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
    { assume n s ns ih, rw finset.sum_insert ns, exact h_add A ih } },
  convert B p.support,
  ext a,
  simp_rw [← single_eq_C_mul_T, finset.sum_apply', single_apply, finset.sum_ite_eq'],
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

/--  `trunc : R[T;T⁻¹] →+ R[X]` maps a Laurent polynomial `f` to the polynomial whose terms of
nonnegative degree coincide with the ones of `f`.  The terms of negative degree of `f` "vanish".

`trunc` is a left-inverse to `polynomial.to_laurent`. -/
def trunc : R[T;T⁻¹] →+ R[X] :=
((to_finsupp_iso R).symm.to_add_monoid_hom).comp $
  comap_domain.add_monoid_hom $ λ a b, int.of_nat.inj

@[simp]
lemma trunc_C_mul_T (n : ℤ) (r : R) : trunc (C r * T n) = ite (0 ≤ n) (monomial n.to_nat r) 0 :=
begin
  apply (to_finsupp_iso R).injective,
  rw [← single_eq_C_mul_T, trunc, add_monoid_hom.coe_comp, function.comp_app,
    comap_domain.add_monoid_hom_apply, to_finsupp_iso_apply],
  by_cases n0 : 0 ≤ n,
  { lift n to ℕ using n0,
    erw [comap_domain_single (function.injective.inj_on (λ a b, int.coe_nat_inj) _),
      to_finsupp_iso_symm_apply],
    simp only [int.coe_nat_nonneg, int.to_nat_coe_nat, if_true, to_finsupp_iso_apply,
      to_finsupp_monomial] },
  { lift (- n) to ℕ using (neg_pos.mpr (not_le.mp n0)).le with m,
    rw [to_finsupp_iso_apply, to_finsupp_inj, if_neg n0],
    erw to_finsupp_iso_symm_apply,
    ext a,
    have := ((not_le.mp n0).trans_le (int.coe_zero_le a)).ne',
    simp only [coeff, comap_domain_apply, int.of_nat_eq_coe, coeff_zero, single_apply_eq_zero, this,
      forall_false_left] }
end

@[simp]
lemma _root_.polynomial.trunc_to_laurent (f : R[X]) : trunc f.to_laurent = f :=
begin
  refine f.induction_on' _ _,
  { exact λ f g hf hg, by simp only [hf, hg, _root_.map_add] },
  { exact λ n r, by simp only [polynomial.to_laurent_C_mul_T, trunc_C_mul_T, int.coe_nat_nonneg,
      int.to_nat_coe_nat, if_true] }
end

lemma _root_.polynomial.to_laurent_injective :
  function.injective (polynomial.to_laurent : R[X] → R[T;T⁻¹]) :=
function.has_left_inverse.injective ⟨trunc, polynomial.trunc_to_laurent⟩

@[simp]
lemma _root_.polynomial.to_laurent_inj (f g : R[X]) :
  f.to_laurent = g.to_laurent ↔ f = g :=
⟨λ h, polynomial.to_laurent_injective h, λ h, congr_arg _ h⟩

lemma exists_T_pow (f : R[T;T⁻¹]) :
  ∃ (n : ℕ) (f' : R[X]), f'.to_laurent = f * T n :=
begin
  apply f.induction_on' _ (λ n a, _); clear f,
  { rintros f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩,
    by_cases h : m ≤ n;
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, _⟩;
    simp only [hf, hg, add_mul, add_comm (n : ℤ), map_add, map_mul, polynomial.to_laurent_X_pow,
      mul_T_assoc, int.coe_nat_add] },
  { cases n with n n,
    { exact ⟨0, polynomial.C a * X ^ n, by simp⟩ },
    { refine ⟨n + 1, polynomial.C a, _⟩,
      simp only [int.neg_succ_of_nat_eq, polynomial.to_laurent_C, int.coe_nat_succ, mul_T_assoc,
        add_left_neg, T_zero, mul_one] } }
end

/--  This version of `exists_T_pow` can be called as `rcases f.exists_T_pow' with ⟨n, f', rfl⟩`. -/
lemma exists_T_pow' (f : R[T;T⁻¹]) :
  ∃ (n : ℕ) (f' : R[X]), f = f'.to_laurent * T (- n) :=
begin
  rcases f.exists_T_pow with ⟨n, f', hf⟩,
  exact ⟨n, f', by simp [hf]⟩,
end

/--  Suppose that `Q` is a statement about Laurent polynomials such that
* `Q` is true on *ordinary* polynomials;
* `Q (f * T)` implies `Q f`;
it follow that `Q` is true on all Laurent polynomials. -/
lemma reduce_to_polynomial_of_mul_T (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
  (Qf : ∀ (f : R[X]), Q f.to_laurent)
  (QT : ∀ f, Q (f * T 1) → Q f) :
  Q f :=
begin
  rcases f.exists_T_pow' with ⟨n, f', rfl⟩,
  induction n with n hn,
  { simpa using Qf _ },
  { convert QT _ _,
    simpa using hn }
end

instance : module R[X] R[T;T⁻¹] :=
{ smul      := λ f l, f.to_laurent * l,
  one_smul  := λ f, by simp only [map_one, one_mul],
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
