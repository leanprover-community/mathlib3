/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.algebra_map
import data.polynomial.denoms_clearable

/-!  # Laurent polynomials -/

open_locale polynomial big_operators
open polynomial monoid_algebra multiplicative
noncomputable theory

variables {R Z : Type*}

section monoid_algebra_homs
variables [comm_semiring R]

section multiplicative
variables [monoid Z]

/--  A multiplicative homomorphism `f : N →* Z` between two monoids induces an `R`-algebra
homomorphism `full_lift f : monoid_algebra R N →ₐ[R] monoid_algebra R Z`. -/
def full_lift {N : Type*} [monoid N] (f : N →* Z) :
  monoid_algebra R N →ₐ[R] monoid_algebra R Z :=
begin
  refine monoid_algebra.lift R N (monoid_algebra R Z) _,
  refine ⟨λ x, finsupp.single (f x) 1, _, _⟩,
  { rw [_root_.map_one],
    refl },
  { exact λ x y, by simp only [_root_.map_mul, single_mul_single, mul_one] },
end

end multiplicative

section additive
variables [add_monoid Z] {N : Type*} [add_monoid N] (f : N →+ Z)

/--  An additive homomorphism `f : N →+ Z` between two additive monoids induces an `R`-algebra
homomorphism `full_lift f : add_monoid_algebra R N →ₐ[R] add_monoid_algebra R Z`. -/
def add_full_lift (f : N →+ Z) :
  add_monoid_algebra R N →ₐ[R] add_monoid_algebra R Z :=
begin
  refine add_monoid_algebra.lift R N (monoid_algebra R (multiplicative Z)) _,
  refine ⟨λ x, finsupp.single (of_add (f (to_add x))) 1, _, _⟩,
  { rw [to_add_one, _root_.map_zero, of_add_zero],
    refl },
  { exact λ x y, by simp only [single_mul_single, mul_one, to_add_mul, _root_.map_add, of_add_add]},
end

@[simp]
lemma add_full_lift_single (n : N) (r : R) :
  add_full_lift f (finsupp.single n r) = finsupp.single (f n) r :=
begin
  simp only [add_full_lift, add_monoid_algebra.lift_single, monoid_hom.coe_mk, to_add_of_add,
    finsupp.smul_single', mul_one],
  congr,
end

end additive

end monoid_algebra_homs

/--  The semiring of Laurent polynomials with coefficients in the semiring `R`.
We denote it by `R[T;T⁻¹]`.
The ring homomorphism `C : R →+* R[T;T⁻¹]` includes `R` as the constant polynomials.
 -/
abbreviation laurent_polynomial (R : Type*) [semiring R] := add_monoid_algebra R ℤ

local notation R`[T;T⁻¹]`:9000 := laurent_polynomial R

/--  The `R`-algebra map, taking a polynomial with coefficients in `R` to a Laurent polynomial
with coefficients in `R`. -/
def polynomial.to_laurent_polynomial {R : Type*} [comm_semiring R] :
  R[X] →ₐ[R] R[T;T⁻¹] :=
begin
  refine alg_hom.comp _ (to_finsupp_iso_alg R).to_alg_hom,
  exact (add_full_lift (nat.cast_add_monoid_hom ℤ)),
end

namespace laurent_polynomial

section comm_semiring
variables [comm_semiring R]

/--  The ring homomorphism `C`, including `R` into the ring of Laurent polynomials over `R` as
the constant Laurent polynomials. -/
def C : R →+* R[T;T⁻¹] :=
{ to_fun    := finsupp.single 0,
  map_one'  := rfl,
  map_mul'  := λ x y, by simp only [add_monoid_algebra.single_mul_single, add_zero],
  map_zero' := finsupp.single_zero,
  map_add'  := λ x y, finsupp.single_add }

/--  The variable of the ring of Laurent polynomials. -/
def T : R[T;T⁻¹] := finsupp.single 1 1

-- `by simp [polynomial.to_laurent_polynomial]` proves the lemma
@[simp]
lemma full_lift_monomial (n : ℕ) (r : R) :
  (monomial n r : R[X]).to_laurent_polynomial = finsupp.single n r :=
by simp only [polynomial.to_laurent_polynomial, alg_equiv.to_alg_hom_eq_coe, alg_hom.coe_comp,
    alg_equiv.coe_alg_hom, function.comp_app, to_finsupp_iso_alg_apply, ring_equiv.to_fun_eq_coe,
    to_finsupp_iso_apply, to_finsupp_monomial, add_full_lift_single, nat.coe_cast_add_monoid_hom,
    int.nat_cast_eq_coe_nat]

@[simp]
lemma full_lift_one_zero : (finsupp.single 0 1 : R[T;T⁻¹]) = (1 : R[T;T⁻¹]) := rfl

@[simp]
lemma full_lift_C (r : R) :
  (polynomial.C r).to_laurent_polynomial = C r :=
full_lift_monomial 0 r

--  without the empty type annotation `(_ : _)`, the proof times out.
@[simp] lemma full_lift_one : (polynomial.to_laurent_polynomial : R[X] → R[T;T⁻¹]) 1 = 1 :=
(full_lift_C (1 : R) : _)

@[simp]
lemma full_lift_X :
  (X : R[X]).to_laurent_polynomial = T :=
full_lift_monomial 1 1

@[simp]
lemma full_lift_X_pow (n : ℕ) :
  (X ^ n : R[X]).to_laurent_polynomial = T ^ n :=
by simp only [map_pow, full_lift_X]

@[simp]
lemma full_lift_C_mul_X_pow (n : ℕ) (r : R) :
  (polynomial.C r * X ^ n).to_laurent_polynomial = C r * T ^ n :=
by simp only [map_pow, full_lift_X, _root_.map_mul, full_lift_C]

@[simp]
lemma single_eq_C_mul_X_pow (n : ℕ) (r : R) :
  (finsupp.single n r : R[T;T⁻¹]) = (C r * T ^ n : R[T;T⁻¹]) :=
by simp only [T, C, add_monoid_algebra.single_pow, add_monoid_algebra.single_mul_single,
    ring_hom.coe_mk, nat.smul_one_eq_coe, int.nat_cast_eq_coe_nat, one_pow, zero_add, mul_one]

instance : module R[X] R[T;T⁻¹] :=
{ smul := λ f l, f.to_laurent_polynomial * l,
  one_smul := λ f, by simp only [full_lift_one, one_mul],
  mul_smul := λ f g l, by simp only [mul_assoc, _root_.map_mul],
  smul_add := λ f x y, by simp only [mul_add],
  smul_zero := λ f, by simp only [mul_zero],
  add_smul := λ f g x, by simp only [add_mul, _root_.map_add],
  zero_smul := λ f, by simp only [_root_.map_zero, zero_mul] }

@[elab_as_eliminator] protected lemma induction_on {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
  (h_C : ∀a, M (C a))
  (h_add : ∀{p q}, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℕ) (a : R), M (finsupp.single n a) → M (finsupp.single (n+1) a))
  (h_monomial_Z : ∀(n : ℕ) (a : R), M (finsupp.single (- n) a) → M (finsupp.single (-n-1) a)) :
  M p :=
begin
  have A : ∀(n:ℤ) (a), M (finsupp.single n a),
  { assume n a,
    apply n.induction_on,
    { exact h_C a },
    { exact λ m, h_monomial m a },
    { exact λ (m : ℕ), h_monomial_Z m a } },
  have B : ∀ (s : finset ℤ), M (s.sum (λ (n : ℤ), C (p.to_fun n) * (finsupp.single n 1))),
  { apply finset.induction,
    { convert h_C 0, simp only [finset.sum_empty, _root_.map_zero] },
    { assume n s ns ih, rw finset.sum_insert ns,
    { apply h_add  _ ih,
      convert A n (p.to_fun n),
      rw [C, ring_hom.coe_mk],
      simp_rw [add_monoid_algebra.single_mul_single, zero_add, mul_one] } } },
     convert B p.support,
     rw [C, ring_hom.coe_mk],
     simp_rw [add_monoid_algebra.single_mul_single, zero_add, mul_one],
     ext a,
     suffices : p a = ite (a ∈ p.support) (p.to_fun a) 0,
     { simpa only [finset.sum_apply', finsupp.single_apply, finset.sum_ite_eq'] },
     split_ifs with h h,
     { refl },
     { exact finsupp.not_mem_support_iff.mp h }
end


/--
To prove something about Laurent polynomials,
it suffices to show the condition is closed under taking sums,
and it holds for monomials.
-/
@[elab_as_eliminator] protected lemma induction_on' {M : R[T;T⁻¹] → Prop} (p : R[T;T⁻¹])
  (h_add : ∀p q, M p → M q → M (p + q))
  (h_monomial : ∀(n : ℤ) (a : R), M (finsupp.single n a)) :
  M p :=
begin
  refine p.induction_on (h_monomial 0) h_add _ _;
  exact λ n f Mf, h_monomial _ f
end

instance : algebra R[X] R[T;T⁻¹] :=
{ commutes' := λ f l, by simp [mul_comm],
  smul_def' := λ f l, rfl,
  .. (add_full_lift (nat.cast_add_monoid_hom ℤ)).to_ring_hom.comp (to_finsupp_iso R).to_ring_hom }

lemma exists_X_pow (f : R[T;T⁻¹]) : ∃ (n : ℕ) (f' : R[X]), f * T ^ n = f'.to_laurent_polynomial :=
begin
  apply f.induction_on' _ (λ n a, _); clear f,
  { rintros f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩,
    by_cases h : m ≤ n;
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, _⟩;
    rw [add_mul, _root_.map_add, _root_.map_mul, ← hf, _root_.map_mul, ← hg, mul_assoc,
      full_lift_X_pow, pow_add, full_lift_X_pow, mul_assoc, ← pow_add T n, add_comm n, pow_add] },
  { cases n with n n,
    { exact ⟨0, polynomial.C a * X ^ n, by simp⟩ },
    { refine ⟨n + 1, polynomial.C a, _⟩,
      rw [full_lift_C, T, add_monoid_algebra.single_pow, add_monoid_algebra.single_mul_single],
      simp [-neg_add_rev, int.neg_succ_of_nat_eq, neg_add_self, C, ring_hom.coe_mk] } }
end

/--  This version of `exists_X_pow'` can be called as `rcases f.exists_X_pow' with ⟨n, f', rfl⟩`. -/
lemma exists_X_pow' (f : R[T;T⁻¹]) : ∃ (n : ℤ) (f' : R[X]),
  f = f'.to_laurent_polynomial * finsupp.single n 1 :=
begin
  rcases f.exists_X_pow with ⟨n, f', hf⟩,
  refine ⟨(- n), f', _⟩,
  rw [← hf, mul_assoc, T, add_monoid_algebra.single_pow, add_monoid_algebra.single_mul_single],
  simp,
end

/--  Suppose that `Q` is a statement about Laurent polynomials such that
* `Q` is true on ~~Laurent~~ polynomials;
* `Q (f * T)` implies `Q f`;

is true on all Laurent polynomials. -/
lemma proprop (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
  (PQ : ∀ (f : R[X]), Q f.to_laurent_polynomial)
  (Tn : ∀ f, Q (f * T) → Q f) :
  Q f :=
begin
  rcases f.exists_X_pow' with ⟨n, f', rfl⟩,
  cases n with n n,
  { convert PQ (f' * X ^ n),
    simp },
  { rw int.neg_succ_of_nat_eq,
    induction n with n hn,
    { refine Tn _ _,
      convert PQ f',
      rw mul_assoc,
      convert mul_one _,
      rw [T, add_monoid_algebra.single_mul_single],
      simp only [int.coe_nat_zero, zero_add, add_left_neg, mul_one, full_lift_one_zero] },
    { suffices : Q (polynomial.to_laurent_polynomial f' *
        (finsupp.single (-(↑(n.succ))) 1) * finsupp.single (-1) 1),
      { rwa [mul_assoc, add_monoid_algebra.single_mul_single, mul_one] at this },
      refine Tn _ _,
      rwa [mul_assoc, T, add_monoid_algebra.single_mul_single, mul_assoc,
        add_monoid_algebra.single_mul_single, mul_one, mul_one] } }
end

end comm_semiring

end laurent_polynomial
