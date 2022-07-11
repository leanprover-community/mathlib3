/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import data.polynomial.algebra_map
import ring_theory.localization.basic
import tactic.congrm

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

* `C : R →+* R[T;T⁻¹]` the inclusion of constant polynomials, analogous to the one for `R[X]`;
* `T : ℤ → R[T;T⁻¹]` the sequence of powers of the variable `T`.

## Implementation notes

We define Laurent polynomials as `add_monoid_algebra R ℤ`.
Thus, they are essentially `finsupp`s `ℤ →₀ R`.
This choice differs from the current irreducible design of `polynomial`, that instead shields away
the implementation via `finsupp`s.  It is closer to the original definition of polynomials.

As a consequence, `laurent_polynomial` plays well with polynomials, but there is a little roughness
in establishing the API, since the `finsupp` implementation of `polynomial R` is well-shielded.

Unlike the case of polynomials, I felt that the exponent notation was not too easy to use, as only
natural exponents would be allowed.  Moreover, in the end, it seems likely that we should aim to
perform computations on exponents in `ℤ` anyway and separating this via the symbol `T` seems
convenient.

I made a *heavy* use of `simp` lemmas, aiming to bring Laurent polynomials to the form `C a * T n`.
Any comments or suggestions for improvements is greatly appreciated!

##  Future work
Lots is missing!
-- (Riccardo) add inclusion into Laurent series.
-- (Riccardo) giving a morphism (as `R`-alg, so in the commutative case)
  from `R[T,T⁻¹]` to `S` is the same as choosing a unit of `S`.
-- A "better" definition of `trunc` would be as an `R`-linear map.  This works:
--  ```
--  def trunc : R[T;T⁻¹] →[R] R[X] :=
--  begin
--    refine (_ : add_monoid_algebra R ℕ →[R] R[X]).comp _,
--    { exact ⟨(to_finsupp_iso R).symm, by simp⟩ },
--    { refine ⟨λ r, comap_domain _ r (set.inj_on_of_injective (λ a b ab, int.of_nat.inj ab) _), _⟩,
--      exact λ r f, comap_domain_smul _ _ _ }
--  end
--  ```
--  but it would make sense to bundle the maps better, for a smoother user experience.
--  I (DT) did not have the strength to embark on this (possibly short!) journey, after getting to
--  this stage of the Laurent process!
--  This would likely involve adding a `comap_domain` analogue of
--  `add_monoid_algebra.map_domain_alg_hom` and an `R`-linear version of
--  `polynomial.to_finsupp_iso`.
-- Add `degree, int_degree, int_trailing_degree, leading_coeff, trailing_coeff,...`.
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

lemma algebra_map_apply {R A : Type*} [comm_semiring R] [semiring A] [algebra R A] (r : R) :
  algebra_map R (laurent_polynomial A) r = C (algebra_map R A r) :=
rfl

/--
When we have `[comm_semiring R]`, the function `C` is the same as `algebra_map R R[T;T⁻¹]`.
(But note that `C` is defined when `R` is not necessarily commutative, in which case
`algebra_map` is not available.)
-/
lemma C_eq_algebra_map {R : Type*} [comm_semiring R] (r : R) :
  C r = algebra_map R R[T;T⁻¹] r :=
rfl

lemma single_eq_C (r : R) : single 0 r = C r := rfl

/--  The function `n ↦ T ^ n`, implemented as a sequence `ℤ → R[T;T⁻¹]`.

Using directly `T ^ n` does not work, since we want the exponents to be of Type `ℤ` and there
is no `ℤ`-power defined on `R[T;T⁻¹]`.  Using that `T` is a unit introduces extra coercions.
For these reasons, the definition of `T` is as a sequence. -/
def T (n : ℤ) : R[T;T⁻¹] := single n 1

@[simp]
lemma T_zero : (T 0 : R[T;T⁻¹]) = 1 := rfl

@[simp] lemma coeff_T (m n : ℤ) : (T n : R[T;T⁻¹]) m = ite (m = n) 1 0 :=
begin
  split_ifs with h h,
  { simp only [h, T, single_eq_same] },
  { simp only [T, single_eq_of_ne (ne_comm.mp h)] }
end

lemma T_add (m n : ℤ) : (T (m + n) : R[T;T⁻¹]) = T m * T n :=
by { convert single_mul_single.symm, simp [T] }

lemma T_sub (m n : ℤ) : (T (m - n) : R[T;T⁻¹]) = T m * T (-n) :=
by rw [← T_add, sub_eq_add_neg]

@[simp]
lemma T_pow (m : ℤ) (n : ℕ) : (T m ^ n : R[T;T⁻¹]) = T (n * m) :=
by rw [T, T, single_pow n, one_pow, nsmul_eq_mul]

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
  try { exact λ n f _, h_C_mul_T _ f },
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
    erw [comap_domain_single, to_finsupp_iso_symm_apply],
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

@[simp] lemma left_inverse_trunc_to_laurent :
  function.left_inverse (trunc : R[T;T⁻¹] → R[X]) polynomial.to_laurent :=
begin
  refine λ f, f.induction_on' _ _,
  { exact λ f g hf hg, by simp only [hf, hg, _root_.map_add] },
  { exact λ n r, by simp only [polynomial.to_laurent_C_mul_T, trunc_C_mul_T, int.coe_nat_nonneg,
      int.to_nat_coe_nat, if_true] }
end

@[simp] lemma _root_.polynomial.trunc_to_laurent (f : R[X]) : trunc f.to_laurent = f :=
left_inverse_trunc_to_laurent _

lemma _root_.polynomial.to_laurent_injective :
  function.injective (polynomial.to_laurent : R[X] → R[T;T⁻¹]) :=
left_inverse_trunc_to_laurent.injective

@[simp] lemma _root_.polynomial.to_laurent_inj (f g : R[X]) :
  f.to_laurent = g.to_laurent ↔ f = g :=
⟨λ h, polynomial.to_laurent_injective h, congr_arg _⟩

lemma _root_.polynomial.to_laurent_ne_zero {f : R[X]} :
  f ≠ 0 ↔ f.to_laurent ≠ 0 :=
(map_ne_zero_iff _ (by exact polynomial.to_laurent_injective)).symm

lemma exists_T_pow (f : R[T;T⁻¹]) :
  ∃ (n : ℕ) (f' : R[X]), f'.to_laurent = f * T n :=
begin
  apply f.induction_on' _ (λ n a, _); clear f,
  { rintros f g ⟨m, fn, hf⟩ ⟨n, gn, hg⟩,
    refine ⟨m + n, fn * X ^ n + gn * X ^ m, _⟩,
    simp only [hf, hg, add_mul, add_comm (n : ℤ), map_add, map_mul, polynomial.to_laurent_X_pow,
      mul_T_assoc, int.coe_nat_add] },
  { cases n with n n,
    { exact ⟨0, polynomial.C a * X ^ n, by simp⟩ },
    { refine ⟨n + 1, polynomial.C a, _⟩,
      simp only [int.neg_succ_of_nat_eq, polynomial.to_laurent_C, int.coe_nat_succ, mul_T_assoc,
        add_left_neg, T_zero, mul_one] } }
end

/--  This is a version of `exists_T_pow` stated as an induction principle. -/
@[elab_as_eliminator] lemma induction_on_mul_T {Q : R[T;T⁻¹] → Prop} (f : R[T;T⁻¹])
  (Qf : ∀ {f : R[X]} {n : ℕ}, Q (f.to_laurent * T (- n))) :
  Q f :=
begin
  rcases f.exists_T_pow with ⟨n, f', hf⟩,
  rw [← mul_one f, ← T_zero, ← nat.cast_zero, ← nat.sub_self n, nat.cast_sub rfl.le, T_sub,
    ← mul_assoc, ← hf],
  exact Qf,
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
  induction f using laurent_polynomial.induction_on_mul_T with f n,
  induction n with n hn,
  { simpa only [int.coe_nat_zero, neg_zero', T_zero, mul_one] using Qf _ },
  { convert QT _ _,
    simpa using hn }
end

section support

lemma support_C_mul_T (a : R) (n : ℤ) : (C a * T n).support ⊆ {n} :=
by simpa only [← single_eq_C_mul_T] using support_single_subset

lemma support_C_mul_T_ne_zero {a : R} (a0 : a ≠ 0) (n : ℤ) : (C a * T n).support = {n} :=
begin
  rw ← single_eq_C_mul_T,
  exact support_single_ne_zero _ a0,
end

lemma support_mul_T (f : R[T;T⁻¹]) (n : ℤ) :
  (f * T n).support = f.support.map (add_right_embedding n) :=
support_mul_single f 1 (by simp) n

@[simp] lemma to_laurent_support (f : R[X]) :
  f.to_laurent.support = f.support.map nat.cast_embedding :=
begin
  generalize' hd : f.support = s,
  revert f,
  refine finset.induction_on s _ _; clear s,
  { simp only [polynomial.support_eq_empty, map_zero, finsupp.support_zero, eq_self_iff_true,
      implies_true_iff, finset.map_empty] {contextual := tt} },
  { intros a s as hf f fs,
    have : (erase a f).to_laurent.support = s.map nat.cast_embedding := hf (f.erase a) (by simp only
      [fs, finset.erase_eq_of_not_mem as, polynomial.support_erase, finset.erase_insert_eq_erase]),
    rw [← monomial_add_erase f a, finset.map_insert, ← this, map_add,
      polynomial.to_laurent_C_mul_T, support_add_eq, finset.insert_eq],
    { congr,
      exact support_C_mul_T_ne_zero (polynomial.mem_support_iff.mp (by simp [fs])) _ },
    { rw this,
      exact disjoint.mono_left (support_C_mul_T _ _) (by simpa) } }
end

end support

--  #15199
lemma _root_.polynomial.degree_eq_support_max (p : R[X]) : p.degree = p.support.max :=
rfl

section degrees

open_locale classical

/--  The degree of a Laurent polynomial takes values in `with_bot ℤ`.
If `f : R[T;T⁻¹]` is a Laurent polynomial, then `f.degree` is the maximum of its support of `f`,
or `⊥`, if `f = 0`. -/
def degree (f : R[T;T⁻¹]) : with_bot ℤ := f.support.max

/--  The int_degree of a Laurent polynomial takes values in `ℤ`.
If `f : R[T;T⁻¹]` is a Laurent polynomial, then `f.int_degree` is the maximum of its support of `f`,
or `0`, if `f = 0`. -/
def int_degree (f : R[T;T⁻¹]) : ℤ :=
dite (f = 0) (λ _, 0) (λ f0, f.support.max' $ support_nonempty_iff.mpr f0)

@[simp] lemma degree_zero : degree (0 : R[T;T⁻¹]) = ⊥ := rfl

@[simp] lemma degree_eq_bot_iff {f : R[T;T⁻¹]} : f.degree = ⊥ ↔ f = 0 :=
begin
  refine ⟨λ h, _, λ h, by rw [h, degree_zero]⟩,
  rw [degree, finset.max_eq_sup_with_bot] at h,
  ext n,
  refine not_not.mp (λ f0, _),
  simp_rw [finset.sup_eq_bot_iff, finsupp.mem_support_iff, ne.def, with_bot.coe_ne_bot] at h,
  exact h n f0,
end

@[simp] lemma int_degree_zero : int_degree (0 : R[T;T⁻¹]) = 0 := rfl

section exact_degrees

open_locale classical

lemma degree_C_mul_T (n : ℤ) (a : R) (a0 : a ≠ 0) : (C a * T n).degree = n :=
begin
  rw degree,
  convert finset.max_singleton,
  refine support_eq_singleton.mpr _,
  simp only [← single_eq_C_mul_T, single_eq_same, a0, ne.def, not_false_iff, eq_self_iff_true,
    and_self],
end

lemma degree_T [nontrivial R] (n : ℤ) : (T n : R[T;T⁻¹]).degree = n :=
begin
  rw [← one_mul (T n), ← map_one C],
  exact degree_C_mul_T n 1 (one_ne_zero : (1 : R) ≠ 0),
end

lemma degree_C {a : R} (a0 : a ≠ 0) : (C a).degree = 0 :=
begin
  rw [← mul_one (C a), ← T_zero],
  exact degree_C_mul_T 0 a a0
end

lemma degree_C_ite (a : R) : (C a).degree = ite (a = 0) ⊥ 0 :=
by split_ifs with h h;
  simp only [h, map_zero, degree_zero, degree_C, ne.def, not_false_iff]

end exact_degrees

section degree_bounds

lemma degree_C_mul_T_le (n : ℤ) (a : R) : (C a * T n).degree ≤ n :=
begin
  by_cases a0 : a = 0,
  { simp only [a0, map_zero, zero_mul, degree_zero, bot_le] },
  { exact (degree_C_mul_T n a a0).le }
end

lemma degree_T_le (n : ℤ) : (T n : R[T;T⁻¹]).degree ≤ n :=
(le_of_eq (by rw [map_one, one_mul])).trans (degree_C_mul_T_le n (1 : R))

lemma degree_C_le (a : R) : (C a).degree ≤ 0 :=
(le_of_eq (by rw [T_zero, mul_one])).trans (degree_C_mul_T_le 0 a)

end degree_bounds

lemma int_degree_to_laurent_eq_nat_degree {f : R[X]} :
  f.to_laurent.int_degree = f.nat_degree :=
begin
  by_cases f0 : f = 0,
  { simp only [int_degree, f0, map_zero, dif_pos, nat_degree_zero, nat.cast_zero] },
  { rw [int_degree, dif_neg, nat_degree_eq_support_max' f0],
    simp_rw to_laurent_support,
    convert finset.max'_image _ _ _,
    { ext,
      simp only [finset.mem_map, nat.cast_embedding_apply, finset.mem_image] },
    { exact nat.mono_cast },
    { exact (finset.nonempty.image_iff _).mpr (nonempty_support_iff.mpr f0) },
    { exact polynomial.to_laurent_ne_zero.mp f0 } }
end

lemma degree_eq_int_degree {f : R[T;T⁻¹]} (f0 : f ≠ 0) :
  f.degree = f.int_degree :=
by simp [degree, int_degree, finset.max', f0]

lemma degree_to_laurent (f : R[X]) : f.to_laurent.degree = option.map coe f.degree :=
begin
  by_cases f0 : f = 0,
  { simp only [f0, map_zero, degree_zero, polynomial.degree_zero]; refl },
  { rwa [degree_eq_int_degree, int_degree_to_laurent_eq_nat_degree, degree_eq_nat_degree f0],
    { refl },
    { exact polynomial.to_laurent_ne_zero.mp f0 } }
end

instance : can_lift (with_bot ℤ) ℕ :=
{ coe := coe,
  cond := ((≤) 0),
  prf := begin
    rintro (⟨⟩ | x) h,
    { exact (not_lt.mpr h (with_bot.bot_lt_coe _)).elim },
    { lift x to ℕ using with_bot.coe_le_coe.mp h,
      exact ⟨_, rfl⟩ }
    end }

/-
lemma reduce_to_polynomial_of_mul_T' (f : R[T;T⁻¹]) {Q : R[T;T⁻¹] → Prop}
  (P : R[X] → Prop)
  (hP : ∀ (f : R[X]), P f)
  (QT : ∀ f, Q (f * T 1) → Q f)
  (PQ : ∀ f, P f → Q f.to_laurent) :
  Q f :=
begin
  induction f using laurent_polynomial.induction_on_mul_T with f n,
  induction n with n hn,
  { simpa using PQ _ (hP _) },
  { convert QT _ _,
    simpa using hn }
end
-/

lemma reduce_to_polynomial_of_mul_T''' (f : R[T;T⁻¹])
  {Q : R[T;T⁻¹] → Prop}
  (P : R[X] → Prop)
  (hP : ∀ {f}, P f)
  (PQ : ∀ {f}, P f → ∀ (n : ℕ), Q (f.to_laurent * T (- n))) :
  Q f :=
begin
  induction f using laurent_polynomial.induction_on_mul_T with f n,
  exact PQ hP _,
end

lemma finset.fold_max_add {α β} [linear_order β] (f : α → β) [decidable_eq α] [has_add β]
 [covariant_class β β (function.swap (+)) (≤)]
 (n : with_bot β) (s : finset α) :
  finset.fold max ⊥ (λ (x : α), ↑(f x) + n) s = finset.fold max ⊥ (coe ∘ f) s + n :=
by apply s.induction_on;
  simp [max_add_add_right] {contextual := tt}

lemma degree_mul_T (f : R[T;T⁻¹]) (n : ℤ) :
  (f * T n).degree = f.degree + n :=
by simpa only [degree, support_mul_T, finset.max, finset.sup_map]
  using finset.fold_max_add coe ↑n f.support


lemma option.map_id_coe_le (a b : with_bot ℕ) :
  (id (option.map coe a) : with_bot ℤ) ≤ option.map coe b ↔ a ≤ b :=
begin
  rcases a with _ | a,
  { simp },
  { rcases b with _ | b,
    { rw [option.map_some', id.def, option.map_none', ← not_iff_not, not_le, not_le],
      simp only [with_bot.none_lt_some] },
    { simp } }
end

lemma _root_.with_bot.eq_bot_or_coe {α} (n : with_bot α) : n = ⊥ ∨ ∃ m : α, n = m :=
begin
  rcases n with _ | a,
  { exact or.inl rfl },
  { exact or.inr ⟨_, rfl⟩ }
end

lemma option.map_coe_add {a b : with_bot ℕ} :
  (id (option.map coe (a + b : with_bot ℕ)) : with_bot ℤ) ≤ option.map coe a + option.map coe b :=
begin
  rcases a.eq_bot_or_coe with rfl | ⟨a, rfl⟩,
  { exact (with_bot.bot_add _).ge },
  { rcases b.eq_bot_or_coe with rfl | ⟨b, rfl⟩,
    { exact (with_bot.add_bot _).ge },
    { exact rfl.le } },
end

@[to_additive]
lemma mul_le_cancellable_of_mul_eq_one {α} [monoid α] [has_le α] [covariant_class α α (*) (≤)]
  (a b : α) (ba : b * a = 1) :
  mul_le_cancellable a :=
begin
  intros x y xy,
  rw [← one_mul x, ← one_mul y, ← ba, mul_assoc, mul_assoc],
  exact mul_le_mul_left' xy _,
end

@[to_additive]
lemma units.mul_le_cancellable {α} [monoid α] [has_le α] [covariant_class α α (*) (≤)] (u : αˣ) :
  mul_le_cancellable (u : α) :=
mul_le_cancellable_of_mul_eq_one _ u.inv (units.inv_mul _)

/-
lemma with_bot.add_le_cancellable (n : ℕ) :
  add_le_cancellable (n : with_bot ℕ) :=
begin
  rintros (_ | x) (_ | y) hn,
  { exact rfl.le },
  { exact with_bot.none_le },
  { refine (not_lt.mpr hn (_ : ↑n + ⊥ < ↑(n + x))).elim,
    simp only [with_bot.add_bot, with_bot.bot_lt_coe] },
  { sorry }
end
-/

lemma with_bot.add_coe_neg_le_iff (a : with_bot ℤ) (b : ℤ) (c : with_bot ℤ) :
  a + (-b : ℤ) ≤ c ↔ a ≤ c + b :=
begin
  rcases a.eq_bot_or_coe with rfl | ⟨a, rfl⟩,
  { simp },
  rcases c.eq_bot_or_coe with rfl | ⟨c, rfl⟩,
  { simp only [le_bot_iff, with_bot.coe_add_eq_bot_iff, with_bot.bot_add, with_bot.coe_ne_bot,
      iff_false, not_false_iff] },
  { norm_cast,
    rw ← sub_eq_add_neg,
    exact sub_le_iff_le_add }
end

lemma with_bot.eq_add {A} [add_comm_group A] (a : with_bot A) (b : A) :
  ∃ (a' : with_bot A), a = a' + b :=
begin
  rcases a.eq_bot_or_coe with rfl | ⟨a, rfl⟩,
  { exact ⟨_, (with_bot.bot_add _).symm⟩ },
  { exact ⟨(a - b : A), with_bot.coe_eq_coe.mpr (sub_add_cancel a b).symm⟩ }
end

lemma with_bot.add_coe_neg_eq_iff {A} [add_comm_group A]
  (a : with_bot A) (b : A) (c : with_bot A) :
  a + (-b : A) = c ↔ a = c + b :=
begin
  rcases a.eq_bot_or_coe with rfl | ⟨a, rfl⟩,
  { rw [with_bot.bot_add, iff.comm, eq_comm, ← with_bot.add_eq_bot.symm, eq_comm],
    simp },
  { rcases c.eq_bot_or_coe with rfl | ⟨c, rfl⟩,
    { simp only [with_bot.coe_ne_bot, with_bot.coe_add_eq_bot_iff, with_bot.bot_add, iff_false,
        not_false_iff] },
    { norm_cast,
      rw ← sub_eq_add_neg,
      exact sub_eq_iff_eq_add } }
end

lemma degree_mul_aux (d : with_bot ℕ) (e : with_bot ℤ) (f : R[X]) (g : R[T;T⁻¹])
  (fd : f.degree ≤ d) (ge : g.degree ≤ e) :
  (polynomial.to_laurent f * g).degree ≤ option.map coe d + e :=
begin
  revert ge e,
  apply reduce_to_polynomial_of_mul_T''' g (λ p, (f * p).degree ≤ d + p.degree); clear g,
  { exact λ p, (degree_mul_le _ _).trans (add_le_add fd rfl.le) },
  intros g hfg n e h,
  rw [← mul_assoc, ← map_mul, degree_mul_T, degree_to_laurent],
  refine (with_bot.add_coe_neg_le_iff _ _ _).mpr _,
  refine ((option.map_id_coe_le _ _).mpr hfg).trans _,
  refine option.map_coe_add.trans _,
  rw add_assoc,
  refine add_le_add_left _ _,
  rw [degree_mul_T, degree_to_laurent] at h,
  exact (with_bot.add_coe_neg_le_iff _ _ _).mp h,
end

lemma degree_mul {d e : with_bot ℤ} (f g : R[T;T⁻¹]) (df : f.degree ≤ d) (eg : g.degree ≤ e) :
  (f * g).degree ≤ d + e :=
begin
  revert df eg g d e,
  apply reduce_to_polynomial_of_mul_T f; clear f,
  { intros f e d g fd eg,
    rw degree_to_laurent at fd,
    exact (degree_mul_aux f.degree _ _ _ rfl.le eg).trans (add_le_add fd rfl.le) },
  { intros f hf d e g fd eg,
    rcases with_bot.eq_add e 1 with ⟨e', rfl⟩,
    have : (f * T 1 * (g * T (- 1))).degree ≤ (d + 1) + e',
    { refine hf (g * T (-1)) _ _ ;
      rw degree_mul_T,
      { exact add_le_add_right fd (1 : with_bot ℤ) },
      { exact (with_bot.add_coe_neg_le_iff _ _ _).mpr eg } },
    convert this using 1,
    { rw [mul_assoc, T_mul, mul_assoc, ← T_add, neg_add_self, T_zero, mul_one] },
    { rw [add_comm e', add_assoc],
      refl } }
end

end degrees

instance : module R[X] R[T;T⁻¹] :=
module.comp_hom _ polynomial.to_laurent

instance (R : Type*) [semiring R] : is_scalar_tower R[X] R[X] R[T;T⁻¹] :=
{ smul_assoc := λ x y z, by simp only [has_smul.smul, has_smul.comp.smul, map_mul, mul_assoc] }

end semiring

section comm_semiring
variable [comm_semiring R]

instance algebra_polynomial (R : Type*) [comm_semiring R] : algebra R[X] R[T;T⁻¹] :=
{ commutes' := λ f l, by simp [mul_comm],
  smul_def' := λ f l, rfl,
  .. polynomial.to_laurent }

lemma algebra_map_X_pow (n : ℕ) : algebra_map R[X] R[T;T⁻¹] (X ^ n) = T n :=
polynomial.to_laurent_X_pow n

@[simp]
lemma algebra_map_eq_to_laurent (f : R[X]) : algebra_map R[X] R[T;T⁻¹] f = f.to_laurent :=
rfl

lemma is_localization : is_localization (submonoid.closure ({X} : set R[X])) R[T;T⁻¹] :=
{ map_units := λ t, begin
    cases t with t ht,
    rcases submonoid.mem_closure_singleton.mp ht with ⟨n, rfl⟩,
    simp only [is_unit_T n, set_like.coe_mk, algebra_map_eq_to_laurent, polynomial.to_laurent_X_pow]
  end,
  surj := λ f, begin
    induction f using laurent_polynomial.induction_on_mul_T with f n,
    have := (submonoid.closure ({X} : set R[X])).pow_mem submonoid.mem_closure_singleton_self n,
    refine ⟨(f, ⟨_, this⟩), _⟩,
    simp only [set_like.coe_mk, algebra_map_eq_to_laurent, polynomial.to_laurent_X_pow, mul_T_assoc,
      add_left_neg, T_zero, mul_one],
  end,
  eq_iff_exists := λ f g, begin
    rw [algebra_map_eq_to_laurent, algebra_map_eq_to_laurent, polynomial.to_laurent_inj],
    refine ⟨_, _⟩,
    { rintro rfl,
      exact ⟨1, rfl⟩ },
    { rintro ⟨⟨h, hX⟩, h⟩,
      rcases submonoid.mem_closure_singleton.mp hX with ⟨n, rfl⟩,
      exact mul_X_pow_injective n (by simpa only [X_pow_mul] using h) }
  end }

end comm_semiring

end laurent_polynomial
