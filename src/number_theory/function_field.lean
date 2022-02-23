/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
import field_theory.ratfunc
import ring_theory.algebraic
import ring_theory.dedekind_domain.integral_closure
import ring_theory.integrally_closed

/-!
# Function fields

This file defines a function field and the ring of integers corresponding to it.

## Main definitions
 - `function_field Fq F` states that `F` is a function field over the (finite) field `Fq`,
   i.e. it is a finite extension of the field of rational functions in one variable over `Fq`.
 - `function_field.ring_of_integers` defines the ring of integers corresponding to a function field
    as the integral closure of `polynomial Fq` in the function field.
 - `infty_valuation` : The place at infinity on `Fq(t)` is the nonarchimedean valuation on `Fq(t)`
    with uniformizer `1/t`.

## Implementation notes
The definitions that involve a field of fractions choose a canonical field of fractions,
but are independent of that choice. We also omit assumptions like `finite Fq` or
`is_scalar_tower Fq[X] (fraction_ring Fq[X]) F` in definitions,
adding them back in lemmas when they are needed.

## References
* [D. Marcus, *Number Fields*][marcus1977number]
* [J.W.S. Cassels, A. Frölich, *Algebraic Number Theory*][cassels1967algebraic]
* [P. Samuel, *Algebraic Theory of Numbers*][samuel1970algebraic]

## Tags
function field, ring of integers
-/

noncomputable theory
open_locale non_zero_divisors polynomial

variables (Fq F : Type) [field Fq] [field F]

/-- `F` is a function field over the finite field `Fq` if it is a finite
extension of the field of rational functions in one variable over `Fq`.

Note that `F` can be a function field over multiple, non-isomorphic, `Fq`.
-/
abbreviation function_field [algebra (ratfunc Fq) F] : Prop :=
finite_dimensional (ratfunc Fq) F

/-- `F` is a function field over `Fq` iff it is a finite extension of `Fq(t)`. -/
protected lemma function_field_iff (Fqt : Type*) [field Fqt]
  [algebra Fq[X] Fqt] [is_fraction_ring Fq[X] Fqt]
  [algebra (ratfunc Fq) F] [algebra Fqt F]
  [algebra Fq[X] F] [is_scalar_tower Fq[X] Fqt F]
  [is_scalar_tower Fq[X] (ratfunc Fq) F] :
  function_field Fq F ↔ finite_dimensional Fqt F :=
begin
  let e := is_localization.alg_equiv Fq[X]⁰ (ratfunc Fq) Fqt,
  have : ∀ c (x : F), e c • x = c • x,
  { intros c x,
    rw [algebra.smul_def, algebra.smul_def],
    congr,
    refine congr_fun _ c,
    refine is_localization.ext (non_zero_divisors (Fq[X])) _ _ _ _ _ _ _;
      intros; simp only [alg_equiv.map_one, ring_hom.map_one, alg_equiv.map_mul, ring_hom.map_mul,
                         alg_equiv.commutes, ← is_scalar_tower.algebra_map_apply], },
  split; intro h; resetI,
  { let b := finite_dimensional.fin_basis (ratfunc Fq) F,
    exact finite_dimensional.of_fintype_basis (b.map_coeffs e this) },
  { let b := finite_dimensional.fin_basis Fqt F,
    refine finite_dimensional.of_fintype_basis (b.map_coeffs e.symm _),
    intros c x, convert (this (e.symm c) x).symm, simp only [e.apply_symm_apply] },
end

namespace function_field

/-- The function field analogue of `number_field.ring_of_integers`:
`function_field.ring_of_integers Fq Fqt F` is the integral closure of `Fq[t]` in `F`.

We don't actually assume `F` is a function field over `Fq` in the definition,
only when proving its properties.
-/
def ring_of_integers [algebra Fq[X] F] := integral_closure Fq[X] F

namespace ring_of_integers

variables [algebra Fq[X] F]

instance : is_domain (ring_of_integers Fq F) :=
(ring_of_integers Fq F).is_domain

instance : is_integral_closure (ring_of_integers Fq F) Fq[X] F :=
integral_closure.is_integral_closure _ _

variables [algebra (ratfunc Fq) F] [function_field Fq F]
variables [is_scalar_tower Fq[X] (ratfunc Fq) F]

instance : is_fraction_ring (ring_of_integers Fq F) F :=
integral_closure.is_fraction_ring_of_finite_extension (ratfunc Fq) F

instance : is_integrally_closed (ring_of_integers Fq F) :=
integral_closure.is_integrally_closed_of_finite_extension (ratfunc Fq)

instance [is_separable (ratfunc Fq) F] :
  is_dedekind_domain (ring_of_integers Fq F) :=
is_integral_closure.is_dedekind_domain Fq[X] (ratfunc Fq) F _

end ring_of_integers

/-! ### The place at infinity on Fq(t) -/

section infty_valuation

variable [decidable_eq (ratfunc Fq)]

/-- The valuation at infinity is the nonarchimedean valuation on `Fq(t)` with uniformizer `1/t`.
Explicitly, if `f/g ∈ Fq(t)` is a nonzero quotient of polynomials, its valuation at infinity is
`multiplicative.of_add(degree(f) - degree(g))`. -/
def infty_valuation_def (r : ratfunc Fq) : with_zero (multiplicative ℤ) :=
ite (r = 0) 0 (multiplicative.of_add ((r.num.nat_degree : ℤ) - r.denom.nat_degree))

lemma infty_valuation.map_zero' : infty_valuation_def Fq 0 = 0 :=
by { rw [infty_valuation_def, if_pos], refl, }

lemma infty_valuation.map_one' : infty_valuation_def Fq 1 = 1 :=
begin
  rw [infty_valuation_def, if_neg (zero_ne_one.symm : (1 : ratfunc Fq) ≠ 0)],
  simp only [polynomial.nat_degree_one, ratfunc.num_one, int.coe_nat_zero, sub_zero,
  ratfunc.denom_one, of_add_zero, with_zero.coe_one],
end

lemma infty_valuation.map_mul' (x y : ratfunc Fq) :
  infty_valuation_def Fq (x * y) = infty_valuation_def Fq x * infty_valuation_def Fq y :=
begin
  rw [infty_valuation_def, infty_valuation_def, infty_valuation_def],
  by_cases hx : x = 0,
  { rw [hx, zero_mul, if_pos (eq.refl _), zero_mul] },
  { by_cases hy : y = 0,
    { rw [hy, mul_zero, if_pos (eq.refl _), mul_zero] },
    { rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← with_zero.coe_mul,
        with_zero.coe_inj, ← of_add_add],
      apply congr_arg,
      rw [add_sub, sub_add, sub_sub_assoc_swap, sub_sub, sub_eq_sub_iff_add_eq_add],
      norm_cast,
      rw [← polynomial.nat_degree_mul x.denom_ne_zero y.denom_ne_zero,
        ← polynomial.nat_degree_mul (ratfunc.num_ne_zero (mul_ne_zero hx hy))
          (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
        ← polynomial.nat_degree_mul (ratfunc.num_ne_zero hx) (ratfunc.num_ne_zero hy),
        ← polynomial.nat_degree_mul (mul_ne_zero (ratfunc.num_ne_zero hx) (ratfunc.num_ne_zero hy))
          (x * y).denom_ne_zero, ratfunc.num_denom_mul],}}
end

variable {Fq}
/-- Equivalent fractions have the same valuation. -/
lemma infty_valuation_well_defined {r₁ r₂ s₁ s₂ : polynomial Fq} (hr₁ : r₁ ≠ 0) (hs₁ : s₁ ≠ 0)
  (hr₂ : r₂ ≠ 0) (hs₂ : s₂ ≠ 0) (h_eq : r₁*s₂ = r₂*s₁) :
  (r₁.nat_degree : ℤ) - s₁.nat_degree = (r₂.nat_degree : ℤ) - s₂.nat_degree :=
begin
  rw sub_eq_sub_iff_add_eq_add,
  norm_cast,
  rw [← polynomial.nat_degree_mul hr₁ hs₂, ← polynomial.nat_degree_mul hr₂ hs₁, h_eq],
end

lemma ratfunc.num_add_ne_zero {x y : ratfunc Fq} (hxy : x + y ≠ 0) :
  x.num * y.denom + x.denom * y.num ≠ 0 :=
begin
  intro h_zero,
  have h := ratfunc.num_denom_add x y,
  rw [h_zero, zero_mul] at h,
  exact (mul_ne_zero (ratfunc.num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h,
end

lemma infty_valuation_add_rw {x y : ratfunc Fq} (hxy : x + y ≠ 0) :
  ((x + y).num.nat_degree : ℤ) - ((x + y).denom.nat_degree)  =
  ((x.num) * y.denom + (x.denom) * y.num).nat_degree - ((x.denom) * y.denom).nat_degree :=
infty_valuation_well_defined (ratfunc.num_ne_zero hxy) ((x + y).denom_ne_zero)
    (ratfunc.num_add_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (ratfunc.num_denom_add x y)

lemma infty_valuation_rw {x : ratfunc Fq} (hx : x ≠ 0) {s : polynomial Fq} (hs : s ≠ 0):
  (x.num.nat_degree : ℤ) - (x.denom.nat_degree)  =
  ((x.num)*s).nat_degree - (s*(x.denom)).nat_degree :=
begin
  apply infty_valuation_well_defined (ratfunc.num_ne_zero hx) x.denom_ne_zero
    (mul_ne_zero (ratfunc.num_ne_zero hx) hs) (mul_ne_zero hs x.denom_ne_zero),
  rw mul_assoc,
end

variable (Fq)
lemma infty_valuation.map_add_le_max' (x y : ratfunc Fq) :
  infty_valuation_def Fq (x + y) ≤ max (infty_valuation_def Fq x) (infty_valuation_def Fq y) :=
begin
  by_cases hx : x = 0,
    { rw [hx, zero_add],
      conv_rhs {rw [infty_valuation_def, if_pos (eq.refl _)]},
      rw max_eq_right (with_zero.zero_le (infty_valuation_def Fq y)),
      exact le_refl _, },
    { by_cases hy : y = 0,
        { rw [hy, add_zero],
          conv_rhs {rw [max_comm, infty_valuation_def, if_pos (eq.refl _)]},
          rw max_eq_right (with_zero.zero_le (infty_valuation_def Fq x)),
          exact le_refl _ },
        { by_cases hxy : x + y = 0,
          { rw [infty_valuation_def, if_pos hxy], exact zero_le',},
          { rw [infty_valuation_def, infty_valuation_def, infty_valuation_def, if_neg hx,
              if_neg hy, if_neg hxy, infty_valuation_add_rw hxy,
              infty_valuation_rw hx y.denom_ne_zero, mul_comm y.denom,
              infty_valuation_rw hy x.denom_ne_zero, le_max_iff, with_zero.coe_le_coe,
              multiplicative.of_add_le, with_zero.coe_le_coe, multiplicative.of_add_le,
              sub_le_sub_iff_right, int.coe_nat_le, sub_le_sub_iff_right, int.coe_nat_le,
              ← le_max_iff, mul_comm y.num],
            exact polynomial.nat_degree_add_le _ _, }}},
end

/-- The valuation at infinity on `Fq(t)`. -/
def infty_valuation  : valuation (ratfunc Fq) (with_zero (multiplicative ℤ)) :=
{ to_fun    := infty_valuation_def Fq,
  map_zero' := infty_valuation.map_zero' Fq,
  map_one'  := infty_valuation.map_one' Fq,
  map_mul'  := infty_valuation.map_mul' Fq,
  map_add_le_max'  := infty_valuation.map_add_le_max' Fq }

end infty_valuation

end function_field
