/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen, Ashvni Narayanan
-/
import algebra.order.group.type_tags
import field_theory.ratfunc
import ring_theory.dedekind_domain.integral_closure
import ring_theory.integrally_closed
import topology.algebra.valued_field

/-!
# Function fields

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a function field and the ring of integers corresponding to it.

## Main definitions
 - `function_field Fq F` states that `F` is a function field over the (finite) field `Fq`,
   i.e. it is a finite extension of the field of rational functions in one variable over `Fq`.
 - `function_field.ring_of_integers` defines the ring of integers corresponding to a function field
    as the integral closure of `Fq[X]` in the function field.
 - `function_field.infty_valuation` : The place at infinity on `Fq(t)` is the nonarchimedean
    valuation on `Fq(t)` with uniformizer `1/t`.
 -  `function_field.Fqt_infty` : The completion `Fq((t⁻¹))`  of `Fq(t)` with respect to the
    valuation at infinity.

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
open_locale non_zero_divisors polynomial discrete_valuation

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

lemma algebra_map_injective [algebra Fq[X] F] [algebra (ratfunc Fq) F]
  [is_scalar_tower Fq[X] (ratfunc Fq) F] : function.injective ⇑(algebra_map Fq[X] F) :=
begin
  rw is_scalar_tower.algebra_map_eq Fq[X] (ratfunc Fq) F,
  exact function.injective.comp ((algebra_map (ratfunc Fq) F).injective)
    (is_fraction_ring.injective Fq[X] (ratfunc Fq)),
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

variables [algebra (ratfunc Fq) F] [is_scalar_tower Fq[X] (ratfunc Fq) F]

lemma algebra_map_injective :
  function.injective ⇑(algebra_map Fq[X] (ring_of_integers Fq F)) :=
begin
  have hinj : function.injective ⇑(algebra_map Fq[X] F),
  { rw is_scalar_tower.algebra_map_eq Fq[X] (ratfunc Fq) F,
    exact function.injective.comp ((algebra_map (ratfunc Fq) F).injective)
      (is_fraction_ring.injective Fq[X] (ratfunc Fq)), },
  rw injective_iff_map_eq_zero (algebra_map Fq[X] ↥(ring_of_integers Fq F)),
  intros p hp,
  rw [← subtype.coe_inj, subalgebra.coe_zero] at hp,
  rw injective_iff_map_eq_zero (algebra_map Fq[X] F) at hinj,
  exact hinj p hp,
end

lemma not_is_field : ¬ is_field (ring_of_integers Fq F) :=
by simpa [← ((is_integral_closure.is_integral_algebra Fq[X] F).is_field_iff_is_field
  (algebra_map_injective Fq F))] using (polynomial.not_is_field Fq)

variables [function_field Fq F]

instance : is_fraction_ring (ring_of_integers Fq F) F :=
integral_closure.is_fraction_ring_of_finite_extension (ratfunc Fq) F

instance : is_integrally_closed (ring_of_integers Fq F) :=
integral_closure.is_integrally_closed_of_finite_extension (ratfunc Fq)

instance [is_separable (ratfunc Fq) F] : is_noetherian Fq[X] (ring_of_integers Fq F) :=
is_integral_closure.is_noetherian _ (ratfunc Fq) F _

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
def infty_valuation_def (r : ratfunc Fq) : ℤₘ₀ :=
if r = 0 then 0 else (multiplicative.of_add r.int_degree)

lemma infty_valuation.map_zero' : infty_valuation_def Fq 0 = 0 := if_pos rfl

lemma infty_valuation.map_one' : infty_valuation_def Fq 1 = 1 :=
(if_neg one_ne_zero).trans $
  by rw [ratfunc.int_degree_one, of_add_zero, with_zero.coe_one]

lemma infty_valuation.map_mul' (x y : ratfunc Fq) :
  infty_valuation_def Fq (x * y) = infty_valuation_def Fq x * infty_valuation_def Fq y :=
begin
  rw [infty_valuation_def, infty_valuation_def, infty_valuation_def],
  by_cases hx : x = 0,
  { rw [hx, zero_mul, if_pos (eq.refl _), zero_mul] },
  { by_cases hy : y = 0,
    { rw [hy, mul_zero, if_pos (eq.refl _), mul_zero] },
    { rw [if_neg hx, if_neg hy, if_neg (mul_ne_zero hx hy), ← with_zero.coe_mul,
        with_zero.coe_inj, ← of_add_add, ratfunc.int_degree_mul hx hy], }}
end

lemma infty_valuation.map_add_le_max' (x y : ratfunc Fq) :
  infty_valuation_def Fq (x + y) ≤ max (infty_valuation_def Fq x) (infty_valuation_def Fq y) :=
begin
  by_cases hx : x = 0,
  { rw [hx, zero_add],
    conv_rhs { rw [infty_valuation_def, if_pos (eq.refl _)] },
    rw max_eq_right (with_zero.zero_le (infty_valuation_def Fq y)),
    exact le_refl _ },
  { by_cases hy : y = 0,
    { rw [hy, add_zero],
      conv_rhs { rw [max_comm, infty_valuation_def, if_pos (eq.refl _)] },
      rw max_eq_right (with_zero.zero_le (infty_valuation_def Fq x)),
      exact le_refl _ },
    { by_cases hxy : x + y = 0,
      { rw [infty_valuation_def, if_pos hxy], exact zero_le',},
      { rw [infty_valuation_def, infty_valuation_def, infty_valuation_def, if_neg hx, if_neg hy,
        if_neg hxy],
        rw [le_max_iff,
        with_zero.coe_le_coe, multiplicative.of_add_le, with_zero.coe_le_coe,
        multiplicative.of_add_le, ← le_max_iff],
        exact ratfunc.int_degree_add_le hy hxy }}}
end

@[simp] lemma infty_valuation_of_nonzero {x : ratfunc Fq} (hx : x ≠ 0) :
  infty_valuation_def Fq x = (multiplicative.of_add x.int_degree) :=
by rw [infty_valuation_def, if_neg hx]

/-- The valuation at infinity on `Fq(t)`. -/
def infty_valuation  : valuation (ratfunc Fq) ℤₘ₀ :=
{ to_fun          := infty_valuation_def Fq,
  map_zero'       := infty_valuation.map_zero' Fq,
  map_one'        := infty_valuation.map_one' Fq,
  map_mul'        := infty_valuation.map_mul' Fq,
  map_add_le_max' := infty_valuation.map_add_le_max' Fq }

@[simp] lemma infty_valuation_apply {x : ratfunc Fq} :
  infty_valuation Fq x = infty_valuation_def Fq x := rfl

@[simp] lemma infty_valuation.C {k : Fq} (hk : k ≠ 0) :
  infty_valuation_def Fq (ratfunc.C k) = (multiplicative.of_add (0 : ℤ)) :=
begin
  have hCk : ratfunc.C k ≠ 0 := (map_ne_zero _).mpr hk,
  rw [infty_valuation_def, if_neg hCk, ratfunc.int_degree_C],
end

@[simp] lemma infty_valuation.X :
  infty_valuation_def Fq (ratfunc.X) = (multiplicative.of_add (1 : ℤ)) :=
by rw [infty_valuation_def, if_neg ratfunc.X_ne_zero, ratfunc.int_degree_X]

@[simp] lemma infty_valuation.polynomial {p : Fq[X]} (hp : p ≠ 0) :
  infty_valuation_def Fq (algebra_map Fq[X] (ratfunc Fq) p) =
    (multiplicative.of_add (p.nat_degree : ℤ)) :=
begin
  have hp' : algebra_map Fq[X] (ratfunc Fq) p ≠ 0,
  { rw [ne.def, ratfunc.algebra_map_eq_zero_iff], exact hp },
  rw [infty_valuation_def, if_neg hp', ratfunc.int_degree_polynomial]
end

/-- The valued field `Fq(t)` with the valuation at infinity. -/
def infty_valued_Fqt : valued (ratfunc Fq) ℤₘ₀ :=
valued.mk' $ infty_valuation Fq

lemma infty_valued_Fqt.def {x : ratfunc Fq} :
  @valued.v (ratfunc Fq) _ _ _ (infty_valued_Fqt Fq) x = infty_valuation_def Fq x := rfl

/-- The completion `Fq((t⁻¹))`  of `Fq(t)` with respect to the valuation at infinity. -/
def Fqt_infty := @uniform_space.completion (ratfunc Fq) $ (infty_valued_Fqt Fq).to_uniform_space

instance : field (Fqt_infty Fq) :=
by { letI := infty_valued_Fqt Fq, exact uniform_space.completion.field }

instance : inhabited (Fqt_infty Fq) := ⟨(0 : Fqt_infty Fq)⟩

/-- The valuation at infinity on `k(t)` extends to a valuation on `Fqt_infty`. -/
instance valued_Fqt_infty : valued (Fqt_infty Fq) ℤₘ₀ :=
@valued.valued_completion _ _ _ _ (infty_valued_Fqt Fq)

lemma valued_Fqt_infty.def {x : Fqt_infty Fq} :
  valued.v x = @valued.extension (ratfunc Fq) _ _ _ (infty_valued_Fqt Fq) x := rfl

end infty_valuation

end function_field
