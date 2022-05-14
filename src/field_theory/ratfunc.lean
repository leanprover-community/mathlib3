/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.euclidean_domain
import ring_theory.laurent_series
import ring_theory.localization.fraction_ring
import ring_theory.polynomial.content

/-!
# The field of rational functions

This file defines the field `ratfunc K` of rational functions over a field `K`,
and shows it is the field of fractions of `polynomial K`.

## Main definitions

Working with rational functions as polynomials:
 - `ratfunc.field` provides a field structure
 - `ratfunc.C` is the constant polynomial
 - `ratfunc.X` is the indeterminate
 - `ratfunc.eval` evaluates a rational function given a value for the indeterminate
You can use `is_fraction_ring` API to treat `ratfunc` as the field of fractions of polynomials:
 * `algebra_map K[X] (ratfunc K)` maps polynomials to rational functions
 * `is_fraction_ring.alg_equiv` maps other fields of fractions of `polynomial K` to `ratfunc K`,
    in particular:
 * `fraction_ring.alg_equiv K[X] (ratfunc K)` maps the generic field of
    fraction construction to `ratfunc K`. Combine this with `alg_equiv.restrict_scalars` to change
    the `fraction_ring K[X] ≃ₐ[polynomial K] ratfunc K` to
    `fraction_ring K[X] ≃ₐ[K] ratfunc K`.

Working with rational functions as fractions:
 - `ratfunc.num` and `ratfunc.denom` give the numerator and denominator.
   These values are chosen to be coprime and such that `ratfunc.denom` is monic.

Embedding of rational functions into Laurent series, provided as a coercion, utilizing
the underlying `ratfunc.coe_alg_hom`.

Lifting homomorphisms of polynomials to other types, by mapping and dividing, as long
as the homomorphism retains the non-zero-divisor property:
  - `ratfunc.lift_monoid_with_zero_hom` lifts a `polynomial K →*₀ G₀` to
      a `ratfunc K →*₀ G₀`, where `[comm_ring K] [comm_group_with_zero G₀]`
  - `ratfunc.lift_ring_hom` lifts a `polynomial K →+* L` to a `ratfunc K →+* L`,
      where `[comm_ring K] [field L]`
  - `ratfunc.lift_alg_hom` lifts a `polynomial K →ₐ[S] L` to a `ratfunc K →ₐ[S] L`,
      where `[comm_ring K] [field L] [comm_semiring S] [algebra S K[X]] [algebra S L]`
This is satisfied by injective homs.
We also have lifting homomorphisms of polynomials to other polynomials,
with the same condition on retaining the non-zero-divisor property across the map:
  - `ratfunc.map` lifts `polynomial K →* R[X]` when `[comm_ring K] [comm_ring R]`
  - `ratfunc.map_ring_hom` lifts `polynomial K →+* R[X]` when `[comm_ring K] [comm_ring R]`
  - `ratfunc.map_alg_hom` lifts `polynomial K →ₐ[S] R[X]` when
    `[comm_ring K] [is_domain K] [comm_ring R] [is_domain R]`

We also have a set of recursion and induction principles:
 - `ratfunc.lift_on`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
   if `f` is well-defined in the sense that `p/q = p'/q' → f p q = f p' q'`.
 - `ratfunc.lift_on'`: define a function by mapping a fraction of polynomials `p/q` to `f p q`,
   if `f` is well-defined in the sense that `f (a * p) (a * q) = f p' q'`.
 - `ratfunc.induction_on`: if `P` holds on `p / q` for all polynomials `p q`, then `P` holds on all
   rational functions

We define the degree of a rational function, with values in `ℤ`:
 - `int_degree` is the degree of a rational function, defined as the difference between the
   `nat_degree` of its numerator and the `nat_degree` of its denominator. In particular,
   `int_degree 0 = 0`.

## Implementation notes

To provide good API encapsulation and speed up unification problems,
`ratfunc` is defined as a structure, and all operations are `@[irreducible] def`s

We need a couple of maps to set up the `field` and `is_fraction_ring` structure,
namely `ratfunc.of_fraction_ring`, `ratfunc.to_fraction_ring`, `ratfunc.mk` and
`ratfunc.to_fraction_ring_ring_equiv`.
All these maps get `simp`ed to bundled morphisms like `algebra_map K[X] (ratfunc K)`
and `is_localization.alg_equiv`.

There are separate lifts and maps of homomorphisms, to provide routes of lifting even when
the codomain is not a field or even an integral domain.

## References

* [Kleiman, *Misconceptions about $K_X$*][kleiman1979]
* https://freedommathdance.blogspot.com/2012/11/misconceptions-about-kx.html
* https://stacks.math.columbia.edu/tag/01X1

-/

noncomputable theory
open_locale classical
open_locale non_zero_divisors polynomial

universes u v

variables (K : Type u) [hring : comm_ring K] [hdomain : is_domain K]
include hring

/-- `ratfunc K` is `K(x)`, the field of rational functions over `K`.

The inclusion of polynomials into `ratfunc` is `algebra_map K[X] (ratfunc K)`,
the maps between `ratfunc K` and another field of fractions of `polynomial K`,
especially `fraction_ring K[X]`, are given by `is_localization.algebra_equiv`.
-/
structure ratfunc : Type u := of_fraction_ring ::
(to_fraction_ring : fraction_ring K[X])

namespace ratfunc

variables {K}

section rec

/-! ### Constructing `ratfunc`s and their induction principles -/

lemma of_fraction_ring_injective : function.injective (of_fraction_ring : _ → ratfunc K) :=
λ x y, of_fraction_ring.inj

lemma to_fraction_ring_injective :
  function.injective (to_fraction_ring : _ → fraction_ring K[X])
| ⟨x⟩ ⟨y⟩ rfl := rfl

/-- Non-dependent recursion principle for `ratfunc K`:
To construct a term of `P : Sort*` out of `x : ratfunc K`,
it suffices to provide a constructor `f : Π (p q : K[X]), P`
and a proof that `f p q = f p' q'` for all `p q p' q'` such that `p * q' = p' * q` where
both `q` and `q'` are not zero divisors, stated as `q ∉ K[X]⁰`, `q' ∉ K[X]⁰`.

If considering `K` as an integral domain, this is the same as saying that
we construct a value of `P` for such elements of `ratfunc K` by setting
`lift_on (p / q) f _ = f p q`.

When `[is_domain K]`, one can use `ratfunc.lift_on'`, which has the stronger requirement
of `∀ {p q a : K[X]} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q)`.
-/
@[irreducible] protected def lift_on {P : Sort v} (x : ratfunc K)
  (f : ∀ (p q : K[X]), P)
  (H : ∀ {p q p' q'} (hq : q ∈ K[X]⁰) (hq' : q' ∈ K[X]⁰), p * q' = p' * q →
    f p q = f p' q') :
  P :=
localization.lift_on (to_fraction_ring x) (λ p q, f p q) (λ p p' q q' h, H q.2 q'.2
  (let ⟨⟨c, hc⟩, mul_eq⟩ := (localization.r_iff_exists).mp h in
    mul_cancel_right_coe_non_zero_divisor.mp mul_eq))

lemma lift_on_of_fraction_ring_mk {P : Sort v} (n : K[X]) (d : K[X]⁰)
  (f : ∀ (p q : K[X]), P)
  (H : ∀ {p q p' q'} (hq : q ∈ K[X]⁰) (hq' : q' ∈ K[X]⁰), p * q' = p' * q →
    f p q = f p' q') :
  ratfunc.lift_on (of_fraction_ring (localization.mk n d)) f @H = f n d :=
begin
  unfold ratfunc.lift_on,
  exact localization.lift_on_mk _ _ _ _
end

include hdomain

/-- `ratfunc.mk (p q : K[X])` is `p / q` as a rational function.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `algebra` structure on `ratfunc`;
the `simp` normal form of `mk p q` is `algebra_map _ _ p / algebra_map _ _ q`.
-/
@[irreducible] protected def mk (p q : K[X]) : ratfunc K :=
of_fraction_ring (algebra_map _ _ p / algebra_map _ _ q)

lemma mk_eq_div' (p q : K[X]) :
  ratfunc.mk p q = of_fraction_ring (algebra_map _ _ p / algebra_map _ _ q) :=
by unfold ratfunc.mk

lemma mk_zero (p : K[X]) : ratfunc.mk p 0 = of_fraction_ring 0 :=
by rw [mk_eq_div', ring_hom.map_zero, div_zero]

lemma mk_coe_def (p : K[X]) (q : K[X]⁰) :
  ratfunc.mk p q = of_fraction_ring (is_localization.mk' _ p q) :=
by simp only [mk_eq_div', ← localization.mk_eq_mk', fraction_ring.mk_eq_div]

lemma mk_def_of_mem (p : K[X]) {q} (hq : q ∈ K[X]⁰) :
  ratfunc.mk p q = of_fraction_ring (is_localization.mk' _ p ⟨q, hq⟩) :=
by simp only [← mk_coe_def, set_like.coe_mk]

lemma mk_def_of_ne (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
  ratfunc.mk p q = of_fraction_ring (is_localization.mk' _ p
    ⟨q, mem_non_zero_divisors_iff_ne_zero.mpr hq⟩) :=
mk_def_of_mem p _

lemma mk_eq_localization_mk (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
  ratfunc.mk p q = of_fraction_ring (localization.mk p
    ⟨q, mem_non_zero_divisors_iff_ne_zero.mpr hq⟩) :=
by rw [mk_def_of_ne, localization.mk_eq_mk']

lemma mk_one' (p : K[X]) : ratfunc.mk p 1 = of_fraction_ring (algebra_map _ _ p) :=
by rw [← is_localization.mk'_one (fraction_ring K[X]) p, ← mk_coe_def, submonoid.coe_one]

lemma mk_eq_mk {p q p' q' : K[X]} (hq : q ≠ 0) (hq' : q' ≠ 0) :
  ratfunc.mk p q = ratfunc.mk p' q' ↔ p * q' = p' * q :=
by rw [mk_def_of_ne _ hq, mk_def_of_ne _ hq', of_fraction_ring_injective.eq_iff,
       is_localization.mk'_eq_iff_eq, set_like.coe_mk, set_like.coe_mk,
       (is_fraction_ring.injective K[X] (fraction_ring K[X])).eq_iff]

lemma lift_on_mk {P : Sort v} (p q : K[X])
  (f : ∀ (p q : K[X]), P) (f0 : ∀ p, f p 0 = f 0 1)
  (H' : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), p * q' = p' * q → f p q = f p' q')
  (H : ∀ {p q p' q'} (hq : q ∈ K[X]⁰) (hq' : q' ∈ K[X]⁰), p * q' = p' * q →
    f p q = f p' q' :=
    λ p q p' q' hq hq' h, H' (non_zero_divisors.ne_zero hq) (non_zero_divisors.ne_zero hq') h) :
  (ratfunc.mk p q).lift_on f @H = f p q :=
begin
  by_cases hq : q = 0,
  { subst hq,
    simp only [mk_zero, f0, ← localization.mk_zero 1, localization.lift_on_mk,
               lift_on_of_fraction_ring_mk, submonoid.coe_one], },
  { simp only [mk_eq_localization_mk _ hq, localization.lift_on_mk, lift_on_of_fraction_ring_mk,
               set_like.coe_mk] }
end

lemma lift_on_condition_of_lift_on'_condition {P : Sort v} {f : ∀ (p q : K[X]), P}
  (H : ∀ {p q a} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q)
  ⦃p q p' q' : K[X]⦄ (hq : q ≠ 0) (hq' : q' ≠ 0) (h : p * q' = p' * q) :
  f p q = f p' q' :=
begin
  have H0 : f 0 q = f 0 q',
  { calc f 0 q = f (q' * 0) (q' * q) : (H hq hq').symm
           ... = f (q * 0) (q * q') : by rw [mul_zero, mul_zero, mul_comm]
           ... = f 0 q' : H hq' hq },
  by_cases hp : p = 0,
  { simp only [hp, hq, zero_mul, or_false, zero_eq_mul] at ⊢ h, rw [h, H0] },
  by_cases hp' : p' = 0,
  { simpa only [hp, hp', hq', zero_mul, or_self, mul_eq_zero] using h },
  calc f p q = f (p' * p) (p' * q) : (H hq hp').symm
         ... = f (p * p') (p * q') : by rw [mul_comm p p', h]
         ... = f p' q' : H hq' hp
end

-- f
/-- Non-dependent recursion principle for `ratfunc K`: if `f p q : P` for all `p q`,
such that `f (a * p) (a * q) = f p q`, then we can find a value of `P`
for all elements of `ratfunc K` by setting `lift_on' (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on'` assume `f p 0 = f 0 1`.
-/
@[irreducible] protected def lift_on' {P : Sort v} (x : ratfunc K)
  (f : ∀ (p q : K[X]), P)
  (H : ∀ {p q a} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q) :
  P :=
x.lift_on f (λ p q p' q' hq hq', lift_on_condition_of_lift_on'_condition @H
  (non_zero_divisors.ne_zero hq) (non_zero_divisors.ne_zero hq'))

lemma lift_on'_mk {P : Sort v} (p q : K[X])
  (f : ∀ (p q : K[X]), P) (f0 : ∀ p, f p 0 = f 0 1)
  (H : ∀ {p q a} (hq : q ≠ 0) (ha : a ≠ 0), f (a * p) (a * q) = f p q) :
  (ratfunc.mk p q).lift_on' f @H = f p q :=
begin
  rw [ratfunc.lift_on', ratfunc.lift_on_mk _ _ _ f0],
  exact lift_on_condition_of_lift_on'_condition @H
end

/-- Induction principle for `ratfunc K`: if `f p q : P (ratfunc.mk p q)` for all `p q`,
then `P` holds on all elements of `ratfunc K`.

See also `induction_on`, which is a recursion principle defined in terms of `algebra_map`.
-/
@[irreducible] protected lemma induction_on' {P : ratfunc K → Prop} :
  Π (x : ratfunc K) (f : ∀ (p q : K[X]) (hq : q ≠ 0), P (ratfunc.mk p q)), P x
| ⟨x⟩ f := localization.induction_on x
  (λ ⟨p, q⟩, by simpa only [mk_coe_def, localization.mk_eq_mk'] using f p q
    (mem_non_zero_divisors_iff_ne_zero.mp q.2))

end rec

section field

/-! ### Defining the field structure -/

/-- The zero rational function. -/
@[irreducible] protected def zero : ratfunc K := ⟨0⟩
instance : has_zero (ratfunc K) := ⟨ratfunc.zero⟩
lemma of_fraction_ring_zero : (of_fraction_ring 0 : ratfunc K) = 0 :=
by unfold has_zero.zero ratfunc.zero

/-- Addition of rational functions. -/
@[irreducible] protected def add : ratfunc K → ratfunc K → ratfunc K
| ⟨p⟩ ⟨q⟩ := ⟨p + q⟩
instance : has_add (ratfunc K) := ⟨ratfunc.add⟩
lemma of_fraction_ring_add (p q : fraction_ring K[X]) :
  of_fraction_ring (p + q) = of_fraction_ring p + of_fraction_ring q :=
by unfold has_add.add ratfunc.add

/-- Subtraction of rational functions. -/
@[irreducible] protected def sub : ratfunc K → ratfunc K → ratfunc K
| ⟨p⟩ ⟨q⟩ := ⟨p - q⟩
instance : has_sub (ratfunc K) := ⟨ratfunc.sub⟩
lemma of_fraction_ring_sub (p q : fraction_ring K[X]) :
  of_fraction_ring (p - q) = of_fraction_ring p - of_fraction_ring q :=
by unfold has_sub.sub ratfunc.sub

/-- Additive inverse of a rational function. -/
@[irreducible] protected def neg : ratfunc K → ratfunc K
| ⟨p⟩ := ⟨-p⟩
instance : has_neg (ratfunc K) := ⟨ratfunc.neg⟩
lemma of_fraction_ring_neg (p : fraction_ring K[X]) :
  of_fraction_ring (-p) = - of_fraction_ring p :=
by unfold has_neg.neg ratfunc.neg

/-- The multiplicative unit of rational functions. -/
@[irreducible] protected def one : ratfunc K := ⟨1⟩
instance : has_one (ratfunc K) := ⟨ratfunc.one⟩
lemma of_fraction_ring_one : (of_fraction_ring 1 : ratfunc K) = 1 :=
by unfold has_one.one ratfunc.one

/-- Multiplication of rational functions. -/
@[irreducible] protected def mul : ratfunc K → ratfunc K → ratfunc K
| ⟨p⟩ ⟨q⟩ := ⟨p * q⟩
instance : has_mul (ratfunc K) := ⟨ratfunc.mul⟩
lemma of_fraction_ring_mul (p q : fraction_ring K[X]) :
  of_fraction_ring (p * q) = of_fraction_ring p * of_fraction_ring q :=
by unfold has_mul.mul ratfunc.mul

include hdomain

/-- Division of rational functions. -/
@[irreducible] protected def div : ratfunc K → ratfunc K → ratfunc K
| ⟨p⟩ ⟨q⟩ := ⟨p / q⟩
instance : has_div (ratfunc K) := ⟨ratfunc.div⟩
lemma of_fraction_ring_div (p q : fraction_ring K[X]) :
  of_fraction_ring (p / q) = of_fraction_ring p / of_fraction_ring q :=
by unfold has_div.div ratfunc.div

/-- Multiplicative inverse of a rational function. -/
@[irreducible] protected def inv : ratfunc K → ratfunc K
| ⟨p⟩ := ⟨p⁻¹⟩
instance : has_inv (ratfunc K) := ⟨ratfunc.inv⟩
lemma of_fraction_ring_inv (p : fraction_ring K[X]) :
  of_fraction_ring (p⁻¹) = (of_fraction_ring p)⁻¹ :=
by unfold has_inv.inv ratfunc.inv

-- Auxiliary lemma for the `field` instance
lemma mul_inv_cancel : ∀ {p : ratfunc K} (hp : p ≠ 0), p * p⁻¹ = 1
| ⟨p⟩ h := have p ≠ 0 := λ hp, h $ by rw [hp, of_fraction_ring_zero],
by simpa only [← of_fraction_ring_inv, ← of_fraction_ring_mul, ← of_fraction_ring_one]
  using _root_.mul_inv_cancel this

section has_scalar
omit hdomain

variables {R : Type*}

/-- Scalar multiplication of rational functions. -/
@[irreducible] protected def smul [has_scalar R (fraction_ring K[X])] :
  R → ratfunc K → ratfunc K
| r ⟨p⟩ := ⟨r • p⟩

instance [has_scalar R (fraction_ring K[X])] : has_scalar R (ratfunc K) :=
⟨ratfunc.smul⟩

lemma of_fraction_ring_smul [has_scalar R (fraction_ring K[X])]
  (c : R) (p : fraction_ring K[X]) :
  of_fraction_ring (c • p) = c • of_fraction_ring p :=
by unfold has_scalar.smul ratfunc.smul
lemma to_fraction_ring_smul [has_scalar R (fraction_ring K[X])]
  (c : R) (p : ratfunc K) :
  to_fraction_ring (c • p) = c • to_fraction_ring p :=
by { cases p, rw ←of_fraction_ring_smul }

lemma smul_eq_C_smul (x : ratfunc K) (r : K) :
  r • x = polynomial.C r • x :=
begin
  cases x,
  induction x,
  { rw [←of_fraction_ring_smul, ←of_fraction_ring_smul, localization.smul_mk, localization.smul_mk,
        smul_eq_mul, polynomial.smul_eq_C_mul] },
  { simp only }
end

include hdomain
variables [monoid R] [distrib_mul_action R K[X]]
variables [htower : is_scalar_tower R K[X] K[X]]
include htower

lemma mk_smul (c : R) (p q : K[X]) :
  ratfunc.mk (c • p) q = c • ratfunc.mk p q :=
begin
  by_cases hq : q = 0,
  { rw [hq, mk_zero, mk_zero, ←of_fraction_ring_smul, smul_zero] },
  { rw [mk_eq_localization_mk _ hq, mk_eq_localization_mk _ hq,
         ←localization.smul_mk, ←of_fraction_ring_smul] }
end

instance : is_scalar_tower R K[X] (ratfunc K) :=
⟨λ c p q, q.induction_on' (λ q r _, by rw [← mk_smul, smul_assoc, mk_smul, mk_smul])⟩

end has_scalar

variables (K)

omit hdomain

instance [subsingleton K] : subsingleton (ratfunc K) :=
to_fraction_ring_injective.subsingleton

instance : inhabited (ratfunc K) :=
⟨0⟩
instance [nontrivial K] : nontrivial (ratfunc K) :=
of_fraction_ring_injective.nontrivial

/-- `ratfunc K` is isomorphic to the field of fractions of `polynomial K`, as rings.

This is an auxiliary definition; `simp`-normal form is `is_localization.alg_equiv`.
-/
@[simps apply] def to_fraction_ring_ring_equiv : ratfunc K ≃+* fraction_ring K[X] :=
{ to_fun := to_fraction_ring,
  inv_fun := of_fraction_ring,
  left_inv := λ ⟨_⟩, rfl,
  right_inv := λ _, rfl,
  map_add' := λ ⟨_⟩ ⟨_⟩, by simp [←of_fraction_ring_add],
  map_mul' := λ ⟨_⟩ ⟨_⟩, by simp [←of_fraction_ring_mul] }

omit hring

/-- Solve equations for `ratfunc K` by working in `fraction_ring K[X]`. -/
meta def frac_tac : tactic unit :=
`[repeat { rintro (⟨⟩ : ratfunc _) },
  simp only [← of_fraction_ring_zero, ← of_fraction_ring_add, ← of_fraction_ring_sub,
    ← of_fraction_ring_neg, ← of_fraction_ring_one, ← of_fraction_ring_mul, ← of_fraction_ring_div,
    ← of_fraction_ring_inv,
    add_assoc, zero_add, add_zero, mul_assoc, mul_zero, mul_one, mul_add, inv_zero,
    add_comm, add_left_comm, mul_comm, mul_left_comm, sub_eq_add_neg, div_eq_mul_inv,
    add_mul, zero_mul, one_mul, neg_mul, mul_neg, add_right_neg]]

/-- Solve equations for `ratfunc K` by applying `ratfunc.induction_on`. -/
meta def smul_tac : tactic unit :=
`[repeat { rintro (⟨⟩ : ratfunc _) <|> intro },
  simp_rw [←of_fraction_ring_smul],
  simp only [add_comm, mul_comm, zero_smul, succ_nsmul, zsmul_eq_mul, mul_add, mul_one, mul_zero,
    neg_add, mul_neg,
    int.of_nat_eq_coe, int.coe_nat_succ, int.cast_zero, int.cast_add, int.cast_one,
    int.cast_neg_succ_of_nat, int.cast_coe_nat,
    localization.mk_zero, localization.add_mk_self, localization.neg_mk,
    of_fraction_ring_zero, ← of_fraction_ring_add, ← of_fraction_ring_neg]]

include hring

instance : comm_ring (ratfunc K) :=
{ add := (+),
  add_assoc := by frac_tac,
  add_comm := by frac_tac,
  zero := 0,
  zero_add := by frac_tac,
  add_zero := by frac_tac,
  neg := has_neg.neg,
  add_left_neg := by frac_tac,
  sub := has_sub.sub,
  sub_eq_add_neg := by frac_tac,
  mul := (*),
  mul_assoc := by frac_tac,
  mul_comm := by frac_tac,
  left_distrib := by frac_tac,
  right_distrib := by frac_tac,
  one := 1,
  one_mul := by frac_tac,
  mul_one := by frac_tac,
  nsmul := (•),
  nsmul_zero' := by smul_tac,
  nsmul_succ' := λ _, by smul_tac,
  zsmul := (•),
  zsmul_zero' := by smul_tac,
  zsmul_succ' := λ _, by smul_tac,
  zsmul_neg' := λ _, by smul_tac,
  npow := npow_rec }

variables {K}

section lift_hom

variables {G₀ L R S F : Type*} [comm_group_with_zero G₀] [field L] [comm_ring R] [comm_ring S]
omit hring

/-- Lift a monoid homomorphism that maps polynomials `φ : R[X] →* S[X]`
to a `ratfunc R →* ratfunc S`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def map [monoid_hom_class F R[X] S[X]] (φ : F)
  (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
  ratfunc R →* ratfunc S :=
{ to_fun := λ f, ratfunc.lift_on f (λ n d, if h : φ d ∈ S[X]⁰
    then of_fraction_ring (localization.mk (φ n) ⟨φ d, h⟩) else 0) $ λ p q p' q' hq hq' h,
    begin
      rw [dif_pos, dif_pos, of_fraction_ring.inj_eq, localization.mk_eq_mk_iff],
      rotate,
      { exact hφ hq' },
      { exact hφ hq },
      refine localization.r_of_eq _,
      simpa only [map_mul] using (congr_arg φ h).symm,
    end,
  map_one' := begin
    rw [←of_fraction_ring_one, ←localization.mk_one, lift_on_of_fraction_ring_mk, dif_pos],
    { simpa using of_fraction_ring_one },
    { simpa using submonoid.one_mem _}
  end,
  map_mul' := λ x y, begin
    cases x, cases y, induction x with p q, induction y with p' q',
    { have hq : φ q ∈ S[X]⁰ := hφ q.prop,
      have hq' : φ q' ∈ S[X]⁰ := hφ q'.prop,
      have hqq' : φ ↑(q * q') ∈ S[X]⁰,
      { simpa using submonoid.mul_mem _ hq hq' },
      simp_rw [←of_fraction_ring_mul, localization.mk_mul, lift_on_of_fraction_ring_mk, dif_pos hq,
               dif_pos hq', dif_pos hqq', ←of_fraction_ring_mul, submonoid.coe_mul, map_mul,
               localization.mk_mul, submonoid.mk_mul_mk] },
    { refl },
    { refl }
  end }

lemma map_apply_of_fraction_ring_mk [monoid_hom_class F R[X] S[X]] (φ : F)
  (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
  map φ hφ (of_fraction_ring (localization.mk n d)) =
    of_fraction_ring (localization.mk (φ n) ⟨φ d, hφ d.prop⟩) :=
begin
  convert lift_on_of_fraction_ring_mk _ _ _ _,
  rw dif_pos
end

lemma map_injective [monoid_hom_class F R[X] S[X]] (φ : F)
  (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) (hf : function.injective φ) :
  function.injective (map φ hφ) :=
begin
  rintro ⟨x⟩ ⟨y⟩ h, induction x, induction y,
  { simpa only [map_apply_of_fraction_ring_mk, of_fraction_ring_injective.eq_iff,
                localization.mk_eq_mk_iff, localization.r_iff_exists,
                mul_cancel_right_coe_non_zero_divisor, exists_const, set_like.coe_mk, ←map_mul,
                hf.eq_iff] using h },
  { refl },
  { refl }
end

/-- Lift a ring homomorphism that maps polynomials `φ : R[X] →+* S[X]`
to a `ratfunc R →+* ratfunc S`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def map_ring_hom [ring_hom_class F R[X] S[X]] (φ : F)
  (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) : ratfunc R →+* ratfunc S :=
{ map_zero' := begin
    simp_rw [monoid_hom.to_fun_eq_coe, ←of_fraction_ring_zero,
             ←localization.mk_zero (1 : R[X]⁰),
             ←localization.mk_zero (1 : S[X]⁰), map_apply_of_fraction_ring_mk, map_zero,
             localization.mk_eq_mk', is_localization.mk'_zero],
  end,
  map_add' := begin
    rintro ⟨x⟩ ⟨y⟩, induction x, induction y,
    { simp only [←of_fraction_ring_add, localization.add_mk, map_add, set_like.coe_mk, map_mul,
                 monoid_hom.to_fun_eq_coe, map_apply_of_fraction_ring_mk, submonoid.mk_mul_mk,
                 submonoid.coe_mul] },
    { refl },
    { refl }
  end,
  ..map φ hφ }

lemma coe_map_ring_hom_eq_coe_map [ring_hom_class F R[X] S[X]] (φ : F)
  (hφ : R[X]⁰ ≤ S[X]⁰.comap φ) :
  (map_ring_hom φ hφ : ratfunc R → ratfunc S) = map φ hφ := rfl

-- TODO: Generalize to `fun_like` classes,
/-- Lift an monoid with zero homomorphism `polynomial R →*₀ G₀` to a `ratfunc R →*₀ G₀`
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. --/
def lift_monoid_with_zero_hom (φ : R[X] →*₀ G₀) (hφ : R[X]⁰ ≤ G₀⁰.comap φ) :
  ratfunc R →*₀ G₀ :=
{ to_fun := λ f, ratfunc.lift_on f (λ p q, φ p / (φ q)) $ λ p q p' q' hq hq' h, begin
    casesI subsingleton_or_nontrivial R,
    { rw [subsingleton.elim p q, subsingleton.elim p' q, subsingleton.elim q' q] },
    rw [div_eq_div_iff, ←map_mul, h, map_mul];
    exact non_zero_divisors.ne_zero (hφ ‹_›),
  end,
  map_one' := by { rw [←of_fraction_ring_one, ←localization.mk_one, lift_on_of_fraction_ring_mk],
                   simp only [map_one, submonoid.coe_one, div_one] },
  map_mul' := λ x y, by { cases x, cases y, induction x with p q, induction y with p' q',
    { rw [←of_fraction_ring_mul, localization.mk_mul],
      simp only [lift_on_of_fraction_ring_mk, div_mul_div_comm, map_mul, submonoid.coe_mul] },
    { refl },
    { refl } },
  map_zero' := by { rw [←of_fraction_ring_zero, ←localization.mk_zero (1 : R[X]⁰),
                         lift_on_of_fraction_ring_mk],
                    simp only [map_zero, zero_div] } }

lemma lift_monoid_with_zero_hom_apply_of_fraction_ring_mk (φ : R[X] →*₀ G₀)
  (hφ : R[X]⁰ ≤ G₀⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
  lift_monoid_with_zero_hom φ hφ (of_fraction_ring (localization.mk n d)) = φ n / φ d :=
lift_on_of_fraction_ring_mk _ _ _ _

lemma lift_monoid_with_zero_hom_injective [nontrivial R] (φ : R[X] →*₀ G₀)
  (hφ : function.injective φ)
  (hφ' : R[X]⁰ ≤ G₀⁰.comap φ :=
    non_zero_divisors_le_comap_non_zero_divisors_of_injective _ hφ) :
  function.injective (lift_monoid_with_zero_hom φ hφ') :=
begin
  rintro ⟨x⟩ ⟨y⟩, induction x, induction y,
  { simp_rw [lift_monoid_with_zero_hom_apply_of_fraction_ring_mk, localization.mk_eq_mk_iff],
    intro h,
    refine localization.r_of_eq _,
    simpa only [←hφ.eq_iff, map_mul] using mul_eq_mul_of_div_eq_div _ _ _ _ h.symm;
    exact (map_ne_zero_of_mem_non_zero_divisors _ hφ (set_like.coe_mem _)) },
  { exact λ _, rfl },
  { exact λ _, rfl }
end

/-- Lift an injective ring homomorphism `polynomial R →+* L` to a `ratfunc R →+* L`
by mapping both the numerator and denominator and quotienting them. --/
def lift_ring_hom (φ : R[X] →+* L) (hφ : R[X]⁰ ≤ L⁰.comap φ) : ratfunc R →+* L :=
{ map_add' := λ x y, by { simp only [monoid_with_zero_hom.to_fun_eq_coe],
    casesI subsingleton_or_nontrivial R,
    { rw [subsingleton.elim (x + y) y, subsingleton.elim x 0, map_zero, zero_add] },
    cases x, cases y, induction x with p q, induction y with p' q',
    { rw [←of_fraction_ring_add, localization.add_mk],
      simp only [ring_hom.to_monoid_with_zero_hom_eq_coe,
                 lift_monoid_with_zero_hom_apply_of_fraction_ring_mk],
      rw [div_add_div, div_eq_div_iff],
      { rw [mul_comm _ p, mul_comm _ p', mul_comm _ (φ p'), add_comm],
        simp only [map_add, map_mul, submonoid.coe_mul] },
      all_goals {
        try { simp only [←map_mul, ←submonoid.coe_mul] },
        exact non_zero_divisors.ne_zero (hφ (set_like.coe_mem _)) } },
    { refl },
    { refl } },
  ..lift_monoid_with_zero_hom φ.to_monoid_with_zero_hom hφ }

lemma lift_ring_hom_apply_of_fraction_ring_mk (φ : R[X] →+* L)
  (hφ : R[X]⁰ ≤ L⁰.comap φ) (n : R[X]) (d : R[X]⁰) :
  lift_ring_hom φ hφ (of_fraction_ring (localization.mk n d)) = φ n / φ d :=
lift_monoid_with_zero_hom_apply_of_fraction_ring_mk _ _ _ _

lemma lift_ring_hom_injective [nontrivial R] (φ : R[X] →+* L) (hφ : function.injective φ)
  (hφ' : R[X]⁰ ≤ L⁰.comap φ :=
    non_zero_divisors_le_comap_non_zero_divisors_of_injective _ hφ) :
  function.injective (lift_ring_hom φ hφ') :=
lift_monoid_with_zero_hom_injective _ hφ

end lift_hom

variables (K)
include hdomain

instance : field (ratfunc K) :=
{ inv := has_inv.inv,
  inv_zero := by frac_tac,
  div := (/),
  div_eq_mul_inv := by frac_tac,
  mul_inv_cancel := λ _, mul_inv_cancel,
  zpow := zpow_rec,
  .. ratfunc.comm_ring K,
  .. ratfunc.nontrivial K }

end field

section is_fraction_ring

/-! ### `ratfunc` as field of fractions of `polynomial` -/

include hdomain

instance (R : Type*) [comm_semiring R] [algebra R K[X]] :
  algebra R (ratfunc K) :=
{ to_fun := λ x, ratfunc.mk (algebra_map _ _ x) 1,
  map_add' := λ x y, by simp only [mk_one', ring_hom.map_add, of_fraction_ring_add],
  map_mul' := λ x y, by simp only [mk_one', ring_hom.map_mul, of_fraction_ring_mul],
  map_one' := by simp only [mk_one', ring_hom.map_one, of_fraction_ring_one],
  map_zero' := by simp only [mk_one', ring_hom.map_zero, of_fraction_ring_zero],
  smul := (•),
  smul_def' := λ c x, x.induction_on' $ λ p q hq,
    by simp_rw [mk_one', ← mk_smul, mk_def_of_ne (c • p) hq, mk_def_of_ne p hq,
      ← of_fraction_ring_mul, is_localization.mul_mk'_eq_mk'_of_mul, algebra.smul_def],
  commutes' := λ c x, mul_comm _ _ }

variables {K}

lemma mk_one (x : K[X]) : ratfunc.mk x 1 = algebra_map _ _ x := rfl

lemma of_fraction_ring_algebra_map (x : K[X]) :
  of_fraction_ring (algebra_map _ (fraction_ring K[X]) x) = algebra_map _ _ x :=
by rw [← mk_one, mk_one']

@[simp] lemma mk_eq_div (p q : K[X]) :
  ratfunc.mk p q = (algebra_map _ _ p / algebra_map _ _ q) :=
by simp only [mk_eq_div', of_fraction_ring_div, of_fraction_ring_algebra_map]

@[simp] lemma div_smul {R} [monoid R] [distrib_mul_action R K[X]]
  [is_scalar_tower R K[X] K[X]] (c : R) (p q : K[X]) :
  algebra_map _ (ratfunc K) (c • p) / (algebra_map _ _ q) =
    c • (algebra_map _ _ p / algebra_map _ _ q) :=
by rw [←mk_eq_div, mk_smul, mk_eq_div]

lemma algebra_map_apply {R : Type*} [comm_semiring R] [algebra R K[X]] (x : R) :
  algebra_map R (ratfunc K) x = (algebra_map _ _ (algebra_map R K[X] x)) /
    (algebra_map K[X] _ 1) :=
by { rw [←mk_eq_div], refl }

lemma map_apply_div_ne_zero {R F : Type*} [comm_ring R] [is_domain R]
  [monoid_hom_class F K[X] R[X]] (φ : F)
  (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) (hq : q ≠ 0) :
  map φ hφ (algebra_map _ _ p / algebra_map _ _ q) =
    algebra_map _ _ (φ p) / algebra_map _ _ (φ q) :=
begin
  have hq' : φ q ≠ 0 := non_zero_divisors.ne_zero (hφ (mem_non_zero_divisors_iff_ne_zero.mpr hq)),
  simp only [←mk_eq_div, mk_eq_localization_mk _ hq, map_apply_of_fraction_ring_mk,
             mk_eq_localization_mk _ hq', set_like.coe_mk],
end

@[simp] lemma map_apply_div {R F : Type*} [comm_ring R] [is_domain R]
  [monoid_with_zero_hom_class F K[X] R[X]] (φ : F)
  (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (p q : K[X]) :
  map φ hφ (algebra_map _ _ p / algebra_map _ _ q) =
    algebra_map _ _ (φ p) / algebra_map _ _ (φ q) :=
begin
  rcases eq_or_ne q 0 with rfl|hq,
  { have : (0 : ratfunc K) = algebra_map K[X] _ 0 / algebra_map K[X] _ 1,
    { simp },
    rw [map_zero, map_zero, map_zero, div_zero, div_zero, this, map_apply_div_ne_zero,
        map_one, map_one, div_one, map_zero, map_zero],
    exact one_ne_zero },
  exact map_apply_div_ne_zero _ _ _ _ hq
end

@[simp] lemma lift_monoid_with_zero_hom_apply_div {L : Type*} [comm_group_with_zero L]
  (φ : monoid_with_zero_hom K[X] L)
  (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
  lift_monoid_with_zero_hom φ hφ (algebra_map _ _ p / algebra_map _ _ q) = φ p / φ q :=
begin
  rcases eq_or_ne q 0 with rfl|hq,
  { simp only [div_zero, map_zero] },
  simpa only [←mk_eq_div, mk_eq_localization_mk _ hq,
               lift_monoid_with_zero_hom_apply_of_fraction_ring_mk],
end

@[simp] lemma lift_ring_hom_apply_div {L : Type*} [field L]
  (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (p q : K[X]) :
  lift_ring_hom φ hφ (algebra_map _ _ p / algebra_map _ _ q) = φ p / φ q :=
lift_monoid_with_zero_hom_apply_div _ _ _ _

variables (K)

lemma of_fraction_ring_comp_algebra_map :
  of_fraction_ring ∘ algebra_map K[X] (fraction_ring K[X]) = algebra_map _ _ :=
funext of_fraction_ring_algebra_map

lemma algebra_map_injective : function.injective (algebra_map K[X] (ratfunc K)) :=
begin
  rw ← of_fraction_ring_comp_algebra_map,
  exact of_fraction_ring_injective.comp (is_fraction_ring.injective _ _),
end

@[simp] lemma algebra_map_eq_zero_iff {x : K[X]} :
  algebra_map K[X] (ratfunc K) x = 0 ↔ x = 0 :=
⟨(injective_iff_map_eq_zero _).mp (algebra_map_injective K) _, λ hx, by rw [hx, ring_hom.map_zero]⟩

variables {K}

lemma algebra_map_ne_zero {x : K[X]} (hx : x ≠ 0) :
  algebra_map K[X] (ratfunc K) x ≠ 0 :=
mt (algebra_map_eq_zero_iff K).mp hx

section lift_alg_hom

variables {L R S : Type*} [field L] [comm_ring R] [is_domain R] [comm_semiring S]
  [algebra S K[X]] [algebra S L] [algebra S R[X]]
  (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ)

/-- Lift an algebra homomorphism that maps polynomials `φ : polynomial K →ₐ[S] R[X]`
to a `ratfunc K →ₐ[S] ratfunc R`,
on the condition that `φ` maps non zero divisors to non zero divisors,
by mapping both the numerator and denominator and quotienting them. -/
def map_alg_hom (φ : K[X] →ₐ[S] R[X])
  (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) : ratfunc K →ₐ[S] ratfunc R :=
{ commutes' := λ r, by simp_rw [ring_hom.to_fun_eq_coe, coe_map_ring_hom_eq_coe_map,
      algebra_map_apply r, map_apply_div, map_one, alg_hom.commutes],
  ..map_ring_hom φ hφ }

lemma coe_map_alg_hom_eq_coe_map (φ : K[X] →ₐ[S] R[X])
  (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) :
  (map_alg_hom φ hφ : ratfunc K → ratfunc R) = map φ hφ := rfl

/-- Lift an injective algebra homomorphism `polynomial K →ₐ[S] L` to a `ratfunc K →ₐ[S] L`
by mapping both the numerator and denominator and quotienting them. --/
def lift_alg_hom : ratfunc K →ₐ[S] L :=
{ commutes' := λ r, by simp_rw [ring_hom.to_fun_eq_coe, alg_hom.to_ring_hom_eq_coe,
    algebra_map_apply r, lift_ring_hom_apply_div, alg_hom.coe_to_ring_hom, map_one,
    div_one, alg_hom.commutes],
  ..lift_ring_hom φ.to_ring_hom hφ }

lemma lift_alg_hom_apply_of_fraction_ring_mk (n : K[X]) (d : K[X]⁰) :
  lift_alg_hom φ hφ (of_fraction_ring (localization.mk n d)) = φ n / φ d :=
lift_monoid_with_zero_hom_apply_of_fraction_ring_mk _ _ _ _

lemma lift_alg_hom_injective (φ : K[X] →ₐ[S] L) (hφ : function.injective φ)
  (hφ' : K[X]⁰ ≤ L⁰.comap φ :=
    non_zero_divisors_le_comap_non_zero_divisors_of_injective _ hφ) :
  function.injective (lift_alg_hom φ hφ') :=
lift_monoid_with_zero_hom_injective _ hφ

@[simp] lemma lift_alg_hom_apply_div (p q : K[X]) :
  lift_alg_hom φ hφ (algebra_map _ _ p / algebra_map _ _ q) = φ p / φ q :=
lift_monoid_with_zero_hom_apply_div _ _ _ _

end lift_alg_hom

variables (K)

omit hdomain

include hdomain

/-- `ratfunc K` is the field of fractions of the polynomials over `K`. -/
instance : is_fraction_ring K[X] (ratfunc K) :=
{ map_units := λ y, by rw ← of_fraction_ring_algebra_map;
    exact (to_fraction_ring_ring_equiv K).symm.to_ring_hom.is_unit_map
      (is_localization.map_units _ y),
  eq_iff_exists := λ x y, by rw [← of_fraction_ring_algebra_map, ← of_fraction_ring_algebra_map];
    exact (to_fraction_ring_ring_equiv K).symm.injective.eq_iff.trans
      (is_localization.eq_iff_exists _ _),
  surj := by { rintro ⟨z⟩, convert is_localization.surj K[X]⁰ z, ext ⟨x, y⟩,
    simp only [← of_fraction_ring_algebra_map, function.comp_app, ← of_fraction_ring_mul] } }

variables {K}

@[simp] lemma lift_on_div {P : Sort v} (p q : K[X])
  (f : ∀ (p q : K[X]), P) (f0 : ∀ p, f p 0 = f 0 1)
  (H' : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), p * q' = p' * q → f p q = f p' q')
  (H : ∀ {p q p' q'} (hq : q ∈ K[X]⁰) (hq' : q' ∈ K[X]⁰), p * q' = p' * q →
  f p q = f p' q' :=
  λ p q p' q' hq hq' h, H' (non_zero_divisors.ne_zero hq) (non_zero_divisors.ne_zero hq') h) :
  (algebra_map _ (ratfunc K) p / algebra_map _ _ q).lift_on f @H = f p q :=
by rw [← mk_eq_div, lift_on_mk _ _ f f0 @H']

@[simp] lemma lift_on'_div {P : Sort v} (p q : K[X])
  (f : ∀ (p q : K[X]), P) (f0 : ∀ p, f p 0 = f 0 1) (H) :
  (algebra_map _ (ratfunc K) p / algebra_map _ _ q).lift_on' f @H = f p q :=
begin
  rw [ratfunc.lift_on', lift_on_div _ _ _ f0],
  exact lift_on_condition_of_lift_on'_condition @H
end

/-- Induction principle for `ratfunc K`: if `f p q : P (p / q)` for all `p q : polynomial K`,
then `P` holds on all elements of `ratfunc K`.

See also `induction_on'`, which is a recursion principle defined in terms of `ratfunc.mk`.
-/
protected lemma induction_on {P : ratfunc K → Prop} (x : ratfunc K)
  (f : ∀ (p q : K[X]) (hq : q ≠ 0),
    P (algebra_map _ (ratfunc K) p / algebra_map _ _ q)) :
  P x :=
x.induction_on' (λ p q hq, by simpa using f p q hq)

lemma of_fraction_ring_mk' (x : K[X]) (y : K[X]⁰) :
  of_fraction_ring (is_localization.mk' _ x y) = is_localization.mk' (ratfunc K) x y :=
by rw [is_fraction_ring.mk'_eq_div, is_fraction_ring.mk'_eq_div, ← mk_eq_div', ← mk_eq_div]

@[simp] lemma of_fraction_ring_eq :
  (of_fraction_ring : fraction_ring K[X] → ratfunc K) =
    is_localization.alg_equiv K[X]⁰ _ _ :=
funext $ λ x, localization.induction_on x $ λ x,
by simp only [is_localization.alg_equiv_apply, is_localization.ring_equiv_of_ring_equiv_apply,
    ring_equiv.to_fun_eq_coe, localization.mk_eq_mk'_apply, is_localization.map_mk',
    of_fraction_ring_mk', ring_equiv.coe_to_ring_hom, ring_equiv.refl_apply, set_like.eta]

@[simp] lemma to_fraction_ring_eq :
  (to_fraction_ring : ratfunc K → fraction_ring K[X]) =
    is_localization.alg_equiv K[X]⁰ _ _ :=
funext $ λ ⟨x⟩, localization.induction_on x $ λ x,
by simp only [localization.mk_eq_mk'_apply, of_fraction_ring_mk', is_localization.alg_equiv_apply,
  ring_equiv.to_fun_eq_coe, is_localization.ring_equiv_of_ring_equiv_apply,
  is_localization.map_mk', ring_equiv.coe_to_ring_hom, ring_equiv.refl_apply, set_like.eta]

@[simp] lemma to_fraction_ring_ring_equiv_symm_eq :
  (to_fraction_ring_ring_equiv K).symm =
    (is_localization.alg_equiv K[X]⁰ _ _).to_ring_equiv :=
by { ext x,
     simp [to_fraction_ring_ring_equiv, of_fraction_ring_eq, alg_equiv.coe_ring_equiv'] }

end is_fraction_ring

section num_denom

/-! ### Numerator and denominator -/

open gcd_monoid polynomial

omit hring
variables [hfield : field K]
include hfield

/-- `ratfunc.num_denom` are numerator and denominator of a rational function over a field,
normalized such that the denominator is monic. -/
def num_denom (x : ratfunc K) : K[X] × K[X] :=
x.lift_on' (λ p q, if q = 0 then ⟨0, 1⟩ else let r := gcd p q in
  ⟨polynomial.C ((q / r).leading_coeff⁻¹) * (p / r),
   polynomial.C ((q / r).leading_coeff⁻¹) * (q / r)⟩)
  begin
    intros p q a hq ha,
    rw [if_neg hq, if_neg (mul_ne_zero ha hq)],
    have hpq : gcd p q ≠ 0 := mt (and.right ∘ (gcd_eq_zero_iff _ _).mp) hq,
    have ha' : a.leading_coeff ≠ 0 := polynomial.leading_coeff_ne_zero.mpr ha,
    have hainv : (a.leading_coeff)⁻¹ ≠ 0 := inv_ne_zero ha',
    simp only [prod.ext_iff, gcd_mul_left, normalize_apply, polynomial.coe_norm_unit, mul_assoc,
      comm_group_with_zero.coe_norm_unit _ ha'],
    have hdeg : (gcd p q).degree ≤ q.degree := degree_gcd_le_right _ hq,
    have hdeg' : (polynomial.C (a.leading_coeff⁻¹) * gcd p q).degree ≤ q.degree,
    { rw [polynomial.degree_mul, polynomial.degree_C hainv, zero_add],
      exact hdeg },
    have hdivp : (polynomial.C a.leading_coeff⁻¹) * gcd p q ∣ p :=
      (C_mul_dvd hainv).mpr (gcd_dvd_left p q),
    have hdivq : (polynomial.C a.leading_coeff⁻¹) * gcd p q ∣ q :=
      (C_mul_dvd hainv).mpr (gcd_dvd_right p q),
    rw [euclidean_domain.mul_div_mul_cancel ha hdivp, euclidean_domain.mul_div_mul_cancel ha hdivq,
        leading_coeff_div hdeg, leading_coeff_div hdeg', polynomial.leading_coeff_mul,
        polynomial.leading_coeff_C, div_C_mul, div_C_mul,
        ← mul_assoc, ← polynomial.C_mul, ← mul_assoc, ← polynomial.C_mul],
    split; congr; rw [inv_div, mul_comm, mul_div_assoc, ← mul_assoc, inv_inv,
      _root_.mul_inv_cancel ha', one_mul, inv_div],
  end

@[simp] lemma num_denom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
  num_denom (algebra_map _ _ p / algebra_map _ _ q) =
    (polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (p / gcd p q),
     polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (q / gcd p q)) :=
begin
  rw [num_denom, lift_on'_div, if_neg hq],
  intros p,
  rw [if_pos rfl, if_neg (@one_ne_zero K[X] _ _)],
  simp,
end

/-- `ratfunc.num` is the numerator of a rational function,
normalized such that the denominator is monic. -/
def num (x : ratfunc K) : K[X] := x.num_denom.1

private lemma num_div' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
  num (algebra_map _ _ p / algebra_map _ _ q) =
    polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (p / gcd p q) :=
by rw [num, num_denom_div _ hq]

@[simp] lemma num_zero : num (0 : ratfunc K) = 0 :=
by { convert num_div' (0 : K[X]) one_ne_zero; simp }

@[simp] lemma num_div (p q : K[X]) :
  num (algebra_map _ _ p / algebra_map _ _ q) =
    polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (p / gcd p q) :=
begin
  by_cases hq : q = 0,
  { simp [hq] },
  { exact num_div' p hq, },
end

@[simp] lemma num_one : num (1 : ratfunc K) = 1 :=
by { convert num_div (1 : K[X]) 1; simp }

@[simp] lemma num_algebra_map (p : K[X]) :
  num (algebra_map _ _ p) = p :=
by { convert num_div p 1; simp }

lemma num_div_dvd (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
  num (algebra_map _ _ p / algebra_map _ _ q) ∣ p :=
begin
  rw [num_div _ q, C_mul_dvd],
  { exact euclidean_domain.div_dvd_of_dvd (gcd_dvd_left p q) },
  { simpa only [ne.def, inv_eq_zero, polynomial.leading_coeff_eq_zero]
      using right_div_gcd_ne_zero hq },
end

/-- A version of `num_div_dvd` with the LHS in simp normal form -/
@[simp] lemma num_div_dvd' (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
  C ((q / gcd p q).leading_coeff)⁻¹ * (p / gcd p q) ∣ p :=
by simpa using num_div_dvd p hq

/-- `ratfunc.denom` is the denominator of a rational function,
normalized such that it is monic. -/
def denom (x : ratfunc K) : K[X] := x.num_denom.2

@[simp] lemma denom_div (p : K[X]) {q : K[X]} (hq : q ≠ 0) :
  denom (algebra_map _ _ p / algebra_map _ _ q) =
    polynomial.C ((q / gcd p q).leading_coeff⁻¹) * (q / gcd p q) :=
by rw [denom, num_denom_div _ hq]

lemma monic_denom (x : ratfunc K) : (denom x).monic :=
x.induction_on (λ p q hq, begin
  rw [denom_div p hq, mul_comm],
  exact polynomial.monic_mul_leading_coeff_inv (right_div_gcd_ne_zero hq)
end)

lemma denom_ne_zero (x : ratfunc K) : denom x ≠ 0 :=
(monic_denom x).ne_zero

@[simp] lemma denom_zero : denom (0 : ratfunc K) = 1 :=
by { convert denom_div (0 : K[X]) one_ne_zero; simp }

@[simp] lemma denom_one : denom (1 : ratfunc K) = 1 :=
by { convert denom_div (1 : K[X]) one_ne_zero; simp }

@[simp] lemma denom_algebra_map (p : K[X]) :
  denom (algebra_map _ (ratfunc K) p) = 1 :=
by { convert denom_div p one_ne_zero; simp }

@[simp] lemma denom_div_dvd (p q : K[X]) :
  denom (algebra_map _ _ p / algebra_map _ _ q) ∣ q :=
begin
  by_cases hq : q = 0,
  { simp [hq], },
  rw [denom_div _ hq, C_mul_dvd],
  { exact euclidean_domain.div_dvd_of_dvd (gcd_dvd_right p q) },
  { simpa only [ne.def, inv_eq_zero, polynomial.leading_coeff_eq_zero]
      using right_div_gcd_ne_zero hq },
end

@[simp] lemma num_div_denom (x : ratfunc K) :
  algebra_map _ _ (num x) / algebra_map _ _ (denom x) = x :=
x.induction_on (λ p q hq, begin
  have q_div_ne_zero := right_div_gcd_ne_zero hq,
  rw [num_div p q, denom_div p hq, ring_hom.map_mul, ring_hom.map_mul,
    mul_div_mul_left, div_eq_div_iff, ← ring_hom.map_mul, ← ring_hom.map_mul, mul_comm _ q,
    ← euclidean_domain.mul_div_assoc, ← euclidean_domain.mul_div_assoc, mul_comm],
  { apply gcd_dvd_right },
  { apply gcd_dvd_left },
  { exact algebra_map_ne_zero q_div_ne_zero },
  { exact algebra_map_ne_zero hq },
  { refine algebra_map_ne_zero (mt polynomial.C_eq_zero.mp _),
    exact inv_ne_zero (polynomial.leading_coeff_ne_zero.mpr q_div_ne_zero) },
end)

@[simp] lemma num_eq_zero_iff {x : ratfunc K} : num x = 0 ↔ x = 0 :=
⟨λ h, by rw [← num_div_denom x, h, ring_hom.map_zero, zero_div],
 λ h, h.symm ▸ num_zero⟩

lemma num_ne_zero {x : ratfunc K} (hx : x ≠ 0) : num x ≠ 0 :=
mt num_eq_zero_iff.mp hx

lemma num_mul_eq_mul_denom_iff {x : ratfunc K} {p q : K[X]}
  (hq : q ≠ 0) :
  x.num * q = p * x.denom ↔ x = algebra_map _ _ p / algebra_map _ _ q :=
begin
  rw [← (algebra_map_injective K).eq_iff, eq_div_iff (algebra_map_ne_zero hq)],
  conv_rhs { rw ← num_div_denom x },
  rw [ring_hom.map_mul, ring_hom.map_mul, div_eq_mul_inv, mul_assoc, mul_comm (has_inv.inv _),
      ← mul_assoc, ← div_eq_mul_inv, div_eq_iff],
  exact algebra_map_ne_zero (denom_ne_zero x)
end

lemma num_denom_add (x y : ratfunc K) :
  (x + y).num * (x.denom * y.denom) = (x.num * y.denom + x.denom * y.num) * (x + y).denom :=
(num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr $
begin
  conv_lhs { rw [← num_div_denom x, ← num_div_denom y] },
  rw [div_add_div, ring_hom.map_mul, ring_hom.map_add, ring_hom.map_mul, ring_hom.map_mul],
  { exact algebra_map_ne_zero (denom_ne_zero x) },
  { exact algebra_map_ne_zero (denom_ne_zero y) }
end

lemma num_denom_neg (x : ratfunc K) :
  (-x).num * x.denom = - x.num * (-x).denom :=
by rw [num_mul_eq_mul_denom_iff (denom_ne_zero x), _root_.map_neg, neg_div, num_div_denom]

lemma num_denom_mul (x y : ratfunc K) :
  (x * y).num * (x.denom * y.denom) = x.num * y.num * (x * y).denom :=
(num_mul_eq_mul_denom_iff (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y))).mpr $
  by conv_lhs { rw [← num_div_denom x, ← num_div_denom y, div_mul_div_comm,
                    ← ring_hom.map_mul, ← ring_hom.map_mul] }

lemma num_dvd {x : ratfunc K} {p : K[X]} (hp : p ≠ 0) :
  num x ∣ p ↔ ∃ (q : K[X]) (hq : q ≠ 0), x = algebra_map _ _ p / algebra_map _ _ q :=
begin
  split,
  { rintro ⟨q, rfl⟩,
    obtain ⟨hx, hq⟩ := mul_ne_zero_iff.mp hp,
    use denom x * q,
    rw [ring_hom.map_mul, ring_hom.map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom],
    { exact ⟨mul_ne_zero (denom_ne_zero x) hq, rfl⟩ },
    { exact algebra_map_ne_zero hq } },
  { rintro ⟨q, hq, rfl⟩,
    exact num_div_dvd p hq },
end

lemma denom_dvd {x : ratfunc K} {q : K[X]} (hq : q ≠ 0) :
  denom x ∣ q ↔ ∃ (p : K[X]), x = algebra_map _ _ p / algebra_map _ _ q :=
begin
  split,
  { rintro ⟨p, rfl⟩,
    obtain ⟨hx, hp⟩ := mul_ne_zero_iff.mp hq,
    use num x * p,
    rw [ring_hom.map_mul, ring_hom.map_mul, ← div_mul_div_comm, div_self, mul_one, num_div_denom],
    { exact algebra_map_ne_zero hp } },
  { rintro ⟨p, rfl⟩,
    exact denom_div_dvd p q },
end

lemma num_mul_dvd (x y : ratfunc K) : num (x * y) ∣ num x * num y :=
begin
  by_cases hx : x = 0,
  { simp [hx] },
  by_cases hy : y = 0,
  { simp [hy] },
  rw num_dvd (mul_ne_zero (num_ne_zero hx) (num_ne_zero hy)),
  refine ⟨x.denom * y.denom, mul_ne_zero (denom_ne_zero x) (denom_ne_zero y), _⟩,
  rw [ring_hom.map_mul, ring_hom.map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
end

lemma denom_mul_dvd (x y : ratfunc K) : denom (x * y) ∣ denom x * denom y :=
begin
  rw denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y)),
  refine ⟨x.num * y.num, _⟩,
  rw [ring_hom.map_mul, ring_hom.map_mul, ← div_mul_div_comm, num_div_denom, num_div_denom]
end

lemma denom_add_dvd (x y : ratfunc K) : denom (x + y) ∣ denom x * denom y :=
begin
  rw denom_dvd (mul_ne_zero (denom_ne_zero x) (denom_ne_zero y)),
  refine ⟨x.num * y.denom + x.denom * y.num, _⟩,
  rw [ring_hom.map_mul, ring_hom.map_add, ring_hom.map_mul, ring_hom.map_mul, ← div_add_div,
      num_div_denom, num_div_denom],
  { exact algebra_map_ne_zero (denom_ne_zero x) },
  { exact algebra_map_ne_zero (denom_ne_zero y) },
end

lemma map_denom_ne_zero {L F : Type*} [has_zero L] [zero_hom_class F K[X] L]
  (φ : F) (hφ : function.injective φ) (f : ratfunc K) : φ f.denom ≠ 0 :=
λ H, (denom_ne_zero f) ((map_eq_zero_iff φ hφ).mp H)

lemma map_apply {R F : Type*} [comm_ring R] [is_domain R]
  [monoid_hom_class F K[X] R[X]]
  (φ : F) (hφ : K[X]⁰ ≤ R[X]⁰.comap φ) (f : ratfunc K) :
  map φ hφ f = algebra_map _ _ (φ f.num) / algebra_map _ _ (φ f.denom) :=
begin
  rw [←num_div_denom f, map_apply_div_ne_zero, num_div_denom f],
  exact denom_ne_zero _
end

lemma lift_monoid_with_zero_hom_apply {L : Type*} [comm_group_with_zero L]
  (φ : K[X] →*₀ L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : ratfunc K) :
  lift_monoid_with_zero_hom φ hφ f = φ f.num / φ f.denom :=
by rw [←num_div_denom f, lift_monoid_with_zero_hom_apply_div, num_div_denom]

lemma lift_ring_hom_apply {L : Type*} [field L]
  (φ : K[X] →+* L) (hφ : K[X]⁰ ≤ L⁰.comap φ)  (f : ratfunc K) :
  lift_ring_hom φ hφ f = φ f.num / φ f.denom :=
lift_monoid_with_zero_hom_apply _ _ _

lemma lift_alg_hom_apply {L S : Type*} [field L] [comm_semiring S] [algebra S K[X]]
  [algebra S L] (φ : K[X] →ₐ[S] L) (hφ : K[X]⁰ ≤ L⁰.comap φ) (f : ratfunc K) :
  lift_alg_hom φ hφ f = φ f.num / φ f.denom :=
lift_monoid_with_zero_hom_apply _ _ _

lemma num_mul_denom_add_denom_mul_num_ne_zero {x y : ratfunc K} (hxy : x + y ≠ 0) :
  x.num * y.denom + x.denom * y.num ≠ 0 :=
begin
  intro h_zero,
  have h := num_denom_add x y,
  rw [h_zero, zero_mul] at h,
  exact (mul_ne_zero (num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)) h
end

end num_denom

section eval

/-! ### Polynomial structure: `C`, `X`, `eval` -/

include hdomain

/-- `ratfunc.C a` is the constant rational function `a`. -/
def C : K →+* ratfunc K :=
algebra_map _ _

@[simp] lemma algebra_map_eq_C : algebra_map K (ratfunc K) = C := rfl
@[simp] lemma algebra_map_C (a : K) :
  algebra_map K[X] (ratfunc K) (polynomial.C a) = C a := rfl
@[simp] lemma algebra_map_comp_C :
  (algebra_map K[X] (ratfunc K)).comp polynomial.C = C := rfl

lemma smul_eq_C_mul (r : K) (x : ratfunc K) :
  r • x = C r * x :=
by rw [algebra.smul_def, algebra_map_eq_C]

/-- `ratfunc.X` is the polynomial variable (aka indeterminate). -/
def X : ratfunc K := algebra_map K[X] (ratfunc K) polynomial.X

@[simp] lemma algebra_map_X :
  algebra_map K[X] (ratfunc K) polynomial.X = X := rfl

omit hring hdomain
variables [hfield : field K]
include hfield

@[simp] lemma num_C (c : K) : num (C c) = polynomial.C c :=
num_algebra_map _
@[simp] lemma denom_C (c : K) : denom (C c) = 1 :=
denom_algebra_map _

@[simp] lemma num_X : num (X : ratfunc K) = polynomial.X :=
num_algebra_map _
@[simp] lemma denom_X : denom (X : ratfunc K) = 1 :=
denom_algebra_map _

lemma X_ne_zero : (ratfunc.X : ratfunc K) ≠ 0 :=
ratfunc.algebra_map_ne_zero polynomial.X_ne_zero

variables {L : Type*} [field L]

/-- Evaluate a rational function `p` given a ring hom `f` from the scalar field
to the target and a value `x` for the variable in the target.

Fractions are reduced by clearing common denominators before evaluating:
`eval id 1 ((X^2 - 1) / (X - 1)) = eval id 1 (X + 1) = 2`, not `0 / 0 = 0`.
-/
def eval (f : K →+* L) (a : L) (p : ratfunc K) : L :=
(num p).eval₂ f a / (denom p).eval₂ f a

variables {f : K →+* L} {a : L}

lemma eval_eq_zero_of_eval₂_denom_eq_zero
  {x : ratfunc K} (h : polynomial.eval₂ f a (denom x) = 0) :
  eval f a x = 0 :=
by rw [eval, h, div_zero]
lemma eval₂_denom_ne_zero {x : ratfunc K} (h : eval f a x ≠ 0) :
  polynomial.eval₂ f a (denom x) ≠ 0 :=
mt eval_eq_zero_of_eval₂_denom_eq_zero h

variables (f a)

@[simp] lemma eval_C {c : K} : eval f a (C c) = f c := by simp [eval]
@[simp] lemma eval_X : eval f a X = a := by simp [eval]
@[simp] lemma eval_zero : eval f a 0 = 0 := by simp [eval]
@[simp] lemma eval_one : eval f a 1 = 1 := by simp [eval]
@[simp] lemma eval_algebra_map {S : Type*} [comm_semiring S] [algebra S K[X]] (p : S) :
  eval f a (algebra_map _ _ p) = (algebra_map _ K[X] p).eval₂ f a :=
by simp [eval, is_scalar_tower.algebra_map_apply S K[X] (ratfunc K)]

/-- `eval` is an additive homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 1 (X / (X-1)) + eval _ 1 (-1 / (X-1)) = 0`
`... ≠ 1 = eval _ 1 ((X-1) / (X-1))`.

See also `ratfunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
lemma eval_add {x y : ratfunc K}
  (hx : polynomial.eval₂ f a (denom x) ≠ 0) (hy : polynomial.eval₂ f a (denom y) ≠ 0) :
  eval f a (x + y) = eval f a x + eval f a y :=
begin
  unfold eval,
  by_cases hxy : polynomial.eval₂ f a (denom (x + y)) = 0,
  { have := polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_add_dvd x y) hxy,
    rw polynomial.eval₂_mul at this,
    cases mul_eq_zero.mp this; contradiction },
  rw [div_add_div _ _ hx hy, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv, div_eq_iff hxy],
  simp only [← polynomial.eval₂_mul, ← polynomial.eval₂_add],
  congr' 1,
  apply num_denom_add
end

/-- `eval` is a multiplicative homomorphism except when a denominator evaluates to `0`.

Counterexample: `eval _ 0 X * eval _ 0 (1/X) = 0 ≠ 1 = eval _ 0 1 = eval _ 0 (X * 1/X)`.

See also `ratfunc.eval₂_denom_ne_zero` to make the hypotheses simpler but less general.
-/
lemma eval_mul {x y : ratfunc K}
  (hx : polynomial.eval₂ f a (denom x) ≠ 0) (hy : polynomial.eval₂ f a (denom y) ≠ 0) :
  eval f a (x * y) = eval f a x * eval f a y :=
begin
  unfold eval,
  by_cases hxy : polynomial.eval₂ f a (denom (x * y)) = 0,
  { have := polynomial.eval₂_eq_zero_of_dvd_of_eval₂_eq_zero f a (denom_mul_dvd x y) hxy,
    rw polynomial.eval₂_mul at this,
    cases mul_eq_zero.mp this; contradiction },
  rw [div_mul_div_comm, eq_div_iff (mul_ne_zero hx hy), div_eq_mul_inv, mul_right_comm,
      ← div_eq_mul_inv, div_eq_iff hxy],
  repeat { rw ← polynomial.eval₂_mul },
  congr' 1,
  apply num_denom_mul,
end

end eval

section int_degree

open polynomial

omit hring

variables [field K]

/-- `int_degree x` is the degree of the rational function `x`, defined as the difference between
the `nat_degree` of its numerator and the `nat_degree` of its denominator. In particular,
`int_degree 0 = 0`. -/
def int_degree (x : ratfunc K) : ℤ := nat_degree x.num - nat_degree x.denom

@[simp] lemma int_degree_zero : int_degree (0 : ratfunc K) = 0 :=
by rw [int_degree, num_zero, nat_degree_zero, denom_zero, nat_degree_one, sub_self]

@[simp] lemma int_degree_one : int_degree (1 : ratfunc K) = 0 :=
by rw [int_degree, num_one, denom_one, sub_self]

@[simp] lemma int_degree_C (k : K): int_degree (ratfunc.C k) = 0 :=
by rw [int_degree, num_C, nat_degree_C, denom_C, nat_degree_one, sub_self]

@[simp] lemma int_degree_X : int_degree (X : ratfunc K) = 1 :=
by rw [int_degree, ratfunc.num_X, polynomial.nat_degree_X, ratfunc.denom_X,
  polynomial.nat_degree_one, int.coe_nat_one, int.coe_nat_zero, sub_zero]

@[simp] lemma int_degree_polynomial {p : polynomial K} :
  int_degree (algebra_map (polynomial K) (ratfunc K) p) = nat_degree p :=
by rw [int_degree, ratfunc.num_algebra_map, ratfunc.denom_algebra_map, polynomial.nat_degree_one,
  int.coe_nat_zero, sub_zero]

lemma int_degree_mul {x y : ratfunc K} (hx : x ≠ 0) (hy : y ≠ 0) :
  int_degree (x * y) = int_degree x + int_degree y :=
begin
  simp only [int_degree, add_sub, sub_add, sub_sub_eq_add_sub, sub_sub, sub_eq_sub_iff_add_eq_add],
  norm_cast,
  rw [← polynomial.nat_degree_mul x.denom_ne_zero y.denom_ne_zero,
        ← polynomial.nat_degree_mul (ratfunc.num_ne_zero (mul_ne_zero hx hy))
          (mul_ne_zero x.denom_ne_zero y.denom_ne_zero),
        ← polynomial.nat_degree_mul (ratfunc.num_ne_zero hx) (ratfunc.num_ne_zero hy),
        ← polynomial.nat_degree_mul (mul_ne_zero (ratfunc.num_ne_zero hx) (ratfunc.num_ne_zero hy))
          (x * y).denom_ne_zero, ratfunc.num_denom_mul]
end

@[simp] lemma int_degree_neg (x : ratfunc K) : int_degree (-x) = int_degree x :=
begin
  by_cases hx : x = 0,
  { rw [hx, neg_zero] },
  { rw [int_degree, int_degree, ← nat_degree_neg x.num],
    exact nat_degree_sub_eq_of_prod_eq (num_ne_zero (neg_ne_zero.mpr hx)) (denom_ne_zero (- x))
      (neg_ne_zero.mpr (num_ne_zero hx)) (denom_ne_zero x) (num_denom_neg x) }
end

lemma int_degree_add {x y : ratfunc K}
  (hxy : x + y ≠ 0) : (x + y).int_degree  =
    (x.num * y.denom + x.denom * y.num).nat_degree - (x.denom * y.denom).nat_degree :=
nat_degree_sub_eq_of_prod_eq (num_ne_zero hxy) ((x + y).denom_ne_zero)
    (num_mul_denom_add_denom_mul_num_ne_zero hxy) (mul_ne_zero x.denom_ne_zero y.denom_ne_zero)
    (num_denom_add x y)

lemma nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree {x : ratfunc K}
  (hx : x ≠ 0) {s : polynomial K} (hs : s ≠ 0) :
  ((x.num * s).nat_degree : ℤ) - (s * x.denom).nat_degree = x.int_degree :=
begin
  apply nat_degree_sub_eq_of_prod_eq (mul_ne_zero (num_ne_zero hx) hs)
    (mul_ne_zero hs x.denom_ne_zero) (num_ne_zero hx) x.denom_ne_zero,
  rw mul_assoc
end

lemma int_degree_add_le {x y : ratfunc K} (hy : y ≠ 0) (hxy : x + y ≠ 0) :
  int_degree (x + y) ≤ max (int_degree x) (int_degree y) :=
begin
  by_cases hx : x = 0,
  { simp [hx] at *, },
  rw [int_degree_add hxy,
    ← nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree hx y.denom_ne_zero,
    mul_comm y.denom,
    ← nat_degree_num_mul_right_sub_nat_degree_denom_mul_left_eq_int_degree hy x.denom_ne_zero,
    le_max_iff,sub_le_sub_iff_right, int.coe_nat_le, sub_le_sub_iff_right, int.coe_nat_le,
    ← le_max_iff, mul_comm y.num],
    exact nat_degree_add_le _ _,
end

end int_degree

section laurent_series

open power_series laurent_series hahn_series

omit hring
variables {F : Type u} [field F] (p q : F[X]) (f g : ratfunc F)

/-- The coercion `ratfunc F → laurent_series F` as bundled alg hom. -/
def coe_alg_hom (F : Type u) [field F] : ratfunc F →ₐ[polynomial F] laurent_series F :=
lift_alg_hom (algebra.of_id _ _) $ non_zero_divisors_le_comap_non_zero_divisors_of_injective _ $
  polynomial.algebra_map_hahn_series_injective _

instance coe_to_laurent_series : has_coe (ratfunc F) (laurent_series F) :=
⟨coe_alg_hom F⟩

lemma coe_def : (f : laurent_series F) = coe_alg_hom F f := rfl

lemma coe_num_denom : (f : laurent_series F) = f.num / f.denom :=
lift_alg_hom_apply _ _ f

lemma coe_injective : function.injective (coe : ratfunc F → laurent_series F) :=
lift_alg_hom_injective _ (polynomial.algebra_map_hahn_series_injective _)

@[simp, norm_cast] lemma coe_apply : coe_alg_hom F f = f := rfl

@[simp, norm_cast] lemma coe_zero : ((0 : ratfunc F) : laurent_series F) = 0 :=
(coe_alg_hom F).map_zero

@[simp, norm_cast] lemma coe_one : ((1 : ratfunc F) : laurent_series F) = 1 :=
(coe_alg_hom F).map_one

@[simp, norm_cast] lemma coe_add : ((f + g : ratfunc F) : laurent_series F) = f + g :=
(coe_alg_hom F).map_add _ _

@[simp, norm_cast] lemma coe_mul : ((f * g : ratfunc F) : laurent_series F) = f * g :=
(coe_alg_hom F).map_mul _ _

@[simp, norm_cast] lemma coe_div : ((f / g : ratfunc F) : laurent_series F) =
  (f : laurent_series F) / (g : laurent_series F) :=
(coe_alg_hom F).map_div _ _

@[simp, norm_cast] lemma coe_C (r : F) : ((C r : ratfunc F) : laurent_series F) = hahn_series.C r :=
by rw [coe_num_denom, num_C, denom_C, coe_coe, polynomial.coe_C, coe_C, coe_coe, polynomial.coe_one,
       power_series.coe_one, div_one]

-- TODO: generalize over other modules
@[simp, norm_cast] lemma coe_smul (r : F) : ((r • f : ratfunc F) : laurent_series F) = r • f :=
by rw [smul_eq_C_mul, ←C_mul_eq_smul, coe_mul, coe_C]

@[simp, norm_cast] lemma coe_X : ((X : ratfunc F) : laurent_series F) = single 1 1 :=
by rw [coe_num_denom, num_X, denom_X, coe_coe, polynomial.coe_X, coe_X, coe_coe, polynomial.coe_one,
       power_series.coe_one, div_one]

instance : algebra (ratfunc F) (laurent_series F) :=
ring_hom.to_algebra (coe_alg_hom F).to_ring_hom

lemma algebra_map_apply_div :
  algebra_map (ratfunc F) (laurent_series F) (algebra_map _ _ p / algebra_map _ _ q) =
    algebra_map F[X] (laurent_series F) p / algebra_map _ _ q :=
begin
  convert coe_div _ _;
  rw [←mk_one, coe_def, coe_alg_hom, mk_eq_div, lift_alg_hom_apply_div, map_one, div_one,
      algebra.of_id_apply]
end

instance : is_scalar_tower F[X] (ratfunc F) (laurent_series F) :=
⟨λ x y z, by { ext, simp }⟩

end laurent_series

end ratfunc
