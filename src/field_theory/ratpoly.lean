/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/

import ring_theory.localization

/-!
# The field of rational polynomials

This file defines the field `ratpoly K` of rational polynomials over a field `K`,
and shows it is the field of fractions of `polynomial K`.

## Implementation notes

We need a couple of maps to set up the `field` and `is_fraction_ring` structure,
namely `ratpoly.of_fraction_ring`, `ratpoly.to_fraction_ring`, `ratpoly.mk` and `ratpoly.aux_equiv`.
All these maps get `simp`ed to bundled morphisms like `algebra_map (polynomial K) (ratpoly K)`
and `is_localization.alg_equiv`.
-/

noncomputable theory
open_locale classical
open_locale non_zero_divisors

universes u v

variables (K : Type u) [field K]

/-- `ratpoly K` is `K(x)`, the field of rational polynomials over `K`.

The inclusion of polynomials into `ratpoly` is `algebra_map (polynomial K) (ratpoly K)`,
the maps between `ratpoly K` and another field of fractions of `polynomial K`,
especially `fraction_ring (polynomial K)`, are given by `is_localization.algebra_equiv`.
-/
structure ratpoly : Type u := of_fraction_ring ::
(to_fraction_ring : fraction_ring (polynomial K))

namespace ratpoly

variables {K}

lemma of_fraction_ring_injective : function.injective (of_fraction_ring : _ → ratpoly K) :=
λ x y, of_fraction_ring.inj

lemma to_fraction_ring_injective :
  function.injective (to_fraction_ring : _ → fraction_ring (polynomial K))
| ⟨x⟩ ⟨y⟩ rfl := rfl

/-- `ratpoly.mk (p q : polynomial K)` is `p / q` as a rational polynomial.

If `q = 0`, then `mk` returns 0.

This is an auxiliary definition used to define an `algebra` structure on `ratpoly`;
the `simp` normal form of `mk p q` is `algebra_map _ _ p / algebra_map _ _ q`.
-/
@[irreducible] protected def mk (p q : polynomial K) : ratpoly K :=
of_fraction_ring (algebra_map _ _ p / algebra_map _ _ q)

lemma mk_eq_div' (p q : polynomial K) :
  ratpoly.mk p q = of_fraction_ring (algebra_map _ _ p / algebra_map _ _ q) :=
by unfold ratpoly.mk

lemma mk_zero (p : polynomial K) : ratpoly.mk p 0 = of_fraction_ring 0 :=
by rw [mk_eq_div', ring_hom.map_zero, div_zero]

lemma mk_coe_def (p : polynomial K) (q : (polynomial K)⁰) :
  ratpoly.mk p q = of_fraction_ring (is_localization.mk' _ p q) :=
by simp only [mk_eq_div', ← localization.mk_eq_mk', fraction_ring.mk_eq_div]

lemma mk_def_of_mem (p : polynomial K) {q} (hq : q ∈ (polynomial K)⁰) :
  ratpoly.mk p q = of_fraction_ring (is_localization.mk' _ p ⟨q, hq⟩) :=
by simp only [← mk_coe_def, set_like.coe_mk]

lemma mk_def_of_ne (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  ratpoly.mk p q = of_fraction_ring (is_localization.mk' _ p
    ⟨q, mem_non_zero_divisors_iff_ne_zero.mpr hq⟩) :=
mk_def_of_mem p _

lemma mk_eq_localization_mk (p : polynomial K) {q : polynomial K} (hq : q ≠ 0) :
  ratpoly.mk p q = of_fraction_ring (localization.mk p
    ⟨q, mem_non_zero_divisors_iff_ne_zero.mpr hq⟩) :=
by rw [mk_def_of_ne, localization.mk_eq_mk']

lemma mk_one' (p : polynomial K) : ratpoly.mk p 1 = of_fraction_ring (algebra_map _ _ p) :=
by rw [← is_localization.mk'_one (fraction_ring (polynomial K)) p, ← mk_coe_def, submonoid.coe_one]

lemma mk_eq_mk {p q p' q' : polynomial K} (hq : q ≠ 0) (hq' : q' ≠ 0) :
  ratpoly.mk p q = ratpoly.mk p' q' ↔ p * q' = p' * q :=
by rw [mk_def_of_ne _ hq, mk_def_of_ne _ hq', of_fraction_ring_injective.eq_iff,
       is_localization.mk'_eq_iff_eq, set_like.coe_mk, set_like.coe_mk,
       (is_fraction_ring.injective (polynomial K) (fraction_ring (polynomial K))).eq_iff]

/-- Non-dependent recursion principle for `ratpoly K`: if `f p q : P` for all `p q`,
such that `p * q' = p' * q` implies `f p q = f p' q'`, then we can find a value of `P`
for all elements of `ratpoly K` by setting `lift_on (p / q) f _ = f p q`.

The value of `f p 0` for any `p` is never used and in principle this may be anything,
although many usages of `lift_on` assume `f p 0 = f 0 1`.
-/
@[irreducible] protected def lift_on {P : Sort v} (x : ratpoly K)
  (f : ∀ (p q : polynomial K), P)
  (H : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), p * q' = p' * q → f p q = f p' q') :
  P :=
localization.lift_on (to_fraction_ring x) (λ p q, f p q) (λ p p' q q' h, H
  (mem_non_zero_divisors_iff_ne_zero.mp q.2)
  (mem_non_zero_divisors_iff_ne_zero.mp q'.2)
  (let ⟨⟨c, hc⟩, mul_eq⟩ := (localization.r_iff_exists).mp h in
    (mul_eq_mul_right_iff.mp mul_eq).resolve_right (mem_non_zero_divisors_iff_ne_zero.mp hc)))

lemma lift_on_mk {P : Sort v} (p q : polynomial K)
  (f : ∀ (p q : polynomial K), P) (f0 : ∀ p, f p 0 = f 0 1)
  (H : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), p * q' = p' * q → f p q = f p' q') :
  (ratpoly.mk p q).lift_on f @H = f p q :=
begin
  unfold ratpoly.lift_on,
  by_cases hq : q = 0,
  { subst hq,
    simp only [mk_zero, f0, ← localization.mk_zero 1, localization.lift_on_mk, submonoid.coe_one] },
  { simp only [mk_eq_localization_mk _ hq, localization.lift_on_mk, set_like.coe_mk] }
end

/-- Induction principle for `ratpoly K`: if `f p q : P (ratpoly.mk p q)` for all `p q`,
then `P` holds on all elements of `ratpoly K`.

See also `induction_on`, which is a recursion principle defined in terms of `algebra_map`.
-/
@[irreducible] protected lemma induction_on' {P : ratpoly K → Prop} :
  Π (x : ratpoly K) (f : ∀ (p q : polynomial K) (hq : q ≠ 0), P (ratpoly.mk p q)), P x
| ⟨x⟩ f := localization.induction_on x
  (λ ⟨p, q⟩, by simpa only [mk_coe_def, localization.mk_eq_mk'] using f p q
    (mem_non_zero_divisors_iff_ne_zero.mp q.2))

/-- The zero rational polynomial. -/
@[irreducible] protected def zero : ratpoly K := ⟨0⟩
instance : has_zero (ratpoly K) := ⟨ratpoly.zero⟩
lemma of_fraction_ring_zero : (of_fraction_ring 0 : ratpoly K) = 0 :=
by unfold has_zero.zero ratpoly.zero

/-- Addition of rational polynomials. -/
@[irreducible] protected def add : ratpoly K → ratpoly K → ratpoly K
| ⟨p⟩ ⟨q⟩ := ⟨p + q⟩
instance : has_add (ratpoly K) := ⟨ratpoly.add⟩
lemma of_fraction_ring_add (p q : fraction_ring (polynomial K)) :
  of_fraction_ring (p + q) = of_fraction_ring p + of_fraction_ring q :=
by unfold has_add.add ratpoly.add

/-- Subtraction of rational polynomials. -/
@[irreducible] protected def sub : ratpoly K → ratpoly K → ratpoly K
| ⟨p⟩ ⟨q⟩ := ⟨p - q⟩
instance : has_sub (ratpoly K) := ⟨ratpoly.sub⟩
lemma of_fraction_ring_sub (p q : fraction_ring (polynomial K)) :
  of_fraction_ring (p - q) = of_fraction_ring p - of_fraction_ring q :=
by unfold has_sub.sub ratpoly.sub

/-- Additive inverse of a rational polynomial. -/
@[irreducible] protected def neg : ratpoly K → ratpoly K
| ⟨p⟩ := ⟨-p⟩
instance : has_neg (ratpoly K) := ⟨ratpoly.neg⟩
lemma of_fraction_ring_neg (p : fraction_ring (polynomial K)) :
  of_fraction_ring (-p) = - of_fraction_ring p :=
by unfold has_neg.neg ratpoly.neg

/-- The multiplicative unit of rational polynomials. -/
@[irreducible] protected def one : ratpoly K := ⟨1⟩
instance : has_one (ratpoly K) := ⟨ratpoly.one⟩
lemma of_fraction_ring_one : (of_fraction_ring 1 : ratpoly K) = 1 :=
by unfold has_one.one ratpoly.one

/-- Multiplication of rational polynomials. -/
@[irreducible] protected def mul : ratpoly K → ratpoly K → ratpoly K
| ⟨p⟩ ⟨q⟩ := ⟨p * q⟩
instance : has_mul (ratpoly K) := ⟨ratpoly.mul⟩
lemma of_fraction_ring_mul (p q : fraction_ring (polynomial K)) :
  of_fraction_ring (p * q) = of_fraction_ring p * of_fraction_ring q :=
by unfold has_mul.mul ratpoly.mul

/-- Division of rational polynomials. -/
@[irreducible] protected def div : ratpoly K → ratpoly K → ratpoly K
| ⟨p⟩ ⟨q⟩ := ⟨p / q⟩
instance : has_div (ratpoly K) := ⟨ratpoly.div⟩
lemma of_fraction_ring_div (p q : fraction_ring (polynomial K)) :
  of_fraction_ring (p / q) = of_fraction_ring p / of_fraction_ring q :=
by unfold has_div.div ratpoly.div

/-- Multiplicative inverse of a rational polynomial. -/
@[irreducible] protected def inv : ratpoly K → ratpoly K
| ⟨p⟩ := ⟨p⁻¹⟩
instance : has_inv (ratpoly K) := ⟨ratpoly.inv⟩
lemma of_fraction_ring_inv (p : fraction_ring (polynomial K)) :
  of_fraction_ring (p⁻¹) = (of_fraction_ring p)⁻¹ :=
by unfold has_inv.inv ratpoly.inv

-- Auxiliary lemma for the `field` instance
lemma mul_inv_cancel : ∀ {p : ratpoly K} (hp : p ≠ 0), p * p⁻¹ = 1
| ⟨p⟩ h := have p ≠ 0 := λ hp, h $ by rw [hp, of_fraction_ring_zero],
by simpa only [← of_fraction_ring_inv, ← of_fraction_ring_mul, ← of_fraction_ring_one]
  using _root_.mul_inv_cancel this

section has_scalar

variables {R : Type*} [monoid R] [distrib_mul_action R (polynomial K)]
variables [is_scalar_tower R (polynomial K) (polynomial K)]

-- Can't define this in terms of `localization.has_scalar`, because that one
-- is not general enough.
instance : has_scalar R (ratpoly K) :=
⟨λ c p, p.lift_on (λ p q, ratpoly.mk (c • p) q) (λ p q p' q' hq hq' h, (mk_eq_mk hq hq').mpr $
  by rw [smul_mul_assoc, h, smul_mul_assoc])⟩

lemma mk_smul (c : R) (p q : polynomial K) :
  ratpoly.mk (c • p) q = c • ratpoly.mk p q :=
show ratpoly.mk (c • p) q = (ratpoly.mk p q).lift_on _ _,
from symm $ (lift_on_mk p q _ (λ p, show ratpoly.mk (c • p) 0 = ratpoly.mk (c • 0) 1,
  by rw [mk_zero, smul_zero, mk_eq_localization_mk (0 : polynomial K) one_ne_zero,
         localization.mk_zero]) _)

instance : is_scalar_tower R (polynomial K) (ratpoly K) :=
⟨λ c p q, q.induction_on' (λ q r _, by rw [← mk_smul, smul_assoc, mk_smul, mk_smul])⟩

end has_scalar

variables (K)

instance : inhabited (ratpoly K) :=
⟨0⟩
instance : nontrivial (ratpoly K) :=
⟨⟨0, 1, mt (congr_arg to_fraction_ring) $
  by simpa only [← of_fraction_ring_zero, ← of_fraction_ring_one] using zero_ne_one⟩⟩

/-- Solve equations for `ratpoly K` by working in `fraction_ring (polynomial K)`. -/
meta def frac_tac : tactic unit :=
`[repeat { rintro (⟨⟩ : ratpoly _) },
  simp only [← of_fraction_ring_zero, ← of_fraction_ring_add, ← of_fraction_ring_sub,
    ← of_fraction_ring_neg, ← of_fraction_ring_one, ← of_fraction_ring_mul, ← of_fraction_ring_div,
    ← of_fraction_ring_inv,
    add_assoc, zero_add, add_zero, mul_assoc, mul_zero, mul_one, mul_add, inv_zero,
    add_comm, add_left_comm, mul_comm, mul_left_comm, sub_eq_add_neg, div_eq_mul_inv,
    add_mul, zero_mul, one_mul, ← neg_mul_eq_neg_mul, ← neg_mul_eq_mul_neg, add_right_neg]]

/-- Solve equations for `ratpoly K` by applying `ratpoly.induction_on`. -/
meta def smul_tac : tactic unit :=
`[repeat { rintro (x : ratpoly _) <|> intro },
  refine x.induction_on' (λ p q hq, _),
  simp_rw [← mk_smul, mk_eq_localization_mk _ hq],
  simp only [add_comm, mul_comm, zero_smul, succ_nsmul, gsmul_eq_mul, mul_add, mul_one, mul_zero,
    neg_add, ← neg_mul_eq_mul_neg,
    int.of_nat_eq_coe, int.coe_nat_succ, int.cast_zero, int.cast_add, int.cast_one,
    int.cast_neg_succ_of_nat, int.cast_coe_nat,
    localization.mk_zero, localization.add_mk_self, localization.neg_mk,
    of_fraction_ring_zero, ← of_fraction_ring_add, ← of_fraction_ring_neg]]

instance : field (ratpoly K) :=
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
  inv := has_inv.inv,
  inv_zero := by frac_tac,
  div := (/),
  div_eq_mul_inv := by frac_tac,
  mul_inv_cancel := λ _, mul_inv_cancel,
  nsmul := (•),
  nsmul_zero' := by smul_tac,
  nsmul_succ' := by smul_tac,
  gsmul := (•),
  gsmul_zero' := by smul_tac,
  gsmul_succ' := by smul_tac,
  gsmul_neg' := by smul_tac,
  npow := npow_rec,
  gpow := gpow_rec,
  .. ratpoly.nontrivial K }

instance (R : Type*) [comm_semiring R] [algebra R (polynomial K)] :
  algebra R (ratpoly K) :=
{ to_fun := λ x, ratpoly.mk (algebra_map _ _ x) 1,
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

lemma mk_one (x : polynomial K) : ratpoly.mk x 1 = algebra_map _ _ x := rfl

lemma of_fraction_ring_algebra_map (x : polynomial K) :
  of_fraction_ring (algebra_map _ (fraction_ring (polynomial K)) x) = algebra_map _ _ x :=
by rw [← mk_one, mk_one']

@[simp] lemma mk_eq_div (p q : polynomial K) :
  ratpoly.mk p q = (algebra_map _ _ p / algebra_map _ _ q) :=
by simp only [mk_eq_div', of_fraction_ring_div, of_fraction_ring_algebra_map]

variables (K)

lemma of_fraction_ring_comp_algebra_map :
  of_fraction_ring ∘ algebra_map (polynomial K) (fraction_ring (polynomial K)) = algebra_map _ _ :=
funext of_fraction_ring_algebra_map

lemma algebra_map_injective : function.injective (algebra_map (polynomial K) (ratpoly K)) :=
begin
  rw ← of_fraction_ring_comp_algebra_map,
  exact of_fraction_ring_injective.comp (is_fraction_ring.injective _ _),
end

/-- `ratpoly K` is isomorphic to the field of fractions of `polynomial K`, as rings.

This is an auxiliary definition; `simp`-normal form is `is_localization.alg_equiv`.
-/
def aux_equiv : fraction_ring (polynomial K) ≃+* ratpoly K :=
{ to_fun := of_fraction_ring,
  inv_fun := to_fraction_ring,
  left_inv := λ x, rfl,
  right_inv := λ ⟨x⟩, rfl,
  map_add' := of_fraction_ring_add,
  map_mul' := of_fraction_ring_mul }

/-- `ratpoly K` is the field of fractions of the polynomials over `K`. -/
instance : is_fraction_ring (polynomial K) (ratpoly K) :=
{ map_units := λ y, by rw ← of_fraction_ring_algebra_map;
    exact (aux_equiv K).to_ring_hom.is_unit_map (is_localization.map_units _ y),
  eq_iff_exists := λ x y, by rw [← of_fraction_ring_algebra_map, ← of_fraction_ring_algebra_map];
    exact (aux_equiv K).injective.eq_iff.trans (is_localization.eq_iff_exists _ _),
  surj := by { rintro ⟨z⟩, convert is_localization.surj (polynomial K)⁰ z, ext ⟨x, y⟩,
    simp only [← of_fraction_ring_algebra_map, function.comp_app, ← of_fraction_ring_mul] } }

variables {K}

@[simp] lemma lift_on_div {P : Sort v} (p q : polynomial K)
  (f : ∀ (p q : polynomial K), P) (f0 : ∀ p, f p 0 = f 0 1)
  (H : ∀ {p q p' q'} (hq : q ≠ 0) (hq' : q' ≠ 0), p * q' = p' * q → f p q = f p' q') :
  (algebra_map _ (ratpoly K) p / algebra_map _ _ q).lift_on f @H = f p q :=
by rw [← mk_eq_div, lift_on_mk _ _ f f0 @H]

/-- Induction principle for `ratpoly K`: if `f p q : P (p / q)` for all `p q : polynomial K`,
then `P` holds on all elements of `ratpoly K`.

See also `induction_on'`, which is a recursion principle defined in terms of `ratpoly.mk`.
-/
protected lemma induction_on {P : ratpoly K → Prop} (x : ratpoly K)
  (f : ∀ (p q : polynomial K) (hq : q ≠ 0),
    P (algebra_map _ (ratpoly K) p / algebra_map _ _ q)) :
  P x :=
x.induction_on' (λ p q hq, by simpa using f p q hq)

lemma of_fraction_ring_mk' (x : polynomial K) (y : (polynomial K)⁰) :
  of_fraction_ring (is_localization.mk' _ x y) = is_localization.mk' (ratpoly K) x y :=
by rw [is_fraction_ring.mk'_eq_div, is_fraction_ring.mk'_eq_div, ← mk_eq_div', ← mk_eq_div]

@[simp] lemma of_fraction_ring_eq :
  (of_fraction_ring : fraction_ring (polynomial K) → ratpoly K) =
    is_localization.alg_equiv (polynomial K)⁰ _ _ :=
funext $ λ x, localization.induction_on x $ λ x,
by simp only [is_localization.alg_equiv_apply, is_localization.ring_equiv_of_ring_equiv_apply,
    ring_equiv.to_fun_eq_coe, localization.mk_eq_mk'_apply, is_localization.map_mk',
    of_fraction_ring_mk', ring_equiv.coe_to_ring_hom, ring_equiv.refl_apply, set_like.eta]

@[simp] lemma to_fraction_ring_eq :
  (to_fraction_ring : ratpoly K → fraction_ring (polynomial K)) =
    is_localization.alg_equiv (polynomial K)⁰ _ _ :=
funext $ λ ⟨x⟩, localization.induction_on x $ λ x,
by simp only [localization.mk_eq_mk'_apply, of_fraction_ring_mk', is_localization.alg_equiv_apply,
  ring_equiv.to_fun_eq_coe, is_localization.ring_equiv_of_ring_equiv_apply, is_localization.map_mk',
  ring_equiv.coe_to_ring_hom, ring_equiv.refl_apply, set_like.eta]

@[simp] lemma aux_equiv_eq :
  aux_equiv K = (is_localization.alg_equiv (polynomial K)⁰ _ _).to_ring_equiv :=
by { ext x,
     simp only [aux_equiv, ring_equiv.coe_mk, of_fraction_ring_eq, alg_equiv.coe_ring_equiv'] }

end ratpoly
