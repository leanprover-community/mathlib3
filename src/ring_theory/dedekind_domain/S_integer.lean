/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import ring_theory.dedekind_domain.adic_valuation

/-!
# `S`-integers and `S`-units of fraction fields of Dedekind domains

Let `K` be the field of fractions of a Dedekind domain `R`, and let `S` be a set of prime ideals in
the height one spectrum of `R`. An `S`-integer of `K` is defined to have `v`-adic valuation at most
one for all primes ideals `v` away from `S`, whereas an `S`-unit of `Kˣ` is defined to have `v`-adic
valuation exactly one for all prime ideals `v` away from `S`.

This file defines the subring of `S`-integers of `K` and the subgroup of `S`-units of `Kˣ`, which
can be specialised to the case of a number field or a function field separately.

## Main definitions

 * `set.integer`: `S`-integers.
 * `set.unit`: `S`-units.
 * TODO: notation for `S`-integers and `S`-units.

## Main statements

 * `set.unit_equiv_units_integer`: `S`-units are units of `S`-integers.
 * TODO: proof that `S`-units is the kernel of a map to a product.
 * TODO: proof that `∅`-integers is the usual ring of integers.
 * TODO: finite generation of `S`-units and Dirichlet's `S`-unit theorem.

## References

 * [D Marcus, *Number Fields*][marcus1977number]
 * [J W S Cassels, A Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

S integer, S-integer, S unit, S-unit
-/

open is_dedekind_domain

open_locale non_zero_divisors

namespace set

noncomputable theory

universes u v

variables {R : Type u} [comm_ring R] [is_domain R] [is_dedekind_domain R]
  (S : set $ height_one_spectrum R) (K : Type v) [field K] [algebra R K] [is_fraction_ring R K]

/-! ## `S`-integers -/

/-- The subring of `S`-integers of `K`. -/
@[simps] def integer : subring K :=
(⨅ v ∉ S, (v : height_one_spectrum R).valuation.valuation_subring.to_subring).copy
  {x : K | ∀ v ∉ S, (v : height_one_spectrum R).valuation x ≤ 1} $ set.ext $ λ _,
  by simpa only [set_like.mem_coe, subring.mem_infi]

lemma integer_eq :
  S.integer K = ⨅ v ∉ S, (v : height_one_spectrum R).valuation.valuation_subring.to_subring :=
subring.copy_eq _ _ _

lemma integer_valuation_le_one (x : S.integer K) {v : height_one_spectrum R} (hv : v ∉ S) :
  v.valuation (x : K) ≤ 1 :=
x.property v hv

/-- The subring of `S`-integers of `K` is an algebra over `R`. -/
instance : algebra R (S.integer K) :=
{ smul      := λ x y, ⟨algebra_map R K x, λ v _, v.valuation_le_one x⟩ * y,
  to_fun    := λ x, ⟨algebra_map R K x, λ v _, v.valuation_le_one x⟩,
  map_one'  := by simpa only [map_one],
  map_mul'  := λ _ _, by simpa only [map_mul],
  map_zero' := by simpa only [map_zero],
  map_add'  := λ _ _, by simpa only [map_add],
  commutes' := λ _, mul_comm _,
  smul_def' := λ _ _, rfl }

/-! ## `S`-units -/

/-- The subgroup of `S`-units of `Kˣ`. -/
@[simps] def unit : subgroup Kˣ :=
(⨅ v ∉ S, (v : height_one_spectrum R).valuation.valuation_subring.unit_group).copy
  {x : Kˣ | ∀ v ∉ S, (v : height_one_spectrum R).valuation (x : K) = 1} $ set.ext $ λ _,
  by simpa only [set_like.mem_coe, subgroup.mem_infi, valuation.mem_unit_group_iff]

lemma unit_eq :
  S.unit K = ⨅ v ∉ S, (v : height_one_spectrum R).valuation.valuation_subring.unit_group :=
subgroup.copy_eq _ _ _

lemma unit_valuation_eq_one (x : S.unit K) {v : height_one_spectrum R} (hv : v ∉ S) :
  v.valuation (x : K) = 1 :=
x.property v hv

/-- The group of `S`-units is the group of units of the ring of `S`-integers. -/
@[simps] def unit_equiv_units_integer : S.unit K ≃* (S.integer K)ˣ :=
{ to_fun    := λ x, ⟨⟨x.val, λ v hv, by { rw [x.property v hv], exact le_rfl }⟩,
    ⟨x.val.inv, λ v hv, by { rw [← v.valuation.map_one, ← congr_arg v.valuation x.val.val_inv,
      map_mul, units.val_eq_coe, x.property v hv, one_mul], exact le_rfl }⟩,
    subtype.mk_eq_mk.mpr x.val.val_inv, subtype.mk_eq_mk.mpr x.val.inv_val⟩,
  inv_fun   := λ x, ⟨units.mk0 x $ λ hx, x.ne_zero ((subring.coe_eq_zero_iff _).mp hx),
  λ v hv, eq_one_of_one_le_mul_left (x.val.property v hv) (x.inv.property v hv) $ eq.ge $
    by { rw [← map_mul, ← v.valuation.map_one], congr' 1, exact subtype.mk_eq_mk.mp x.val_inv }⟩,
  left_inv  := λ _, by { ext, refl },
  right_inv := λ _, by { ext, refl },
  map_mul'  := λ _ _, by { ext, refl } }

end set
