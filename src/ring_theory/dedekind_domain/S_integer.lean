/-
Copyright (c) 2022 David Kurniadi Angdinata. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Kurniadi Angdinata
-/

import ring_theory.dedekind_domain.adic_valuation

/-!
# `S`-integers and `S`-units of fraction fields of Dedekind domains

This file defines the ring of `S`-integers and the group of `S`-units of the field of fractions of a
Dedekind domain, to be specialised to the case of a number field or a function field separately.

TODO:
 * notation for `S`-integers and `S`-units.
 * proof that `S`-integers is the intersection of valuation rings.
 * proof that `S`-units is the kernel of a map to a product.
 * proof that `∅`-integers is the usual ring of integers.
 * finite generation of `S`-units and Dirichlet's `S`-unit theorem.

## Main definitions

 * `set.integer`: the ring of `S`-integers.
 * `set.unit`: the group of `S`-units.

## Main statements

 * `set.units_integer_equiv_unit`: units of `S`-integers are `S`-units.

## References

 * [D Marcus, *Number Fields*][marcus1977number]
 * [J W S Cassels, A Frölich, *Algebraic Number Theory*][cassels1967algebraic]
 * [J Neukirch, *Algebraic Number Theory*][Neukirch1992]

## Tags

S-integer, S-unit
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
{ carrier   := {x : K | ∀ v ∉ S, (v : height_one_spectrum R).valuation x ≤ 1},
  mul_mem'  := λ _ _ hx hy v hv, by simp only [map_mul, mul_le_one₀ (hx v hv) (hy v hv)],
  one_mem'  := λ _ _, by simp only [map_one, le_refl],
  add_mem'  := λ _ _ hx hy v hv, v.valuation.map_add_le (hx v hv) (hy v hv),
  zero_mem' := λ _ _, by simp only [map_zero, zero_le_one],
  neg_mem'  := λ _ hx v hv, by simp only [valuation.map_neg, hx v hv] }

lemma integer_eq :
  S.integer K = ⨅ v ∉ S, (v : height_one_spectrum R).valuation.valuation_subring.to_subring :=
subring.ext $ λ _, by simpa only [subring.mem_infi]

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
{ carrier  := {x : Kˣ | ∀ v ∉ S, (v : height_one_spectrum R).valuation (x : K) = 1},
  mul_mem' := λ _ _ hx hy v hv, by rw [units.coe_mul, map_mul, hx v hv, hy v hv, one_mul],
  one_mem' := λ _ _, map_one _,
  inv_mem' := λ _ hx v hv, by rw [map_units_inv, hx v hv, inv_one] }

/-- The group of units of the ring of `S`-integers is the group of `S`-units. -/
@[simps] def units_integer_equiv_unit : (S.integer K)ˣ ≃* S.unit K :=
{ to_fun    := λ x, ⟨units.mk0 x $ λ hx, x.ne_zero ((subring.coe_eq_zero_iff _).mp hx),
  λ v hv, eq_one_of_mul_eq_one_left (x.val.property v hv) (x.inv.property v hv) $
    by { rw [← map_mul, ← v.valuation.map_one], congr' 1, exact subtype.mk_eq_mk.mp x.val_inv }⟩,
  inv_fun   := λ x, ⟨⟨x.val, λ v hv, by { rw [x.property v hv], exact le_rfl }⟩,
    ⟨x.val.inv, λ v hv, by { rw [← v.valuation.map_one, ← congr_arg v.valuation x.val.val_inv,
      map_mul, units.val_eq_coe, x.property v hv, one_mul], exact le_rfl }⟩,
    subtype.mk_eq_mk.mpr x.val.val_inv, subtype.mk_eq_mk.mpr x.val.inv_val⟩,
  left_inv  := λ _, by { ext, refl },
  right_inv := λ _, by { ext, refl },
  map_mul'  := λ _ _, by { ext, refl } }

end set
