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

TODO: notation for `S`-integers and `S`-units, proof that `S`-integers is the intersection of
valuation rings, proof that `S`-units is the kernel of a map to a product, proof that `∅`-integers
is the usual ring of integers, finite generation of `S`-units and Dirichlet's `S`-unit theorem.

## Main definitions

* `is_dedekind_domain.S_integer_ring`: the ring of `S`-integers.
* `is_dedekind_domain.S_unit_group`: the group of `S`-units.

## Main statements

* `is_dedekind_domain.S_integer_unit`: the units of the `S`-integers are the `S`-units.

## References

* https://encyclopediaofmath.org/wiki/S-integer
* https://en.wikipedia.org/wiki/S-unit

## Tags

S-integer, S-unit
-/

open_locale non_zero_divisors

namespace is_dedekind_domain

noncomputable theory

universes u v

variables {R : Type u} [comm_ring R] [is_domain R] [is_dedekind_domain R] (K : Type v) [field K]
  [algebra R K] [is_fraction_ring R K] (S : set $ height_one_spectrum R)

/-- The subring of `S`-integers of `K`. -/
def S_integer_ring : subring K :=
{ carrier   := {x : K | ∀ v ∉ S, (v : height_one_spectrum R).valuation x ≤ 1},
  mul_mem'  := λ _ _ hx hy v hv, by simp only [map_mul, mul_le_one₀ (hx v hv) (hy v hv)],
  one_mem'  := λ _ _, by simp only [map_one, le_refl],
  add_mem'  := λ _ _ hx hy v hv, v.valuation.map_add_le (hx v hv) (hy v hv),
  zero_mem' := λ _ _, by simp only [map_zero, zero_le_one],
  neg_mem'  := λ _ hx v hv, by simp only [valuation.map_neg, hx v hv] }

/-- The subgroup of `S`-units of `Kˣ`. -/
def S_unit_group : subgroup Kˣ :=
{ carrier  := {x : Kˣ | ∀ v ∉ S, (v : height_one_spectrum R).valuation (x : K) = 1},
  mul_mem' := λ _ _ hx hy v hv, by rw [units.coe_mul, map_mul, hx v hv, hy v hv, one_mul],
  one_mem' := λ _ _, map_one _,
  inv_mem' := λ _ hx v hv, by rw [valuation.map_units_inv, hx v hv, inv_one] }

/-- The group of units of the ring of `S`-integers is the group of `S`-units. -/
def S_integer_unit : (S_integer_ring K S)ˣ ≃* S_unit_group K S :=
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

end is_dedekind_domain
