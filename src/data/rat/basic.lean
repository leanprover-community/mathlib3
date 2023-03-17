/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Mario Carneiro, Yaël Dillies
-/
import algebra.order.nonneg.field
import tactic.nth_rewrite

/-!
# Field Structure on the (nonnegative) Rational Numbers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

We put the (discrete) field structure on the type `ℚ` of rational numbers that
was defined in `data.rat.defs`.

## Main Definitions

- `rat.field` is the field structure on `ℚ`.

## Implementation notes

We have to define the field structure in a separate file to avoid cyclic imports:
the `field` class contains a map from `ℚ` (see `field`'s docstring for the rationale),
so we have a dependency `rat.field → field → rat` that is reflected in the import
hierarchy `data.rat.defs → algebra.order.field.basic → algebra.field.basic → data.rat.nnrat.defs →
data.rat.order → data.rat.basic`.

## Tags

rat, rationals, field, ℚ, numerator, denominator, num, denom
-/

open_locale nnrat

instance : field ℚ :=
{ zero             := 0,
  add              := (+),
  neg              := has_neg.neg,
  one              := 1,
  mul              := (*),
  inv              := has_inv.inv,
  nnrat_cast       := subtype.val,
  nnrat_cast_eq    := λ q, begin
    rw [nnrat.num, ←int.cast_coe_nat, int.nat_abs_of_nonneg (rat.num_nonneg_iff_zero_le.2 q.prop)],
    exact (rat.num_div_denom q).symm,
  end,
  rat_cast         := id,
  rat_cast_mk      := λ a b h1 h2, (rat.num_div_denom _).symm,
  qsmul            := (*),
  .. rat.comm_ring,
  .. rat.comm_group_with_zero}

instance : linear_ordered_field ℚ :=
{ zero_le_one     := dec_trivial,
  add_le_add_left := assume a b ab c, rat.add_le_add_left.2 ab,
  mul_pos         := assume a b ha hb, lt_of_le_of_ne
    (rat.mul_nonneg (le_of_lt ha) (le_of_lt hb))
    (mul_ne_zero (ne_of_lt ha).symm (ne_of_lt hb).symm).symm,
  ..rat.field,
  ..rat.linear_order,
  ..rat.semiring }

attribute [derive canonically_linear_ordered_semifield] nnrat

/- Extra instances to short-circuit type class resolution -/
instance : division_ring ℚ      := by apply_instance

namespace nnrat
variables {p q : ℚ≥0}

@[simp] lemma num_div_denom (q : ℚ≥0) : (q.num : ℚ≥0) / q.denom = q :=
begin
  refine ext (_ : ↑((int.nat_abs _ : ℤ)) / _ = _),
  rw int.nat_abs_of_nonneg (rat.num_nonneg_iff_zero_le.2 q.prop),
  exact rat.num_div_denom q,
end

/-- A recursor for nonnegative rationals in terms of numerators and denominators. -/
protected def rec {α : ℚ≥0 → Sort*} (h : Π m n : ℕ, α (m / n)) (q : ℚ≥0) : α q :=
(num_div_denom _).rec (h _ _)

lemma add_def (hp : p.denom ≠ 0) (hq : q.denom ≠ 0) :
  p + q = (p.num * q.denom + p.denom * q.num) / (p.denom * q.denom) :=
by rw [←div_add_div, num_div_denom, num_div_denom]; rwa nat.cast_ne_zero

lemma mul_def : p * q = (p.num * q.num) / (p.denom * q.denom) :=
by simp_rw [mul_div_mul_comm, num_div_denom]

end nnrat

namespace nnrat
variables {α : Type*} {p q : ℚ≥0}

@[simp, norm_cast] lemma coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = q⁻¹ := rfl
@[simp, norm_cast] lemma coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q := rfl
@[simp, norm_cast] lemma coe_zpow (q : ℚ≥0) (n : ℤ) : (↑(q ^ n) : ℚ) = q ^ n := rfl

/-- A `mul_action` over `ℚ` restricts to a `mul_action` over `ℚ≥0`. -/
instance [mul_action ℚ α] : mul_action ℚ≥0 α :=
mul_action.comp_hom α ⟨(coe : ℚ≥0 → ℚ), rfl, λ _ _, rfl⟩

/-- A `distrib_mul_action` over `ℚ` restricts to a `distrib_mul_action` over `ℚ≥0`. -/
instance [add_comm_monoid α] [distrib_mul_action ℚ α] : distrib_mul_action ℚ≥0 α :=
distrib_mul_action.comp_hom α ⟨(coe : ℚ≥0 → ℚ), rfl, λ _ _, rfl⟩

end nnrat

open nnrat

namespace rat
variables {p q : ℚ}

lemma to_nnrat_inv (q : ℚ) : to_nnrat q⁻¹ = (to_nnrat q)⁻¹ :=
begin
  obtain hq | hq := le_total q 0,
  { rw [to_nnrat_eq_zero.mpr hq, inv_zero, to_nnrat_eq_zero.mpr (inv_nonpos.mpr hq)] },
  { nth_rewrite 0 ←rat.coe_to_nnrat q hq,
    rw [←coe_inv, to_nnrat_coe] }
end

lemma to_nnrat_div (hp : 0 ≤ p) : to_nnrat (p / q) = to_nnrat p / to_nnrat q :=
by rw [div_eq_mul_inv, div_eq_mul_inv, ←to_nnrat_inv, ←to_nnrat_mul hp]

lemma to_nnrat_div' (hq : 0 ≤ q) : to_nnrat (p / q) = to_nnrat p / to_nnrat q :=
by rw [div_eq_inv_mul, div_eq_inv_mul, to_nnrat_mul (inv_nonneg.2 hq), to_nnrat_inv]

end rat
