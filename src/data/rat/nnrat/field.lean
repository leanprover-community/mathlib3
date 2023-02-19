/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.order.nonneg.field
import data.rat.field
import tactic.nth_rewrite

/-!
# Field structure on the nonnegative rationals

This file provides additional results about `nnrat` that could not
-/

open function
open_locale nnrat

namespace nnrat
variables {α : Type*} {p q : ℚ≥0}

attribute [derive linear_ordered_semifield] nnrat

@[simp, norm_cast] lemma coe_inv (q : ℚ≥0) : ((q⁻¹ : ℚ≥0) : ℚ) = q⁻¹ := rfl
@[simp, norm_cast] lemma coe_div (p q : ℚ≥0) : ((p / q : ℚ≥0) : ℚ) = p / q := rfl

/-- A `mul_action` over `ℚ` restricts to a `mul_action` over `ℚ≥0`. -/
instance [mul_action ℚ α] : mul_action ℚ≥0 α := mul_action.comp_hom α cast_hom.to_monoid_hom

/-- A `distrib_mul_action` over `ℚ` restricts to a `distrib_mul_action` over `ℚ≥0`. -/
instance [add_comm_monoid α] [distrib_mul_action ℚ α] : distrib_mul_action ℚ≥0 α :=
distrib_mul_action.comp_hom α cast_hom.to_monoid_hom

@[simp, norm_cast] lemma coe_zpow (q : ℚ≥0) (n : ℤ) : (↑(q ^ n) : ℚ) = q ^ n :=
map_zpow₀ cast_hom _ _

@[norm_cast] lemma coe_nsmul (q : ℚ≥0) (n : ℕ) : ↑(n • q) = n • (q : ℚ) :=
cast_hom.to_add_monoid_hom.map_nsmul _ _

@[simp, norm_cast] lemma coe_max (x y : ℚ≥0) : ((max x y : ℚ≥0) : ℚ) = max (x : ℚ) (y : ℚ) :=
coe_mono.map_max

@[simp, norm_cast] lemma coe_min (x y : ℚ≥0) : ((min x y : ℚ≥0) : ℚ) = min (x : ℚ) (y : ℚ) :=
coe_mono.map_min

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
