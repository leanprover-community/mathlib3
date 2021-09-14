/-
Copyright (c) 2021 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen
-/
import algebra.absolute_value
import algebra.euclidean_domain

/-!
# Euclidean absolute values

This file defines a predicate `absolute_value.is_euclidean abv` stating the
absolute value is compatible with the Euclidean domain structure on its domain.

## Main definitions

 * `absolute_value.is_euclidean abv` is a predicate on absolute values on `R` mapping to `S`
    that preserve the order on `R` arising from the Euclidean domain structure.
 * `absolute_value.abs_is_euclidean` shows the "standard" absolute value on `ℤ`,
   mapping negative `x` to `-x`, is euclidean.
-/
local infix ` ≺ `:50 := euclidean_domain.r

namespace absolute_value

section ordered_semiring

variables {R S : Type*} [euclidean_domain R] [ordered_semiring S]
variables (abv : absolute_value R S)

/-- An absolute value `abv : R → S` is Euclidean if it is compatible with the
`euclidean_domain` structure on `R`, namely `abv` is strictly monotone with respect to the well
founded relation `≺` on `R`. -/
structure is_euclidean : Prop :=
(map_lt_map_iff' : ∀ {x y}, abv x < abv y ↔ x ≺ y)

namespace is_euclidean

variables {abv}

-- Rearrange the parameters to `map_lt_map_iff'` so it elaborates better.
lemma map_lt_map_iff {x y : R} (h : abv.is_euclidean) : abv x < abv y ↔ x ≺ y :=
map_lt_map_iff' h

attribute [simp] map_lt_map_iff

lemma sub_mod_lt (h : abv.is_euclidean) (a : R) {b : R} (hb : b ≠ 0) :
  abv (a % b) < abv b :=
h.map_lt_map_iff.mpr (euclidean_domain.mod_lt a hb)

end is_euclidean

end ordered_semiring

section int

open int

-- TODO: generalize to `linear_ordered_euclidean_domain`s if we ever get a definition of those
/-- `abs : ℤ → ℤ` is a Euclidean absolute value -/
protected lemma abs_is_euclidean : is_euclidean (absolute_value.abs : absolute_value ℤ ℤ) :=
{ map_lt_map_iff' := λ x y, show abs x < abs y ↔ nat_abs x < nat_abs y,
    by rw [abs_eq_nat_abs, abs_eq_nat_abs, coe_nat_lt] }

end int

end absolute_value
