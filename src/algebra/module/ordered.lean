/-
Copyright (c) 2020 Frédéric Dupuis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Frédéric Dupuis
-/

import algebra.module.basic
import algebra.ordered_group

/-!
# Ordered semimodules

In this file we define

* `ordered_semimodule R M` : an ordered additive commutative monoid `M` is an `ordered_semimodule`
  over an `ordered_semiring` `R` if the scalar product respects the order relation on the
  monoid and on the ring.

## Implementation notes

* We choose to define `ordered_semimodule` so that it extends `semimodule` only, as is done
  for semimodules itself.
* To get ordered modules and ordered vector spaces, it suffices to the replace the
  `order_add_comm_monoid` and the `ordered_semiring` as desired.

## TODO

* Connect this with convex cones: show that a convex cone defines an order on the vector space
  and vice-versa.

## References

* https://en.wikipedia.org/wiki/Ordered_vector_space

## Tags

ordered semimodule, ordered module, ordered vector space
-/


set_option default_priority 100 -- see Note [default priority]

/--
An ordered semimodule is an ordered additive commutative monoid
with a partial order in which the scalar multiplication is compatible with the order.
-/
@[protect_proj, ancestor semimodule]
class ordered_semimodule (R β : Type*)
  [ordered_semiring R] [ordered_add_comm_monoid β] extends semimodule R β :=
(smul_lt_smul_of_pos : ∀ {a b : β}, ∀ {c : R}, a < b → 0 < c → c • a < c • b)
(lt_of_smul_lt_smul_of_nonneg : ∀ a b : β, ∀ c : R, c • a < c • b → 0 ≤ c → a < b)

variable {R : Type*}

instance linear_ordered_ring.to_ordered_semimodule [linear_ordered_ring R] :
  ordered_semimodule R R :=
{ smul_lt_smul_of_pos      := ordered_semiring.mul_lt_mul_of_pos_left,
  lt_of_smul_lt_smul_of_nonneg  := lt_of_mul_lt_mul_left }

variables {β : Type*} [ordered_semiring R] [ordered_add_comm_monoid β] [ordered_semimodule R β]
  {a b : β} {c : R}

lemma smul_lt_smul_of_pos : a < b → 0 < c → c • a < c • b := ordered_semimodule.smul_lt_smul_of_pos

lemma smul_le_smul_of_nonneg (h₁ : a ≤ b) (h₂ : 0 ≤ c) : c • a ≤ c • b :=
begin
  by_cases H₁ : c = 0,
  { simp [H₁, zero_smul] },
  { by_cases H₂ : a = b,
    { rw H₂ },
    { exact le_of_lt
        (smul_lt_smul_of_pos (lt_of_le_of_ne h₁ H₂) (lt_of_le_of_ne h₂ (ne.symm H₁))), } }
end
