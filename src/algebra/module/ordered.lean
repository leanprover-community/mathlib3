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
  monoid and on the ring. There is a correspondence between this structure and convex cones,
  which is proven in `analysis/convex/cone.lean`.

## Implementation notes

* We choose to define `ordered_semimodule` so that it extends `semimodule` only, as is done
  for semimodules itself.
* To get ordered modules and ordered vector spaces, it suffices to the replace the
  `order_add_comm_monoid` and the `ordered_semiring` as desired.

## References

* https://en.wikipedia.org/wiki/Ordered_vector_space

## Tags

ordered semimodule, ordered module, ordered vector space
-/


/--
An ordered semimodule is an ordered additive commutative monoid
with a partial order in which the scalar multiplication is compatible with the order.
-/
@[protect_proj, ancestor semimodule]
class ordered_semimodule (R β : Type*)
  [ordered_semiring R] [ordered_add_comm_monoid β] extends semimodule R β :=
(smul_lt_smul_of_pos : ∀ {a b : β}, ∀ {c : R}, a < b → 0 < c → c • a < c • b)
(lt_of_smul_lt_smul_of_nonneg : ∀ {a b : β}, ∀ {c : R}, c • a < c • b → 0 ≤ c → a < b)

section ordered_semimodule

variables {R β : Type*} [ordered_semiring R] [ordered_add_comm_monoid β] [ordered_semimodule R β]
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

end ordered_semimodule

section instances

variables {R : Type*} [linear_ordered_ring R]

instance linear_ordered_ring.to_ordered_semimodule : ordered_semimodule R R :=
{ smul_lt_smul_of_pos      := ordered_semiring.mul_lt_mul_of_pos_left,
  lt_of_smul_lt_smul_of_nonneg  := λ _ _ _, lt_of_mul_lt_mul_left }

end instances

section order_dual

variables {R β : Type*}

instance [semiring R] [ordered_add_comm_monoid β] [semimodule R β] : has_scalar R (order_dual β) :=
{ smul := @has_scalar.smul R β _ }

instance [semiring R] [ordered_add_comm_monoid β] [semimodule R β] : mul_action R (order_dual β) :=
{ one_smul := @mul_action.one_smul R β _ _,
  mul_smul := @mul_action.mul_smul R β _ _ }

instance [semiring R] [ordered_add_comm_monoid β] [semimodule R β] : distrib_mul_action R (order_dual β) :=
{ smul_add := @distrib_mul_action.smul_add R β _ _ _,
  smul_zero := @distrib_mul_action.smul_zero R β _ _ _ }

instance [semiring R] [ordered_add_comm_monoid β] [semimodule R β] : semimodule R (order_dual β) :=
{ add_smul := @semimodule.add_smul R β _ _ _,
  zero_smul := @semimodule.zero_smul R β _ _ _ }

instance [ordered_semiring R] [ordered_add_comm_monoid β] [ordered_semimodule R β] :
  ordered_semimodule R (order_dual β) :=
{ smul_lt_smul_of_pos := λ a b, @ordered_semimodule.smul_lt_smul_of_pos R β _ _ _ b a,
  lt_of_smul_lt_smul_of_nonneg := λ a b, @ordered_semimodule.lt_of_smul_lt_smul_of_nonneg R β _ _ _ b a }

end order_dual
