/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.group.commute
import algebra.ring.basic
import data.equiv.mul_add
import algebra.group.opposite

/-!
# (Semi)ring structure on multiplicative opposite

In this file we define `ring` and related instances on `mul_opposite α = αᵐᵒᵖ`.

## Notation

`αᵐᵒᵖ = mul_opposite α`
-/

universes u v
open function

namespace mul_opposite

variables (α : Type u)

instance [distrib α] : distrib αᵐᵒᵖ :=
{ left_distrib := λ x y z, unop_injective $ add_mul (unop y) (unop z) (unop x),
  right_distrib := λ x y z, unop_injective $ mul_add (unop z) (unop x) (unop y),
  .. mul_opposite.has_add α, .. mul_opposite.has_mul α }

instance [non_unital_non_assoc_semiring α] : non_unital_non_assoc_semiring αᵐᵒᵖ :=
{ .. mul_opposite.add_comm_monoid α, .. mul_opposite.mul_zero_class α, .. mul_opposite.distrib α }

instance [non_unital_semiring α] : non_unital_semiring αᵐᵒᵖ :=
{ .. mul_opposite.semigroup_with_zero α, .. mul_opposite.non_unital_non_assoc_semiring α }

instance [non_assoc_semiring α] : non_assoc_semiring αᵐᵒᵖ :=
{ .. mul_opposite.mul_zero_one_class α, .. mul_opposite.non_unital_non_assoc_semiring α }

instance [semiring α] : semiring αᵐᵒᵖ :=
{ .. mul_opposite.non_unital_semiring α, .. mul_opposite.non_assoc_semiring α,
  .. mul_opposite.monoid_with_zero α }

instance [comm_semiring α] : comm_semiring αᵐᵒᵖ :=
{ .. mul_opposite.semiring α, .. mul_opposite.comm_semigroup α }

instance [ring α] : ring αᵐᵒᵖ :=
{ .. mul_opposite.add_comm_group α, .. mul_opposite.monoid α, .. mul_opposite.semiring α }

instance [comm_ring α] : comm_ring αᵐᵒᵖ :=
{ .. mul_opposite.ring α, .. mul_opposite.comm_semiring α }

instance [ring α] [is_domain α] : is_domain αᵐᵒᵖ :=
{ .. mul_opposite.no_zero_divisors α, .. mul_opposite.ring α, .. mul_opposite.nontrivial α }

variable {α}

end mul_opposite

open mul_opposite

/-- A ring homomorphism `f : R →+* S` such that `f x` commutes with `f y` for all `x, y` defines
a ring homomorphism to `Sᵐᵒᵖ`. -/
@[simps {fully_applied := ff}]
def ring_hom.to_opposite {R S : Type*} [semiring R] [semiring S] (f : R →+* S)
  (hf : ∀ x y, commute (f x) (f y)) : R →+* Sᵐᵒᵖ :=
{ to_fun := mul_opposite.op ∘ f,
  .. ((op_add_equiv : S ≃+ Sᵐᵒᵖ).to_add_monoid_hom.comp ↑f : R →+ Sᵐᵒᵖ),
  .. f.to_monoid_hom.to_opposite hf }

/-- A ring hom `α →+* β` can equivalently be viewed as a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def ring_hom.op {α β} [non_assoc_semiring α] [non_assoc_semiring β] :
  (α →+* β) ≃ (αᵐᵒᵖ →+* βᵐᵒᵖ) :=
{ to_fun    := λ f, { ..f.to_add_monoid_hom.op, ..f.to_monoid_hom.op },
  inv_fun   := λ f, { ..f.to_add_monoid_hom.unop, ..f.to_monoid_hom.unop },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, simp } }

/-- The 'unopposite' of a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. Inverse to `ring_hom.op`. -/
@[simp] def ring_hom.unop {α β} [non_assoc_semiring α] [non_assoc_semiring β] :
  (αᵐᵒᵖ →+* βᵐᵒᵖ) ≃ (α →+* β) := ring_hom.op.symm
