/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import algebra.ring.basic
import algebra.group.opposite

/-!
# Ring structures on the multiplicative opposite
-/
universes u v
variables (α : Type u)

namespace mul_opposite

instance [distrib α] : distrib αᵐᵒᵖ :=
{ left_distrib := λ x y z, unop_injective $ add_mul (unop y) (unop z) (unop x),
  right_distrib := λ x y z, unop_injective $ mul_add (unop z) (unop x) (unop y),
  .. mul_opposite.has_add α, .. mul_opposite.has_mul α }

instance [mul_zero_class α] : mul_zero_class αᵐᵒᵖ :=
{ zero := 0,
  mul := (*),
  zero_mul := λ x, unop_injective $ mul_zero $ unop x,
  mul_zero := λ x, unop_injective $ zero_mul $ unop x }

instance [mul_zero_one_class α] : mul_zero_one_class αᵐᵒᵖ :=
{ .. mul_opposite.mul_zero_class α, .. mul_opposite.mul_one_class α }

instance [semigroup_with_zero α] : semigroup_with_zero αᵐᵒᵖ :=
{ .. mul_opposite.semigroup α, .. mul_opposite.mul_zero_class α }

instance [monoid_with_zero α] : monoid_with_zero αᵐᵒᵖ :=
{ .. mul_opposite.monoid α, .. mul_opposite.mul_zero_one_class α }

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

instance [non_unital_non_assoc_ring α] : non_unital_non_assoc_ring αᵐᵒᵖ :=
{ .. mul_opposite.add_comm_group α, .. mul_opposite.mul_zero_class α, .. mul_opposite.distrib α}

instance [non_unital_ring α] : non_unital_ring αᵐᵒᵖ :=
{ .. mul_opposite.add_comm_group α, .. mul_opposite.semigroup_with_zero α,
  .. mul_opposite.distrib α}

instance [non_assoc_ring α] : non_assoc_ring αᵐᵒᵖ :=
{ .. mul_opposite.add_comm_group α, .. mul_opposite.mul_zero_one_class α, .. mul_opposite.distrib α}

instance [ring α] : ring αᵐᵒᵖ :=
{ .. mul_opposite.add_comm_group α, .. mul_opposite.monoid α, .. mul_opposite.semiring α }

instance [comm_ring α] : comm_ring αᵐᵒᵖ :=
{ .. mul_opposite.ring α, .. mul_opposite.comm_semiring α }

instance [has_zero α] [has_mul α] [no_zero_divisors α] : no_zero_divisors αᵐᵒᵖ :=
{ eq_zero_or_eq_zero_of_mul_eq_zero := λ x y (H : op (_ * _) = op (0:α)),
    or.cases_on (eq_zero_or_eq_zero_of_mul_eq_zero $ op_injective H)
      (λ hy, or.inr $ unop_injective $ hy) (λ hx, or.inl $ unop_injective $ hx), }

instance [ring α] [is_domain α] : is_domain αᵐᵒᵖ :=
{ .. mul_opposite.no_zero_divisors α, .. mul_opposite.ring α, .. mul_opposite.nontrivial α }

instance [group_with_zero α] : group_with_zero αᵐᵒᵖ :=
{ mul_inv_cancel := λ x hx, unop_injective $ inv_mul_cancel $ unop_injective.ne hx,
  inv_zero := unop_injective inv_zero,
  .. mul_opposite.monoid_with_zero α, .. mul_opposite.div_inv_monoid α,
  .. mul_opposite.nontrivial α }

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

/-- A monoid homomorphism `f : R →* S` such that `f x` commutes with `f y` for all `x, y` defines
a monoid homomorphism from `Rᵐᵒᵖ`. -/
@[simps {fully_applied := ff}]
def ring_hom.from_opposite {R S : Type*} [semiring R] [semiring S] (f : R →+* S)
  (hf : ∀ x y, commute (f x) (f y)) : Rᵐᵒᵖ →+* S :=
{ to_fun := f ∘ mul_opposite.unop,
  .. (f.to_add_monoid_hom.comp (op_add_equiv : R ≃+ Rᵐᵒᵖ).symm.to_add_monoid_hom : Rᵐᵒᵖ →+ S),
  .. f.to_monoid_hom.from_opposite hf }

/-- A ring hom `α →+* β` can equivalently be viewed as a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. This is the
action of the (fully faithful) `ᵐᵒᵖ`-functor on morphisms. -/
@[simps]
def ring_hom.op {α β} [non_assoc_semiring α] [non_assoc_semiring β] :
  (α →+* β) ≃ (αᵐᵒᵖ →+* βᵐᵒᵖ) :=
{ to_fun    := λ f, { ..f.to_add_monoid_hom.mul_op, ..f.to_monoid_hom.op },
  inv_fun   := λ f, { ..f.to_add_monoid_hom.mul_unop, ..f.to_monoid_hom.unop },
  left_inv  := λ f, by { ext, refl },
  right_inv := λ f, by { ext, simp } }

/-- The 'unopposite' of a ring hom `αᵐᵒᵖ →+* βᵐᵒᵖ`. Inverse to `ring_hom.op`. -/
@[simp] def ring_hom.unop {α β} [non_assoc_semiring α] [non_assoc_semiring β] :
  (αᵐᵒᵖ →+* βᵐᵒᵖ) ≃ (α →+* β) := ring_hom.op.symm
