/-
Copyright (c) 2018 Simon Hudon. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Simon Hudon, Patrick Massot
-/
import tactic.pi_instances
import algebra.group.pi
import algebra.hom.ring

/-!
# Pi instances for ring

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines instances for ring, semiring and related structures on Pi Types
-/

namespace pi
universes u v w
variable {I : Type u}     -- The indexing type
variable {f : I → Type v} -- The family of types already equipped with instances
variables (x y : Π i, f i) (i : I)

instance distrib [Π i, distrib $ f i] : distrib (Π i : I, f i) :=
by refine_struct { add := (+), mul := (*), .. }; tactic.pi_instance_derive_field

instance non_unital_non_assoc_semiring [∀ i, non_unital_non_assoc_semiring $ f i] :
  non_unital_non_assoc_semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), add := (+), mul := (*), .. };
  tactic.pi_instance_derive_field

instance non_unital_semiring [∀ i, non_unital_semiring $ f i] :
  non_unital_semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), add := (+), mul := (*), .. };
  tactic.pi_instance_derive_field

instance non_assoc_semiring [∀ i, non_assoc_semiring $ f i] :
  non_assoc_semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*), .. };
  tactic.pi_instance_derive_field

instance semiring [∀ i, semiring $ f i] : semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),
  nsmul := add_monoid.nsmul, npow := monoid.npow };
tactic.pi_instance_derive_field

instance non_unital_comm_semiring [∀ i, non_unital_comm_semiring $ f i] :
  non_unital_comm_semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), add := (+), mul := (*), nsmul := add_monoid.nsmul };
tactic.pi_instance_derive_field

instance comm_semiring [∀ i, comm_semiring $ f i] : comm_semiring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),
  nsmul := add_monoid.nsmul, npow := monoid.npow };
tactic.pi_instance_derive_field

instance non_unital_non_assoc_ring [∀ i, non_unital_non_assoc_ring $ f i] :
  non_unital_non_assoc_ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), add := (+), mul := (*),
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul };
tactic.pi_instance_derive_field

instance non_unital_ring [∀ i, non_unital_ring $ f i] :
  non_unital_ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), add := (+), mul := (*),
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul };
tactic.pi_instance_derive_field

instance non_assoc_ring [∀ i, non_assoc_ring $ f i] :
  non_assoc_ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), add := (+), mul := (*),
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul };
tactic.pi_instance_derive_field

instance ring [∀ i, ring $ f i] : ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul,
  npow := monoid.npow };
tactic.pi_instance_derive_field

instance non_unital_comm_ring [∀ i, non_unital_comm_ring $ f i] :
  non_unital_comm_ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), add := (+), mul := (*), neg := has_neg.neg,
  nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul };
tactic.pi_instance_derive_field

instance comm_ring [∀ i, comm_ring $ f i] : comm_ring (Π i : I, f i) :=
by refine_struct { zero := (0 : Π i, f i), one := 1, add := (+), mul := (*),
  neg := has_neg.neg, nsmul := add_monoid.nsmul, zsmul := sub_neg_monoid.zsmul,
  npow := monoid.npow };
tactic.pi_instance_derive_field

/-- A family of non-unital ring homomorphisms `f a : γ →ₙ+* β a` defines a non-unital ring
homomorphism `pi.non_unital_ring_hom f : γ →+* Π a, β a` given by
`pi.non_unital_ring_hom f x b = f b x`. -/
@[simps]
protected def non_unital_ring_hom {γ : Type w} [Π i, non_unital_non_assoc_semiring (f i)]
  [non_unital_non_assoc_semiring γ] (g : Π i, γ →ₙ+* f i) : γ →ₙ+* Π i, f i :=
{ to_fun := λ x b, g b x,
  .. pi.mul_hom (λ i, (g i).to_mul_hom),
  .. pi.add_monoid_hom (λ i, (g i).to_add_monoid_hom) }

lemma non_unital_ring_hom_injective {γ : Type w} [nonempty I]
  [Π i, non_unital_non_assoc_semiring (f i)] [non_unital_non_assoc_semiring γ] (g : Π i, γ →ₙ+* f i)
  (hg : ∀ i, function.injective (g i)) : function.injective (pi.non_unital_ring_hom g) :=
mul_hom_injective (λ i, (g i).to_mul_hom) hg

/-- A family of ring homomorphisms `f a : γ →+* β a` defines a ring homomorphism
`pi.ring_hom f : γ →+* Π a, β a` given by `pi.ring_hom f x b = f b x`. -/
@[simps]
protected def ring_hom {γ : Type w} [Π i, non_assoc_semiring (f i)] [non_assoc_semiring γ]
  (g : Π i, γ →+* f i) : γ →+* Π i, f i :=
{ to_fun := λ x b, g b x,
  .. pi.monoid_hom (λ i, (g i).to_monoid_hom),
  .. pi.add_monoid_hom (λ i, (g i).to_add_monoid_hom) }

lemma ring_hom_injective {γ : Type w} [nonempty I] [Π i, non_assoc_semiring (f i)]
  [non_assoc_semiring γ] (g : Π i, γ →+* f i) (hg : ∀ i, function.injective (g i)) :
  function.injective (pi.ring_hom g) :=
monoid_hom_injective (λ i, (g i).to_monoid_hom) hg

end pi

section non_unital_ring_hom

universes u v
variable {I : Type u}

/-- Evaluation of functions into an indexed collection of non-unital rings at a point is a
non-unital ring homomorphism. This is `function.eval` as a `non_unital_ring_hom`. -/
@[simps]
def pi.eval_non_unital_ring_hom (f : I → Type v)
  [Π i, non_unital_non_assoc_semiring (f i)] (i : I) : (Π i, f i) →ₙ+* f i :=
{ ..(pi.eval_mul_hom f i),
  ..(pi.eval_add_monoid_hom f i) }

/-- `function.const` as a `non_unital_ring_hom`. -/
@[simps]
def pi.const_non_unital_ring_hom (α β : Type*) [non_unital_non_assoc_semiring β] : β →ₙ+* (α → β) :=
{ to_fun := function.const _,
  .. pi.non_unital_ring_hom (λ _, non_unital_ring_hom.id β) }

/-- Non-unital ring homomorphism between the function spaces `I → α` and `I → β`, induced by a
non-unital ring homomorphism `f` between `α` and `β`. -/
@[simps] protected def non_unital_ring_hom.comp_left {α β : Type*} [non_unital_non_assoc_semiring α]
  [non_unital_non_assoc_semiring β] (f : α →ₙ+* β) (I : Type*) :
  (I → α) →ₙ+* (I → β) :=
{ to_fun := λ h, f ∘ h,
  .. f.to_mul_hom.comp_left I,
  .. f.to_add_monoid_hom.comp_left I }

end non_unital_ring_hom

section ring_hom

universes u v
variable {I : Type u}

/-- Evaluation of functions into an indexed collection of rings at a point is a ring
homomorphism. This is `function.eval` as a `ring_hom`. -/
@[simps]
def pi.eval_ring_hom (f : I → Type v) [Π i, non_assoc_semiring (f i)] (i : I) :
  (Π i, f i) →+* f i :=
{ ..(pi.eval_monoid_hom f i),
  ..(pi.eval_add_monoid_hom f i) }

/-- `function.const` as a `ring_hom`. -/
@[simps]
def pi.const_ring_hom (α β : Type*) [non_assoc_semiring β] : β →+* (α → β) :=
{ to_fun := function.const _,
  .. pi.ring_hom (λ _, ring_hom.id β) }

/-- Ring homomorphism between the function spaces `I → α` and `I → β`, induced by a ring
homomorphism `f` between `α` and `β`. -/
@[simps] protected def ring_hom.comp_left {α β : Type*} [non_assoc_semiring α]
  [non_assoc_semiring β] (f : α →+* β) (I : Type*) :
  (I → α) →+* (I → β) :=
{ to_fun := λ h, f ∘ h,
  .. f.to_monoid_hom.comp_left I,
  .. f.to_add_monoid_hom.comp_left I }

end ring_hom
