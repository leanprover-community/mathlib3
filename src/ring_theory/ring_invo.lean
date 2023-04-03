/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/
import algebra.ring.equiv
import algebra.ring.opposite

/-!
# Ring involutions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines a ring involution as a structure extending `R ≃+* Rᵐᵒᵖ`,
with the additional fact `f.involution : (f (f x).unop).unop = x`.

## Notations

We provide a coercion to a function `R → Rᵐᵒᵖ`.

## References

* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring involution
-/

variables (R : Type*)

set_option old_structure_cmd true

/-- A ring involution -/
structure ring_invo [semiring R] extends R ≃+* Rᵐᵒᵖ :=
(involution' : ∀ x, (to_fun (to_fun x).unop).unop = x)

/-- The equivalence of rings underlying a ring involution. -/
add_decl_doc ring_invo.to_ring_equiv

/-- `ring_invo_class F R S` states that `F` is a type of ring involutions.
You should extend this class when you extend `ring_invo`. -/
class ring_invo_class (F : Type*) (R : out_param Type*) [semiring R]
  extends ring_equiv_class F R Rᵐᵒᵖ :=
(involution : ∀ (f : F) (x), (f (f x).unop).unop = x)

namespace ring_invo
variables {R} [semiring R]

instance (R : Type*) [semiring R] : ring_invo_class (ring_invo R) R :=
{ coe := to_fun,
  inv :=  inv_fun,
  coe_injective' := λ e f h₁ h₂, by { cases e, cases f, congr' },
  map_add := map_add',
  map_mul := map_mul',
  left_inv := left_inv,
  right_inv := right_inv,
  involution := involution' }

/-- Construct a ring involution from a ring homomorphism. -/
def mk' (f : R →+* Rᵐᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) :
  ring_invo R :=
{ inv_fun := λ r, (f r.unop).unop,
  left_inv := λ r, involution r,
  right_inv := λ r, mul_opposite.unop_injective $ involution _,
  involution' := involution,
  .. f }

/-- Helper instance for when there's too many metavariables to apply
`fun_like.has_coe_to_fun` directly. -/
instance : has_coe_to_fun (ring_invo R) (λ _, R → Rᵐᵒᵖ) := ⟨λ f, f.to_ring_equiv.to_fun⟩

@[simp]
lemma to_fun_eq_coe (f : ring_invo R) : f.to_fun = f := rfl

@[simp]
lemma involution (f : ring_invo R) (x : R) : (f (f x).unop).unop = x :=
f.involution' x

instance has_coe_to_ring_equiv : has_coe (ring_invo R) (R ≃+* Rᵐᵒᵖ) :=
⟨ring_invo.to_ring_equiv⟩

@[norm_cast] lemma coe_ring_equiv (f : ring_invo R) (a : R) :
  (f : R ≃+* Rᵐᵒᵖ) a = f a := rfl

@[simp] lemma map_eq_zero_iff (f : ring_invo R) {x : R} : f x = 0 ↔ x = 0 :=
f.to_ring_equiv.map_eq_zero_iff

end ring_invo

open ring_invo

section comm_ring
variables [comm_ring R]

/-- The identity function of a `comm_ring` is a ring involution. -/
protected def ring_invo.id : ring_invo R :=
{ involution' := λ r, rfl,
  ..(ring_equiv.to_opposite R) }

instance : inhabited (ring_invo R) := ⟨ring_invo.id _⟩

end comm_ring
