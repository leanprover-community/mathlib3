/-
Copyright (c) 2018 Andreas Swerdlow. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andreas Swerdlow, Kenny Lau
-/
import data.equiv.ring
import algebra.opposites

/-!
# Ring antihomomorphisms, isomorphisms, antiisomorphisms and involutions

This file defines ring antihomomorphisms, antiisomorphism and involutions
and proves basic properties of them.

## Notations

All types defined in this file are given a coercion to the underlying function.

## References

* <https://en.wikipedia.org/wiki/Antihomomorphism>
* <https://en.wikipedia.org/wiki/Involution_(mathematics)#Ring_theory>

## Tags

Ring isomorphism, automorphism, antihomomorphism, antiisomorphism, antiautomorphism, involution
-/

variables (R : Type*) (F : Type*)

/-- A ring involution -/
structure ring_invo [semiring R] extends R ≃+* Rᵒᵖ :=
(involution' : ∀ x, (to_fun (to_fun x).unop).unop = x)

namespace ring_invo
variables {R} [semiring R]

/-- Construct a ring involution from a ring homomorphism. -/
def mk' (f : R →+* Rᵒᵖ) (involution : ∀ r, (f (f r).unop).unop = r) :
  ring_invo R :=
{ inv_fun := λ r, (f r.unop).unop,
  left_inv := λ r, involution r,
  right_inv := λ r, congr_arg opposite.op (involution (r.unop)),
  involution' := involution,
  ..f }

instance : has_coe_to_fun (ring_invo R) := ⟨_, λ f, f.to_ring_equiv.to_fun⟩

@[simp]
lemma to_fun_eq_coe (f : ring_invo R) : f.to_fun = f := rfl

instance has_coe_to_ring_equiv : has_coe (ring_invo R) (R ≃+* Rᵒᵖ) :=
⟨ring_invo.to_ring_equiv⟩

@[norm_cast] lemma coe_ring_equiv (f : ring_invo R) (a : R) :
  (f : R ≃+* Rᵒᵖ) a = f a := rfl

@[simp] lemma map_eq_zero_iff (f : ring_invo R) {x : R} : f x = 0 ↔ x = 0 :=
f.to_ring_equiv.map_eq_zero_iff

end ring_invo

open ring_invo

section comm_ring
variables (R F) [comm_ring R] [comm_ring F]

protected def ring_invo.id : ring_invo R :=
{ involution' := λ r, rfl,
  ..(ring_equiv.to_opposite R) }

instance : inhabited (ring_invo R) := ⟨ring_invo.id _⟩

end comm_ring
