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

namespace ring_equiv

open ring_equiv

variables {R F} [ring R] [ring F] (Hs : R ≃+* F) (x y : R)

lemma bijective : function.bijective Hs :=
Hs.to_equiv.bijective

lemma map_zero_iff {x : R} : Hs x = 0 ↔ x = 0 :=
⟨λ H, Hs.bijective.1 $ H.symm ▸ Hs.map_zero.symm,
λ H, H.symm ▸ Hs.map_zero⟩

end ring_equiv

/-- A ring involution -/
structure ring_invo [ring R] extends R ≃+* opposite R :=
(to_fun_to_fun : ∀ x, (to_fun (to_fun x).unop).unop = x)

open ring_invo

section comm_ring
variables (R F) [comm_ring R] [comm_ring F]

protected def ring_invo.id : ring_invo R :=
{ to_fun_to_fun := λ _, rfl,
  ..(ring_equiv.to_opposite R) }

instance : inhabited (ring_invo R) := ⟨ring_invo.id _⟩

end comm_ring
