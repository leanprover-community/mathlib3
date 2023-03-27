/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import combinatorics.quiver.subquiver
import combinatorics.quiver.path
import combinatorics.quiver.symmetric
/-!
## Weakly connected components

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.


For a quiver `V`, we define the type `weakly_connected_component V` as the quotient of `V`
by the relation which identifies `a` with `b` if there is a path from `a` to `b` in `symmetrify V`.
(These zigzags can be seen as a proof-relevant analogue of `eqv_gen`.)

Strongly connected components have not yet been defined.
-/
universes u

namespace quiver

variables (V : Type*) [quiver.{u+1} V]

/-- Two vertices are related in the zigzag setoid if there is a
    zigzag of arrows from one to the other. -/
def zigzag_setoid : setoid V :=
⟨λ a b, nonempty (@path (symmetrify V) _ a b),
 λ a, ⟨path.nil⟩,
 λ a b ⟨p⟩, ⟨p.reverse⟩,
 λ a b c ⟨p⟩ ⟨q⟩, ⟨p.comp q⟩⟩

/-- The type of weakly connected components of a directed graph. Two vertices are
    in the same weakly connected component if there is a zigzag of arrows from one
    to the other. -/
def weakly_connected_component : Type* := quotient (zigzag_setoid V)

namespace weakly_connected_component
variable {V}

/-- The weakly connected component corresponding to a vertex. -/
protected def mk : V → weakly_connected_component V := quotient.mk'

instance : has_coe_t V (weakly_connected_component V) := ⟨weakly_connected_component.mk⟩
instance [inhabited V] : inhabited (weakly_connected_component V) := ⟨show V, from default⟩

protected lemma eq (a b : V) :
  (a : weakly_connected_component V) = b ↔ nonempty (@path (symmetrify V) _ a b) :=
quotient.eq'

end weakly_connected_component

variable {V}

/-- A wide subquiver `H` of `G.symmetrify` determines a wide subquiver of `G`, containing an
    an arrow `e` if either `e` or its reversal is in `H`. -/
-- Without the explicit universe level in `quiver.{v+1}` Lean comes up with
-- `quiver.{max u_2 u_3 + 1}`. This causes problems elsewhere, so we write `quiver.{v+1}`.
def wide_subquiver_symmetrify (H : wide_subquiver (symmetrify V)) : wide_subquiver V :=
λ a b, { e | sum.inl e ∈ H a b ∨ sum.inr e ∈ H b a }

end quiver
