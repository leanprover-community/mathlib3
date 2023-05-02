/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn
-/
import order.bounded_order
import combinatorics.quiver.basic

/-!
## Wide subquivers

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

A wide subquiver `H` of a quiver `H` consists of a subset of the edge set `a ⟶ b` for
every pair of vertices `a b : V`. We include 'wide' in the name to emphasize that these
subquivers by definition contain all vertices.
-/

universes v u

/-- A wide subquiver `H` of `G` picks out a set `H a b` of arrows from `a` to `b`
    for every pair of vertices `a b`.

    NB: this does not work for `Prop`-valued quivers. It requires `G : quiver.{v+1} V`. -/
def wide_subquiver (V) [quiver.{v+1} V] :=
Π a b : V, set (a ⟶ b)

/-- A type synonym for `V`, when thought of as a quiver having only the arrows from
some `wide_subquiver`. -/
@[nolint unused_arguments has_nonempty_instance]
def wide_subquiver.to_Type (V) [quiver V] (H : wide_subquiver V) : Type u := V

instance wide_subquiver_has_coe_to_sort {V} [quiver V] :
  has_coe_to_sort (wide_subquiver V) (Type u) :=
{ coe := λ H, wide_subquiver.to_Type V H }

/-- A wide subquiver viewed as a quiver on its own. -/
instance wide_subquiver.quiver {V} [quiver V] (H : wide_subquiver V) : quiver H :=
⟨λ a b, { f // f ∈ H a b }⟩

namespace quiver

instance {V} [quiver V] : has_bot (wide_subquiver V) := ⟨λ a b, ∅⟩
instance {V} [quiver V] : has_top (wide_subquiver V) := ⟨λ a b, set.univ⟩
instance {V} [quiver V] : inhabited (wide_subquiver V) := ⟨⊤⟩

/-- `total V` is the type of _all_ arrows of `V`. -/
-- TODO Unify with `category_theory.arrow`? (The fields have been named to match.)
@[ext, nolint has_nonempty_instance]
structure total (V : Type u) [quiver.{v} V] : Sort (max (u+1) v) :=
(left : V)
(right : V)
(hom : left ⟶ right)

/-- A wide subquiver of `G` can equivalently be viewed as a total set of arrows. -/
def wide_subquiver_equiv_set_total {V} [quiver V] :
  wide_subquiver V ≃ set (total V) :=
{ to_fun := λ H, { e | e.hom ∈ H e.left e.right },
  inv_fun := λ S a b, { e | total.mk a b e ∈ S },
  left_inv := λ H, rfl,
  right_inv := by { intro S, ext, cases x, refl } }

/-- An `L`-labelling of a quiver assigns to every arrow an element of `L`. -/
def labelling (V : Type u) [quiver V] (L : Sort*) := Π ⦃a b : V⦄, (a ⟶ b) → L

instance {V : Type u} [quiver V] (L) [inhabited L] : inhabited (labelling V L) :=
⟨λ a b e, default⟩

end quiver
