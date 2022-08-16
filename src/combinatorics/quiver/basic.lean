/-
Copyright (c) 2021 David Wärn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Wärn, Scott Morrison
-/
import data.opposite

/-!
# Quivers

This module defines quivers. A quiver on a type `V` of vertices assigns to every
pair `a b : V` of vertices a type `a ⟶ b` of arrows from `a` to `b`. This
is a very permissive notion of directed graph.

## Implementation notes

Currently `quiver` is defined with `arrow : V → V → Sort v`.
This is different from the category theory setup,
where we insist that morphisms live in some `Type`.
There's some balance here: it's nice to allow `Prop` to ensure there are no multiple arrows,
but it is also results in error-prone universe signatures when constraints require a `Type`.
-/

open opposite

-- We use the same universe order as in category theory.
-- See note [category_theory universes]
universes v v₁ v₂ u u₁ u₂

/--
A quiver `G` on a type `V` of vertices assigns to every pair `a b : V` of vertices
a type `a ⟶ b` of arrows from `a` to `b`.

For graphs with no repeated edges, one can use `quiver.{0} V`, which ensures
`a ⟶ b : Prop`. For multigraphs, one can use `quiver.{v+1} V`, which ensures
`a ⟶ b : Type v`.

Because `category` will later extend this class, we call the field `hom`.
Except when constructing instances, you should rarely see this, and use the `⟶` notation instead.
-/
class quiver (V : Type u) :=
(hom : V → V → Sort v)

infixr ` ⟶ `:10 := quiver.hom -- type as \h

/--
A morphism of quivers. As we will later have categorical functors extend this structure,
we call it a `prefunctor`.
-/
structure prefunctor (V : Type u₁) [quiver.{v₁} V] (W : Type u₂) [quiver.{v₂} W] :=
(obj [] : V → W)
(map : Π {X Y : V}, (X ⟶ Y) → (obj X ⟶ obj Y))

namespace prefunctor

/--
The identity morphism between quivers.
-/
@[simps]
def id (V : Type*) [quiver V] : prefunctor V V :=
{ obj := id,
  map := λ X Y f, f, }

instance (V : Type*) [quiver V] : inhabited (prefunctor V V) := ⟨id V⟩

/--
Composition of morphisms between quivers.
-/
@[simps]
def comp {U : Type*} [quiver U] {V : Type*} [quiver V] {W : Type*} [quiver W]
  (F : prefunctor U V) (G : prefunctor V W) : prefunctor U W :=
{ obj := λ X, G.obj (F.obj X),
  map := λ X Y f, G.map (F.map f), }

end prefunctor

namespace quiver

/-- `Vᵒᵖ` reverses the direction of all arrows of `V`. -/
instance opposite {V} [quiver V] : quiver Vᵒᵖ :=
⟨λ a b, (unop b) ⟶ (unop a)⟩

/--
The opposite of an arrow in `V`.
-/
def hom.op {V} [quiver V] {X Y : V} (f : X ⟶ Y) : op Y ⟶ op X := f
/--
Given an arrow in `Vᵒᵖ`, we can take the "unopposite" back in `V`.
-/
def hom.unop {V} [quiver V] {X Y : Vᵒᵖ} (f : X ⟶ Y) : unop Y ⟶ unop X := f

attribute [irreducible] quiver.opposite

/-- A type synonym for a quiver with no arrows. -/
@[nolint has_nonempty_instance]
def empty (V) : Type u := V

instance empty_quiver (V : Type u) : quiver.{u} (empty V) := ⟨λ a b, pempty⟩

@[simp] lemma empty_arrow {V : Type u} (a b : empty V) : (a ⟶ b) = pempty := rfl

end quiver
