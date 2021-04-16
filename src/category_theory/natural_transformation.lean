/-
Copyright (c) 2017 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tim Baumann, Stephen Morgan, Scott Morrison, Floris van Doorn

Defines natural transformations between functors.

Introduces notations
  `τ.app X` for the components of natural transformations,
  `F ⟶ G` for the type of natural transformations between functors `F` and `G`,
  `σ ≫ τ` for vertical compositions, and
  `σ ◫ τ` for horizontal compositions.
-/
import category_theory.functor

namespace category_theory

-- declare the `v`'s first; see `category_theory.category` for an explanation
universes v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]

/--
`nat_trans F G` represents a natural transformation between functors `F` and `G`.

The field `app` provides the components of the natural transformation.

Naturality is expressed by `α.naturality_lemma`.
-/
@[ext]
structure nat_trans (F G : C ⥤ D) : Type (max u₁ v₂) :=
(app : Π X : C, (F.obj X) ⟶ (G.obj X))
(naturality' : ∀ {{X Y : C}} (f : X ⟶ Y), (F.map f) ≫ (app Y) = (app X) ≫ (G.map f) . obviously)

restate_axiom nat_trans.naturality'
-- Rather arbitrarily, we say that the 'simpler' form is
-- components of natural transfomations moving earlier.
attribute [simp, reassoc] nat_trans.naturality

lemma congr_app {F G : C ⥤ D} {α β : nat_trans F G} (h : α = β) (X : C) : α.app X = β.app X :=
congr_fun (congr_arg nat_trans.app h) X

namespace nat_trans

/-- `nat_trans.id F` is the identity natural transformation on a functor `F`. -/
protected def id (F : C ⥤ D) : nat_trans F F :=
{ app := λ X, 𝟙 (F.obj X) }

@[simp] lemma id_app' (F : C ⥤ D) (X : C) : (nat_trans.id F).app X = 𝟙 (F.obj X) := rfl

instance (F : C ⥤ D) : inhabited (nat_trans F F) := ⟨nat_trans.id F⟩

open category
open category_theory.functor

section
variables {F G H I : C ⥤ D}

/-- `vcomp α β` is the vertical compositions of natural transformations. -/
def vcomp (α : nat_trans F G) (β : nat_trans G H) : nat_trans F H :=
{ app := λ X, (α.app X) ≫ (β.app X) }

-- functor_category will rewrite (vcomp α β) to (α ≫ β), so this is not a
-- suitable simp lemma.  We will declare the variant vcomp_app' there.
lemma vcomp_app (α : nat_trans F G) (β : nat_trans G H) (X : C) :
  (vcomp α β).app X = (α.app X) ≫ (β.app X) := rfl

end

/--
The diagram
    F(f)      F(g)      F(h)
F X ----> F Y ----> F U ----> F U
 |         |         |         |
 | α(X)    | α(Y)    | α(U)    | α(V)
 v         v         v         v
G X ----> G Y ----> G U ----> G V
    G(f)      G(g)      G(h)
commutes.
-/
example {F G : C ⥤ D} (α : nat_trans F G) {X Y U V : C} (f : X ⟶ Y) (g : Y ⟶ U) (h : U ⟶ V) :
  α.app X ≫ G.map f ≫ G.map g ≫ G.map h =
    F.map f ≫ F.map g ≫ F.map h ≫ α.app V :=
by simp

end nat_trans

end category_theory
