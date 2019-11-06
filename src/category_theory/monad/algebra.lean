/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.monad.basic
import category_theory.adjunction.basic

/-!
# Eilenberg-Moore algebras for a monad

This file defines Eilenberg-Moore algebras for a monad, and provides the category instance for them.
Further it defines the adjoint pair of free and forgetful functors, respectively
from and to the original category.

## References
* [Riehl, *Category theory in context*, Section 5.2.4][riehl2017]
-/

namespace category_theory
open category

universes v₁ u₁ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [𝒞 : category.{v₁} C]
include 𝒞

namespace monad

/-- An Eilenberg-Moore algebra for a monad `T`.
    cf Definition 5.2.3 in [Riehl][riehl2017]. -/
structure algebra (T : C ⥤ C) [monad.{v₁} T] : Type (max u₁ v₁) :=
(A : C)
(a : T.obj A ⟶ A)
(unit' : (η_ T).app A ≫ a = 𝟙 A . obviously)
(assoc' : ((μ_ T).app A ≫ a) = (T.map a ≫ a) . obviously)

restate_axiom algebra.unit'
restate_axiom algebra.assoc'

namespace algebra
variables {T : C ⥤ C} [monad.{v₁} T]

structure hom (A B : algebra T) :=
(f : A.A ⟶ B.A)
(h' : T.map f ≫ B.a = A.a ≫ f . obviously)

restate_axiom hom.h'
attribute [simp] hom.h

namespace hom
@[extensionality] lemma ext {A B : algebra T} (f g : hom A B) (w : f.f = g.f) : f = g :=
by { cases f, cases g, congr, assumption }

@[simps] def id (A : algebra T) : hom A A :=
{ f := 𝟙 A.A }

@[simps] def comp {P Q R : algebra T} (f : hom P Q) (g : hom Q R) : hom P R :=
{ f := f.f ≫ g.f,
  h' := by rw [functor.map_comp, category.assoc, g.h, ←category.assoc, f.h, category.assoc] }

end hom

/-- The category of Eilenberg-Moore algebras for a monad.
    cf Definition 5.2.4 in [Riehl][riehl2017]. -/
@[simps] instance EilenbergMoore : category (algebra T) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ _ }

end algebra

variables (T : C ⥤ C) [monad.{v₁} T]

@[simps] def forget : algebra T ⥤ C :=
{ obj := λ A, A.A,
  map := λ A B f, f.f }

@[simps] def free : C ⥤ algebra T :=
{ obj := λ X,
  { A := T.obj X,
    a := (μ_ T).app X,
    assoc' := (monad.assoc T _).symm },
  map := λ X Y f,
  { f := T.map f,
    h' := by erw (μ_ T).naturality } }

/-- The adjunction between the free and forgetful constructions for Eilenberg-Moore algebras for a monad.
    cf Lemma 5.2.8 of [Riehl][riehl2017]. -/
def adj : free T ⊣ forget T :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, (η_ T).app X ≫ f.f,
    inv_fun := λ f,
    { f := T.map f ≫ Y.a,
      h' :=
      begin
        dsimp, simp,
        conv { to_rhs, rw [←category.assoc, ←(μ_ T).naturality, category.assoc], erw algebra.assoc },
        refl,
      end },
    left_inv := λ f,
    begin
      ext1, dsimp,
      simp only [free_obj_a, functor.map_comp, algebra.hom.h, category.assoc],
      erw [←category.assoc, monad.right_unit, id_comp],
    end,
    right_inv := λ f,
    begin
      dsimp,
      erw [←category.assoc, ←(η_ T).naturality, functor.id_map,
            category.assoc, Y.unit, comp_id],
    end }}

end monad

end category_theory
