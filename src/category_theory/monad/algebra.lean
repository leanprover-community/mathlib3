/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monad.basic
import category_theory.adjunction.basic
import category_theory.reflect_isomorphisms

/-!
# Eilenberg-Moore (co)algebras for a (co)monad

This file defines Eilenberg-Moore (co)algebras for a (co)monad, and provides the category instance for them.
Further it defines the adjoint pair of free and forgetful functors, respectively
from and to the original category, as well as the adjoint pair of forgetful and
cofree functors, respectively from and to the original category.

## References
* [Riehl, *Category theory in context*, Section 5.2.4][riehl2017]
-/

namespace category_theory
open category

universes v₁ u₁ -- declare the `v`'s first; see `category_theory.category` for an explanation

variables {C : Type u₁} [category.{v₁} C]

namespace monad

/-- An Eilenberg-Moore algebra for a monad `T`.
    cf Definition 5.2.3 in [Riehl][riehl2017]. -/
structure algebra (T : C ⥤ C) [monad T] : Type (max u₁ v₁) :=
(A : C)
(a : T.obj A ⟶ A)
(unit' : (η_ T).app A ≫ a = 𝟙 A . obviously)
(assoc' : ((μ_ T).app A ≫ a) = (T.map a ≫ a) . obviously)

restate_axiom algebra.unit'
restate_axiom algebra.assoc'

namespace algebra
variables {T : C ⥤ C} [monad T]

/-- A morphism of Eilenberg–Moore algebras for the monad `T`. -/
@[ext] structure hom (A B : algebra T) :=
(f : A.A ⟶ B.A)
(h' : T.map f ≫ B.a = A.a ≫ f . obviously)

restate_axiom hom.h'
attribute [simp] hom.h

namespace hom

/-- The identity homomorphism for an Eilenberg–Moore algebra. -/
@[simps] def id (A : algebra T) : hom A A :=
{ f := 𝟙 A.A }

/-- Composition of Eilenberg–Moore algebra homomorphisms. -/
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

variables (T : C ⥤ C) [monad T]

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the algebraic structure. -/
@[simps] def forget : algebra T ⥤ C :=
{ obj := λ A, A.A,
  map := λ A B f, f.f }

/-- The free functor from the Eilenberg-Moore category, constructing an algebra for any object. -/
@[simps] def free : C ⥤ algebra T :=
{ obj := λ X,
  { A := T.obj X,
    a := (μ_ T).app X,
    assoc' := (monad.assoc _).symm },
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

/-- Given an algebra morphism whose carrier part is an isomorphism, we get an algebra isomorphism. -/
def algebra_iso_of_iso {A B : algebra T} (f : A ⟶ B) [i : is_iso f.f] : is_iso f :=
{ inv :=
  { f := i.inv,
    h' :=
    begin
      erw (as_iso f.f).eq_comp_inv,
      slice_lhs 2 3 {erw ← f.h},
      slice_lhs 1 2 {rw ← T.map_comp},
      rw [is_iso.inv_hom_id, T.map_id, category.id_comp]
    end } }

instance forget_reflects_iso : reflects_isomorphisms (forget T) :=
{ reflects := λ A B, algebra_iso_of_iso T }

end monad

namespace comonad

/-- An Eilenberg-Moore coalgebra for a comonad `T`. -/
@[nolint has_inhabited_instance]
structure coalgebra (G : C ⥤ C) [comonad G] : Type (max u₁ v₁) :=
(A : C)
(a : A ⟶ G.obj A)
(counit' : a ≫ (ε_ G).app A = 𝟙 A . obviously)
(coassoc' : (a ≫ (δ_ G).app A) = (a ≫ G.map a) . obviously)

restate_axiom coalgebra.counit'
restate_axiom coalgebra.coassoc'

namespace coalgebra
variables {G : C ⥤ C} [comonad G]

/-- A morphism of Eilenberg-Moore coalgebras for the comonad `G`. -/
@[ext, nolint has_inhabited_instance] structure hom (A B : coalgebra G) :=
(f : A.A ⟶ B.A)
(h' : A.a ≫ G.map f = f ≫ B.a . obviously)

restate_axiom hom.h'
attribute [simp] hom.h

namespace hom

/-- The identity homomorphism for an Eilenberg–Moore coalgebra. -/
@[simps] def id (A : coalgebra G) : hom A A :=
{ f := 𝟙 A.A }

/-- Composition of Eilenberg–Moore coalgebra homomorphisms. -/
@[simps] def comp {P Q R : coalgebra G} (f : hom P Q) (g : hom Q R) : hom P R :=
{ f := f.f ≫ g.f,
  h' := by rw [functor.map_comp, ← category.assoc, f.h, category.assoc, g.h, category.assoc] }

end hom

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
@[simps] instance EilenbergMoore : category (coalgebra G) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ _ }

end coalgebra

variables (G : C ⥤ C) [comonad G]

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebraic structure. -/
@[simps] def forget : coalgebra G ⥤ C :=
{ obj := λ A, A.A,
  map := λ A B f, f.f }

/-- The cofree functor from the Eilenberg-Moore category, constructing a coalgebra for any object. -/
@[simps] def cofree : C ⥤ coalgebra G :=
{ obj := λ X,
  { A := G.obj X,
    a := (δ_ G).app X,
    coassoc' := (comonad.coassoc _).symm },
  map := λ X Y f,
  { f := G.map f,
    h' := by erw (δ_ G).naturality; refl} }

/--
The adjunction between the cofree and forgetful constructions for Eilenberg-Moore coalgebras
for a comonad.
-/
def adj : forget G ⊣ cofree G :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f,
    { f := X.a ≫ G.map f,
      h' := by { rw [functor.map_comp, ← category.assoc, ← coalgebra.coassoc], simp } },
    inv_fun := λ g, g.f ≫ (ε_ G).app Y,
    left_inv := λ f,
    begin
      dsimp,
      rw [category.assoc, (ε_ G).naturality,
          functor.id_map, ← category.assoc, X.counit, id_comp],
    end,
    right_inv := λ g,
    begin
      ext1, dsimp,
      rw [functor.map_comp, ← category.assoc, coalgebra.hom.h, assoc,
          cofree_obj_a, comonad.right_counit],
      dsimp, simp
    end
    }}

end comonad

end category_theory
