/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monad.basic
import category_theory.adjunction.basic
import category_theory.reflects_isomorphisms

/-!
# Eilenberg-Moore (co)algebras for a (co)monad

This file defines Eilenberg-Moore (co)algebras for a (co)monad,
and provides the category instance for them.

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
(assoc' : (μ_ T).app A ≫ a = T.map a ≫ a . obviously)

restate_axiom algebra.unit'
restate_axiom algebra.assoc'
attribute [reassoc] algebra.unit algebra.assoc

namespace algebra
variables {T : C ⥤ C} [monad T]

/-- A morphism of Eilenberg–Moore algebras for the monad `T`. -/
@[ext] structure hom (A B : algebra T) :=
(f : A.A ⟶ B.A)
(h' : T.map f ≫ B.a = A.a ≫ f . obviously)

restate_axiom hom.h'
attribute [simp, reassoc] hom.h

namespace hom

/-- The identity homomorphism for an Eilenberg–Moore algebra. -/
def id (A : algebra T) : hom A A :=
{ f := 𝟙 A.A }

instance (A : algebra T) : inhabited (hom A A) := ⟨{ f := 𝟙 _ }⟩

/-- Composition of Eilenberg–Moore algebra homomorphisms. -/
def comp {P Q R : algebra T} (f : hom P Q) (g : hom Q R) : hom P R :=
{ f := f.f ≫ g.f,
  h' := by rw [functor.map_comp, category.assoc, g.h, f.h_assoc] }

end hom

instance : category_struct (algebra T) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ _ }

@[simp] lemma comp_eq_comp {A A' A'' : algebra T} (f : A ⟶ A') (g : A' ⟶ A'') :
  algebra.hom.comp f g = f ≫ g := rfl
@[simp] lemma id_eq_id (A : algebra T) :
  algebra.hom.id A = 𝟙 A := rfl

@[simp] lemma id_f (A : algebra T) : (𝟙 A : A ⟶ A).f = 𝟙 A.A := rfl
@[simp] lemma comp_f {A A' A'' : algebra T} (f : A ⟶ A') (g : A' ⟶ A'') :
  (f ≫ g).f = f.f ≫ g.f := rfl

/-- The category of Eilenberg-Moore algebras for a monad.
    cf Definition 5.2.4 in [Riehl][riehl2017]. -/
instance EilenbergMoore : category (algebra T) := {}.

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
def iso_mk {A B : algebra T} (h : A.A ≅ B.A) (w : T.map h.hom ≫ B.a = A.a ≫ h.hom) : A ≅ B :=
{ hom := { f := h.hom },
  inv :=
  { f := h.inv,
    h' := by { rw [h.eq_comp_inv, category.assoc, ←w, ←T.map_comp_assoc], simp } } }

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
    h' := (μ_ T).naturality _ } }

instance [inhabited C] : inhabited (algebra T) :=
⟨(free T).obj (default C)⟩

/-- The adjunction between the free and forgetful constructions for Eilenberg-Moore algebras for a monad.
    cf Lemma 5.2.8 of [Riehl][riehl2017]. -/
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
@[simps unit counit {rhs_md := semireducible}]
def adj : free T ⊣ forget T :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, (η_ T).app X ≫ f.f,
    inv_fun := λ f,
    { f := T.map f ≫ Y.a,
      h' :=
      begin
        rw [free_obj_a, functor.map_comp, category.assoc, ←Y.assoc, ←(μ_ T).naturality_assoc],
        refl
      end },
    left_inv := λ f, by { ext, simp },
    right_inv := λ f,
    begin
      dsimp only [forget_obj],
      rw [←(η_ T).naturality_assoc, Y.unit],
      apply category.comp_id,
    end }}

/--
Given an algebra morphism whose carrier part is an isomorphism, we get an algebra isomorphism.
-/
def algebra_iso_of_iso {A B : algebra T} (f : A ⟶ B) [is_iso f.f] : is_iso f :=
{ inv :=
  { f := inv f.f,
    h' := by { rw [is_iso.eq_comp_inv f.f, category.assoc, ← f.h], simp } } }

instance forget_reflects_iso : reflects_isomorphisms (forget T) :=
{ reflects := λ A B, algebra_iso_of_iso T }

instance forget_faithful : faithful (forget T) := {}

end monad

namespace comonad

/-- An Eilenberg-Moore coalgebra for a comonad `T`. -/
@[nolint has_inhabited_instance]
structure coalgebra (G : C ⥤ C) [comonad G] : Type (max u₁ v₁) :=
(A : C)
(a : A ⟶ G.obj A)
(counit' : a ≫ (ε_ G).app A = 𝟙 A . obviously)
(coassoc' : a ≫ (δ_ G).app A = a ≫ G.map a . obviously)

restate_axiom coalgebra.counit'
restate_axiom coalgebra.coassoc'
attribute [reassoc] coalgebra.counit coalgebra.coassoc

namespace coalgebra
variables {G : C ⥤ C} [comonad G]

/-- A morphism of Eilenberg-Moore coalgebras for the comonad `G`. -/
@[ext, nolint has_inhabited_instance] structure hom (A B : coalgebra G) :=
(f : A.A ⟶ B.A)
(h' : A.a ≫ G.map f = f ≫ B.a . obviously)

restate_axiom hom.h'
attribute [simp, reassoc] hom.h

namespace hom

/-- The identity homomorphism for an Eilenberg–Moore coalgebra. -/
def id (A : coalgebra G) : hom A A :=
{ f := 𝟙 A.A }

/-- Composition of Eilenberg–Moore coalgebra homomorphisms. -/
def comp {P Q R : coalgebra G} (f : hom P Q) (g : hom Q R) : hom P R :=
{ f := f.f ≫ g.f,
  h' := by rw [functor.map_comp, f.h_assoc, g.h, category.assoc] }

end hom

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
instance : category_struct (coalgebra G) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ _ }

@[simp] lemma comp_eq_comp {A A' A'' : coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') :
  coalgebra.hom.comp f g = f ≫ g := rfl
@[simp] lemma id_eq_id (A : coalgebra G) :
  coalgebra.hom.id A = 𝟙 A := rfl

@[simp] lemma id_f (A : coalgebra G) : (𝟙 A : A ⟶ A).f = 𝟙 A.A := rfl
@[simp] lemma comp_f {A A' A'' : coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') :
  (f ≫ g).f = f.f ≫ g.f := rfl

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
instance EilenbergMoore : category (coalgebra G) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ _ }

/--
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
def iso_mk {A B : coalgebra G} (h : A.A ≅ B.A) (w : A.a ≫ G.map h.hom = h.hom ≫ B.a) : A ≅ B :=
{ hom := { f := h.hom },
  inv :=
  { f := h.inv,
    h' := by { rw [h.eq_inv_comp, ←reassoc_of w, ←G.map_comp], simp } } }

end coalgebra

variables (G : C ⥤ C) [comonad G]

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebraic structure. -/
@[simps] def forget : coalgebra G ⥤ C :=
{ obj := λ A, A.A,
  map := λ A B f, f.f }

/--
Given a coalgebra morphism whose carrier part is an isomorphism, we get a coalgebra isomorphism.
-/
def coalgebra_iso_of_iso {A B : coalgebra G} (f : A ⟶ B) [is_iso f.f] : is_iso f :=
{ inv :=
  { f := inv f.f,
    h' := by { rw [is_iso.eq_inv_comp f.f, ←f.h_assoc, ←G.map_comp], simp } } }

instance forget_reflects_iso : reflects_isomorphisms (forget G) :=
{ reflects := λ A B, coalgebra_iso_of_iso G }

/-- The cofree functor from the Eilenberg-Moore category, constructing a coalgebra for any object. -/
@[simps] def cofree : C ⥤ coalgebra G :=
{ obj := λ X,
  { A := G.obj X,
    a := (δ_ G).app X,
    coassoc' := (comonad.coassoc _).symm },
  map := λ X Y f,
  { f := G.map f,
    h' := ((δ_ G).naturality _).symm } }

/--
The adjunction between the cofree and forgetful constructions for Eilenberg-Moore coalgebras
for a comonad.
-/
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
@[simps unit counit]
def adj : forget G ⊣ cofree G :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f,
    { f := X.a ≫ G.map f,
      h' := by { rw [functor.map_comp, ← coalgebra.coassoc_assoc], simp } },
    inv_fun := λ g, g.f ≫ (ε_ G).app Y,
    left_inv := λ f,
      by { dsimp, rw [category.assoc, (ε_ G).naturality, functor.id_map, X.counit_assoc] },
    right_inv := λ g,
    begin
      ext1, dsimp,
      rw [functor.map_comp, g.h_assoc, cofree_obj_a, comonad.right_counit],
      apply comp_id,
    end }}

instance forget_faithful : faithful (forget G) := {}

end comonad

end category_theory
