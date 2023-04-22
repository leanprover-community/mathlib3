/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta
-/
import category_theory.monad.basic
import category_theory.adjunction.basic
import category_theory.functor.epi_mono

/-!
# Eilenberg-Moore (co)algebras for a (co)monad

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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

universes v₁ u₁ -- morphism levels before object levels. See note [category_theory universes].

variables {C : Type u₁} [category.{v₁} C]

namespace monad

/-- An Eilenberg-Moore algebra for a monad `T`.
    cf Definition 5.2.3 in [Riehl][riehl2017]. -/
structure algebra (T : monad C) : Type (max u₁ v₁) :=
(A : C)
(a : (T : C ⥤ C).obj A ⟶ A)
(unit' : T.η.app A ≫ a = 𝟙 A . obviously)
(assoc' : T.μ.app A ≫ a = (T : C ⥤ C).map a ≫ a . obviously)

restate_axiom algebra.unit'
restate_axiom algebra.assoc'
attribute [reassoc] algebra.unit algebra.assoc

namespace algebra
variables {T : monad C}

/-- A morphism of Eilenberg–Moore algebras for the monad `T`. -/
@[ext] structure hom (A B : algebra T) :=
(f : A.A ⟶ B.A)
(h' : (T : C ⥤ C).map f ≫ B.a = A.a ≫ f . obviously)

restate_axiom hom.h'
attribute [simp, reassoc] hom.h

namespace hom

/-- The identity homomorphism for an Eilenberg–Moore algebra. -/
def id (A : algebra T) : hom A A :=
{ f := 𝟙 A.A }

instance (A : algebra T) : inhabited (hom A A) := ⟨{ f := 𝟙 _ }⟩

/-- Composition of Eilenberg–Moore algebra homomorphisms. -/
def comp {P Q R : algebra T} (f : hom P Q) (g : hom Q R) : hom P R :=
{ f := f.f ≫ g.f }

end hom

instance : category_struct (algebra T) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ }

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
def iso_mk {A B : algebra T} (h : A.A ≅ B.A) (w : (T : C ⥤ C).map h.hom ≫ B.a = A.a ≫ h.hom) :
  A ≅ B :=
{ hom := { f := h.hom },
  inv :=
  { f := h.inv,
    h' := by { rw [h.eq_comp_inv, category.assoc, ←w, ←functor.map_comp_assoc], simp } } }

end algebra

variables (T : monad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the algebraic structure. -/
@[simps] def forget : algebra T ⥤ C :=
{ obj := λ A, A.A,
  map := λ A B f, f.f }

/-- The free functor from the Eilenberg-Moore category, constructing an algebra for any object. -/
@[simps] def free : C ⥤ algebra T :=
{ obj := λ X,
  { A := T.obj X,
    a := T.μ.app X,
    assoc' := (T.assoc _).symm },
  map := λ X Y f,
  { f := T.map f,
    h' := T.μ.naturality _ } }

instance [inhabited C] : inhabited (algebra T) :=
⟨(free T).obj default⟩

/-- The adjunction between the free and forgetful constructions for Eilenberg-Moore algebras for
  a monad. cf Lemma 5.2.8 of [Riehl][riehl2017]. -/
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
@[simps unit counit]
def adj : T.free ⊣ T.forget :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, T.η.app X ≫ f.f,
    inv_fun := λ f,
    { f := T.map f ≫ Y.a,
      h' := by { dsimp, simp [←Y.assoc, ←T.μ.naturality_assoc] } },
    left_inv := λ f, by { ext, dsimp, simp },
    right_inv := λ f,
    begin
      dsimp only [forget_obj, monad_to_functor_eq_coe],
      rw [←T.η.naturality_assoc, Y.unit],
      apply category.comp_id,
    end }}

/--
Given an algebra morphism whose carrier part is an isomorphism, we get an algebra isomorphism.
-/
lemma algebra_iso_of_iso {A B : algebra T} (f : A ⟶ B) [is_iso f.f] : is_iso f :=
⟨⟨{ f := inv f.f,
    h' := by { rw [is_iso.eq_comp_inv f.f, category.assoc, ← f.h], simp } }, by tidy⟩⟩

instance forget_reflects_iso : reflects_isomorphisms T.forget :=
{ reflects := λ A B, algebra_iso_of_iso T }

instance forget_faithful : faithful T.forget := {}

/-- Given an algebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/
lemma algebra_epi_of_epi {X Y : algebra T} (f : X ⟶ Y) [h : epi f.f] : epi f :=
(forget T).epi_of_epi_map h

/-- Given an algebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/
lemma algebra_mono_of_mono {X Y : algebra T} (f : X ⟶ Y) [h : mono f.f] : mono f :=
(forget T).mono_of_mono_map h

instance : is_right_adjoint T.forget := ⟨T.free, T.adj⟩
@[simp] lemma left_adjoint_forget : left_adjoint T.forget = T.free := rfl
@[simp] lemma of_right_adjoint_forget : adjunction.of_right_adjoint T.forget = T.adj := rfl

/--
Given a monad morphism from `T₂` to `T₁`, we get a functor from the algebras of `T₁` to algebras of
`T₂`.
-/
@[simps]
def algebra_functor_of_monad_hom {T₁ T₂ : monad C} (h : T₂ ⟶ T₁) :
  algebra T₁ ⥤ algebra T₂ :=
{ obj := λ A,
  { A := A.A,
    a := h.app A.A ≫ A.a,
    unit' := by { dsimp, simp [A.unit] },
    assoc' := by { dsimp, simp [A.assoc] } },
  map := λ A₁ A₂ f,
  { f := f.f } }

/--
The identity monad morphism induces the identity functor from the category of algebras to itself.
-/
@[simps {rhs_md := semireducible}]
def algebra_functor_of_monad_hom_id {T₁ : monad C} :
  algebra_functor_of_monad_hom (𝟙 T₁) ≅ 𝟭 _ :=
nat_iso.of_components
  (λ X, algebra.iso_mk (iso.refl _) (by { dsimp, simp, }))
  (λ X Y f, by { ext, dsimp, simp })

/--
A composition of monad morphisms gives the composition of corresponding functors.
-/
@[simps {rhs_md := semireducible}]
def algebra_functor_of_monad_hom_comp {T₁ T₂ T₃ : monad C} (f : T₁ ⟶ T₂) (g : T₂ ⟶ T₃) :
  algebra_functor_of_monad_hom (f ≫ g) ≅
    algebra_functor_of_monad_hom g ⋙ algebra_functor_of_monad_hom f :=
nat_iso.of_components
  (λ X, algebra.iso_mk (iso.refl _) (by { dsimp, simp }))
  (λ X Y f, by { ext, dsimp, simp })

/--
If `f` and `g` are two equal morphisms of monads, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps {rhs_md := semireducible}]
def algebra_functor_of_monad_hom_eq {T₁ T₂ : monad C} {f g : T₁ ⟶ T₂} (h : f = g) :
  algebra_functor_of_monad_hom f ≅ algebra_functor_of_monad_hom g :=
nat_iso.of_components
  (λ X, algebra.iso_mk (iso.refl _) (by { dsimp, simp [h] }))
  (λ X Y f, by { ext, dsimp, simp })

/--
Isomorphic monads give equivalent categories of algebras. Furthermore, they are equivalent as
categories over `C`, that is, we have `algebra_equiv_of_iso_monads h ⋙ forget = forget`.
-/
@[simps]
def algebra_equiv_of_iso_monads {T₁ T₂ : monad C} (h : T₁ ≅ T₂) :
  algebra T₁ ≌ algebra T₂ :=
{ functor := algebra_functor_of_monad_hom h.inv,
  inverse := algebra_functor_of_monad_hom h.hom,
  unit_iso :=
    algebra_functor_of_monad_hom_id.symm ≪≫
    algebra_functor_of_monad_hom_eq (by simp) ≪≫
    algebra_functor_of_monad_hom_comp _ _,
  counit_iso :=
    (algebra_functor_of_monad_hom_comp _ _).symm ≪≫
    algebra_functor_of_monad_hom_eq (by simp) ≪≫
    algebra_functor_of_monad_hom_id }

@[simp] lemma algebra_equiv_of_iso_monads_comp_forget {T₁ T₂ : monad C} (h : T₁ ⟶ T₂) :
  algebra_functor_of_monad_hom h ⋙ forget _ = forget _ :=
rfl

end monad

namespace comonad

/-- An Eilenberg-Moore coalgebra for a comonad `T`. -/
@[nolint has_nonempty_instance]
structure coalgebra (G : comonad C) : Type (max u₁ v₁) :=
(A : C)
(a : A ⟶ (G : C ⥤ C).obj A)
(counit' : a ≫ G.ε.app A = 𝟙 A . obviously)
(coassoc' : a ≫ G.δ.app A = a ≫ G.map a . obviously)

restate_axiom coalgebra.counit'
restate_axiom coalgebra.coassoc'
attribute [reassoc] coalgebra.counit coalgebra.coassoc

namespace coalgebra
variables {G : comonad C}

/-- A morphism of Eilenberg-Moore coalgebras for the comonad `G`. -/
@[ext, nolint has_nonempty_instance] structure hom (A B : coalgebra G) :=
(f : A.A ⟶ B.A)
(h' : A.a ≫ (G : C ⥤ C).map f = f ≫ B.a . obviously)

restate_axiom hom.h'
attribute [simp, reassoc] hom.h

namespace hom

/-- The identity homomorphism for an Eilenberg–Moore coalgebra. -/
def id (A : coalgebra G) : hom A A :=
{ f := 𝟙 A.A }

/-- Composition of Eilenberg–Moore coalgebra homomorphisms. -/
def comp {P Q R : coalgebra G} (f : hom P Q) (g : hom Q R) : hom P R :=
{ f := f.f ≫ g.f }

end hom

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
instance : category_struct (coalgebra G) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ }

@[simp] lemma comp_eq_comp {A A' A'' : coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') :
  coalgebra.hom.comp f g = f ≫ g := rfl
@[simp] lemma id_eq_id (A : coalgebra G) :
  coalgebra.hom.id A = 𝟙 A := rfl

@[simp] lemma id_f (A : coalgebra G) : (𝟙 A : A ⟶ A).f = 𝟙 A.A := rfl
@[simp] lemma comp_f {A A' A'' : coalgebra G} (f : A ⟶ A') (g : A' ⟶ A'') :
  (f ≫ g).f = f.f ≫ g.f := rfl

/-- The category of Eilenberg-Moore coalgebras for a comonad. -/
instance EilenbergMoore : category (coalgebra G) := {}.

/--
To construct an isomorphism of coalgebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
def iso_mk {A B : coalgebra G} (h : A.A ≅ B.A) (w : A.a ≫ (G : C ⥤ C).map h.hom = h.hom ≫ B.a) :
  A ≅ B :=
{ hom := { f := h.hom },
  inv :=
  { f := h.inv,
    h' := by { rw [h.eq_inv_comp, ←reassoc_of w, ←functor.map_comp], simp } } }

end coalgebra

variables (G : comonad C)

/-- The forgetful functor from the Eilenberg-Moore category, forgetting the coalgebraic
structure. -/
@[simps] def forget : coalgebra G ⥤ C :=
{ obj := λ A, A.A,
  map := λ A B f, f.f }

/-- The cofree functor from the Eilenberg-Moore category, constructing a coalgebra for any
object. -/
@[simps] def cofree : C ⥤ coalgebra G :=
{ obj := λ X,
  { A := G.obj X,
    a := G.δ.app X,
    coassoc' := (G.coassoc _).symm },
  map := λ X Y f,
  { f := G.map f,
    h' := (G.δ.naturality _).symm } }

/--
The adjunction between the cofree and forgetful constructions for Eilenberg-Moore coalgebras
for a comonad.
-/
-- The other two `simps` projection lemmas can be derived from these two, so `simp_nf` complains if
-- those are added too
@[simps unit counit]
def adj : G.forget ⊣ G.cofree :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f,
    { f := X.a ≫ G.map f,
      h' := by { dsimp, simp [←coalgebra.coassoc_assoc] } },
    inv_fun := λ g, g.f ≫ G.ε.app Y,
    left_inv := λ f,
      by { dsimp, rw [category.assoc, G.ε.naturality, functor.id_map, X.counit_assoc] },
    right_inv := λ g,
    begin
      ext1, dsimp,
      rw [functor.map_comp, g.h_assoc, cofree_obj_a, comonad.right_counit],
      apply comp_id,
    end }}

/--
Given a coalgebra morphism whose carrier part is an isomorphism, we get a coalgebra isomorphism.
-/
lemma coalgebra_iso_of_iso {A B : coalgebra G} (f : A ⟶ B) [is_iso f.f] : is_iso f :=
⟨⟨{ f := inv f.f,
    h' := by { rw [is_iso.eq_inv_comp f.f, ←f.h_assoc], simp } }, by tidy⟩⟩

instance forget_reflects_iso : reflects_isomorphisms G.forget :=
{ reflects := λ A B, coalgebra_iso_of_iso G }

instance forget_faithful : faithful (forget G) := {}

/-- Given a coalgebra morphism whose carrier part is an epimorphism, we get an algebra epimorphism.
-/
lemma algebra_epi_of_epi {X Y : coalgebra G} (f : X ⟶ Y) [h : epi f.f] : epi f :=
(forget G).epi_of_epi_map h

/-- Given a coalgebra morphism whose carrier part is a monomorphism, we get an algebra monomorphism.
-/
lemma algebra_mono_of_mono {X Y : coalgebra G} (f : X ⟶ Y) [h : mono f.f] : mono f :=
(forget G).mono_of_mono_map h

instance : is_left_adjoint G.forget := ⟨_, G.adj⟩
@[simp] lemma right_adjoint_forget : right_adjoint G.forget = G.cofree := rfl
@[simp] lemma of_left_adjoint_forget : adjunction.of_left_adjoint G.forget = G.adj := rfl

end comonad

end category_theory
