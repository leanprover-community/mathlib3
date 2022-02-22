/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Johan Commelin, Reid Barton, Rob Lewis, Joseph Hua
-/
import category_theory.functor_category
import category_theory.concrete_category.reflects_isomorphisms

/-!
# Algebras of endofunctors

This file defines algebras of an endofunctor,
and provides the category instance for them.
This extends to Eilenberg-Moore (co)algebras for a (co)monad.

-/
/-Further it defines the forgetful functor from the category of algebras.

## References
* [Riehl, *Category theory in context*, Section 5.2.4][riehl2017]
-/

universes v₁ u₁

namespace category_theory

variables {C : Type u₁} [category.{v₁} C]

/-- An algebra of an endofunctor; `str` stands for "structure morphism" -/
structure algebra (F : C ⥤ C) :=
(carrier : C)
(str : F.obj carrier ⟶ carrier)

namespace algebra

variables {F : C ⥤ C} (A : algebra F) {A₀ A₁ A₂ : algebra F}

/-- A morphism between algebras of endofunctor `F` -/
@[ext] structure hom (A₀ A₁ : algebra F) :=
(to_hom : A₀.1 ⟶ A₁.1)
(square' : F.map to_hom ≫ A₁.str = A₀.str ≫ to_hom . obviously)

restate_axiom hom.square'
attribute [simp, reassoc] hom.square
namespace hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : hom A A := { to_hom := 𝟙 _ }

instance : inhabited (hom A A) := ⟨{ to_hom := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : hom A₀ A₁) (g : hom A₁ A₂) : hom A₀ A₂ := { to_hom := f.1 ≫ g.1 }

end hom

instance (F : C ⥤ C) : category_struct (algebra F) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ }

@[simp] lemma id_eq_id : algebra.hom.id A = 𝟙 A := rfl

@[simp] lemma id_to_hom : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 := rfl

variables {A₀ A₁ A₂} (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp] lemma comp_eq_comp : algebra.hom.comp f g = f ≫ g := rfl

@[simp] lemma comp_to_hom : (f ≫ g).1 = f.1 ≫ g.1 := rfl

/-- Algebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : category (algebra F) := {}

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the carriers which
commutes with the structure morphisms.
-/
@[simps]
def iso_mk (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom) : A₀ ≅ A₁ :=
{ hom := { to_hom := h.hom },
  inv :=
  { to_hom := h.inv,
    square' := by { rw [h.eq_comp_inv, category.assoc, ←w, ←functor.map_comp_assoc], simp } } }

/-- The forgetful functor from the category of algebras, forgetting the algebraic structure. -/
@[simps] def forget (F : C ⥤ C) : algebra F ⥤ C :=
{ obj := λ A, A.1,
  map := λ A B f, f.1 }

/-- An algebra morphism with an underlying isomorphism hom in `C` is an algebra isomorphism. -/
lemma is_iso_of_is_iso (f : A₀ ⟶ A₁) [is_iso f.1] : is_iso f :=
⟨⟨{ to_hom := inv f.1,
    square' := by { rw [is_iso.eq_comp_inv f.1, category.assoc, ← f.square], simp } }, by tidy⟩⟩

instance forget_reflects_iso : reflects_isomorphisms (forget F) :=
{ reflects := λ A B, is_iso_of_is_iso }

instance forget_faithful : faithful (forget F) := {}

/--
From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
@[simps]
def functor_of_nat_trans {F G : C ⥤ C} (α : G ⟶ F) : algebra F ⥤ algebra G :=
{ obj := λ A,
  { carrier := A.1,
    str := α.app A.1 ≫ A.str },
  map := λ A₀ A₁ f,
  { to_hom := f.1 } }

/-- The identity transformation induces the identity endofunctor on the category of algebras. -/
@[simps {rhs_md := semireducible}]
def functor_of_nat_trans_id :
  functor_of_nat_trans (𝟙 F) ≅ 𝟭 _ :=
nat_iso.of_components
  (λ X, iso_mk (iso.refl _) (by { dsimp, simp, }))
  (λ X Y f, by { ext, dsimp, simp })

/-- A composition of natural transformations gives the composition of corresponding functors. -/
@[simps {rhs_md := semireducible}]
def functor_of_nat_trans_comp {F₀ F₁ F₂ : C ⥤ C} (α : F₀ ⟶ F₁) (β : F₁ ⟶ F₂) :
  functor_of_nat_trans (α ≫ β) ≅
    functor_of_nat_trans β ⋙ functor_of_nat_trans α :=
nat_iso.of_components
  (λ X, iso_mk (iso.refl _) (by { dsimp, simp }))
  (λ X Y f, by { ext, dsimp, simp })

/--
If `α` and `β` are two equal natural transformations, then the functors of algebras induced by them
are isomorphic.
We define it like this as opposed to using `eq_to_iso` so that the components are nicer to prove
lemmas about.
-/
@[simps {rhs_md := semireducible}]
def functor_of_nat_trans_eq {F G : C ⥤ C} {α β : F ⟶ G} (h : α = β) :
  functor_of_nat_trans α ≅ functor_of_nat_trans β :=
nat_iso.of_components
  (λ X, iso_mk (iso.refl _) (by { dsimp, simp [h] }))
  (λ X Y f, by { ext, dsimp, simp })

/--
Naturally isomorphic endofunctors give equivalent categories of algebras.
Furthermore, they are equivalent as categories over `C`, that is,
we have `equiv_of_nat_iso h ⋙ forget = forget`.
-/
@[simps]
def equiv_of_nat_iso {F G : C ⥤ C} (α : F ≅ G) :
  algebra F ≌ algebra G :=
{ functor := functor_of_nat_trans α.inv,
  inverse := functor_of_nat_trans α.hom,
  unit_iso :=
    functor_of_nat_trans_id.symm ≪≫
    functor_of_nat_trans_eq (by simp) ≪≫
    functor_of_nat_trans_comp _ _,
  counit_iso :=
    (functor_of_nat_trans_comp _ _).symm ≪≫
    functor_of_nat_trans_eq (by simp) ≪≫
    functor_of_nat_trans_id }

end algebra

end category_theory
