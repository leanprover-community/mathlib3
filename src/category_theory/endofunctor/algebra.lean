/-
Copyright (c) 2019 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Bhavik Mehta, Johan Commelin, Reid Barton, Rob Lewis, Joseph Hua
-/
import category_theory.functor_category
import category_theory.concrete_category.reflects_isomorphisms
import category_theory.limits.final

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

namespace endofunctor

variables {C : Type u₁} [category.{v₁} C]

/-- An algebra of an endofunctor; `str` stands for "structure morphism" -/
structure algebra (F : C ⥤ C) :=
(A : C)
(str : F.obj A ⟶ A)

namespace algebra

variables {F : C ⥤ C} (A : algebra F) {A₀ A₁ A₂ : algebra F}

/-
        str
   F A₀ -----> A₀
    |          |
F f |          | f
    V          V
   F A₁ -----> A₁
        str
-/
/-- A morphism between algebras of endofunctor `F` -/
@[ext] structure hom (A₀ A₁ : algebra F) :=
(f : A₀.1 ⟶ A₁.1)
(h' : F.map f ≫ A₁.str = A₀.str ≫ f . obviously)

restate_axiom hom.h'
attribute [simp, reassoc] hom.h
namespace hom

/-- The identity morphism of an algebra of endofunctor `F` -/
def id : hom A A := { f := 𝟙 _ }

instance : inhabited (hom A A) := ⟨{ f := 𝟙 _ }⟩

/-- The composition of morphisms between algebras of endofunctor `F` -/
def comp (f : hom A₀ A₁) (g : hom A₁ A₂) : hom A₀ A₂ := { f := f.1 ≫ g.1 }

end hom

instance (F : C ⥤ C) : category_struct (algebra F) :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp _ _ _ }

@[simp] lemma id_eq_id : algebra.hom.id A = 𝟙 A := rfl

@[simp] lemma id_f : (𝟙 _ : A ⟶ A).1 = 𝟙 A.1 := rfl

variables {A₀ A₁ A₂} (f : A₀ ⟶ A₁) (g : A₁ ⟶ A₂)

@[simp] lemma comp_eq_comp : algebra.hom.comp f g = f ≫ g := rfl

@[simp] lemma comp_f : (f ≫ g).1 = f.1 ≫ g.1 := rfl

/-- Algebras of an endofunctor `F` form a category -/
instance (F : C ⥤ C) : category (algebra F) := {}

/--
To construct an isomorphism of algebras, it suffices to give an isomorphism of the As which
commutes with the structure morphisms.
-/
@[simps]
def iso_mk (h : A₀.1 ≅ A₁.1) (w : F.map h.hom ≫ A₁.str = A₀.str ≫ h.hom) : A₀ ≅ A₁ :=
{ hom := { f := h.hom },
  inv :=
  { f := h.inv,
    h' := by { rw [h.eq_comp_inv, category.assoc, ←w, ←functor.map_comp_assoc], simp } } }

/-- The forgetful functor from the category of algebras, forgetting the algebraic structure. -/
@[simps] def forget (F : C ⥤ C) : algebra F ⥤ C :=
{ obj := λ A, A.1,
  map := λ A B f, f.1 }

/-- An algebra morphism with an underlying isomorphism hom in `C` is an algebra isomorphism. -/
lemma iso_of_iso (f : A₀ ⟶ A₁) [is_iso f.1] : is_iso f :=
⟨⟨{ f := inv f.1,
    h' := by { rw [is_iso.eq_comp_inv f.1, category.assoc, ← f.h], simp } }, by tidy⟩⟩

instance forget_reflects_iso : reflects_isomorphisms (forget F) :=
{ reflects := λ A B, iso_of_iso }

instance forget_faithful : faithful (forget F) := {}

/--
From a natural transformation `α : G → F` we get a functor from
algebras of `F` to algebras of `G`.
-/
@[simps]
def functor_of_nat_trans {F G : C ⥤ C} (α : G ⟶ F) : algebra F ⥤ algebra G :=
{ obj := λ A,
  { A := A.1,
    str := α.app A.1 ≫ A.str },
  map := λ A₀ A₁ f,
  { f := f.1 } }

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
    functor_of_nat_trans_id }.

namespace initial

variables {A} (h : limits.is_initial A)

/-- The inverse of the structure map of an initial algebra -/
@[simp] def str_inv : A.1 ⟶ F.obj A.1 := (h.to ⟨ F.obj A.1 , F.map A.str ⟩).1

lemma left_inv' : (⟨str_inv h ≫ A.str⟩ : A ⟶ A) = 𝟙 A :=
limits.is_initial.hom_ext h _ (𝟙 A)

lemma left_inv : str_inv h ≫ A.str = 𝟙 _ := congr_arg hom.f (left_inv' h)

lemma right_inv : A.str ≫ str_inv h = 𝟙 _ :=
by { rw [str_inv, ← (h.to ⟨ F.obj A.1 , F.map A.str ⟩).h,
  ← F.map_id, ← F.map_comp], congr, exact (left_inv h) }

/--
The structure map of the inital algebra is an isomorphism,
hence endofunctors preserve their initial algebras
-/
lemma str_is_iso (h : limits.is_initial A) : is_iso A.str :=
{ out := ⟨ str_inv h, right_inv _ , left_inv _ ⟩ }

end initial

end algebra

end endofunctor

end category_theory
