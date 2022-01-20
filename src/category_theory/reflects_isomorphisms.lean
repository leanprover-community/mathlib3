/-
Copyright (c) 2020 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import category_theory.fully_faithful

/-!
# Functors which reflect isomorphisms

A functor `F` reflects isomorphisms if whenever `F.map f` is an isomorphism, `f` was too.

It is formalized as a `Prop` valued typeclass `reflects_isomorphisms F`.

Any fully faithful functor reflects isomorphisms.
-/

open category_theory

namespace category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

variables {C : Type u₁} [category.{v₁} C]

section reflects_iso
variables {D : Type u₂} [category.{v₂} D]
variables {E : Type u₃} [category.{v₃} E]

/--
Define what it means for a functor `F : C ⥤ D` to reflect isomorphisms: for any
morphism `f : A ⟶ B`, if `F.map f` is an isomorphism then `f` is as well.
Note that we do not assume or require that `F` is faithful.
-/
class reflects_isomorphisms (F : C ⥤ D) : Prop :=
(reflects : Π {A B : C} (f : A ⟶ B) [is_iso (F.map f)], is_iso f)

/-- If `F` reflects isos and `F.map f` is an iso, then `f` is an iso. -/
lemma is_iso_of_reflects_iso {A B : C} (f : A ⟶ B) (F : C ⥤ D)
  [is_iso (F.map f)] [reflects_isomorphisms F] :
  is_iso f :=
reflects_isomorphisms.reflects F f

@[priority 100]
instance of_full_and_faithful (F : C ⥤ D) [full F] [faithful F] : reflects_isomorphisms F :=
{ reflects := λ X Y f i, by exactI
  ⟨⟨F.preimage (inv (F.map f)), ⟨F.map_injective (by simp), F.map_injective (by simp)⟩⟩⟩ }

instance (F : C ⥤ D) (G : D ⥤ E) [reflects_isomorphisms F] [reflects_isomorphisms G] :
  reflects_isomorphisms (F ⋙ G) :=
⟨λ _ _ f (hf : is_iso (G.map _)),
  by { resetI, haveI := is_iso_of_reflects_iso (F.map f) G, exact is_iso_of_reflects_iso f F }⟩

end reflects_iso

end category_theory
