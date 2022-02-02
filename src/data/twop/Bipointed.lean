/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import data.twop.Pointed

/-!
# The category of bipointed types

This defines `Bipointed` the category of bipointed types.

## TODO

Monoidal structure
-/

open category_theory

universes u
variables {α β : Type*}

/-- The category of bipointed types. -/
structure Bipointed : Type.{u + 1} :=
(X : Type.{u})
(to_prod : X × X)

namespace Bipointed

instance : has_coe_to_sort Bipointed Type* := ⟨Bipointed.X⟩

/-- Turns a bipointing into a bipointed type. -/
def of {X : Type*} (to_prod : X × X) : Bipointed := ⟨X, to_prod⟩

alias of ← prod.Bipointed

instance : inhabited Bipointed := ⟨of ((), ())⟩

/-- Morphisms in `Bipointed`. -/
@[nolint has_inhabited_instance, ext]
protected structure hom (X Y : Bipointed.{u}) : Type u :=
(to_fun : X → Y)
(map_fst : to_fun X.to_prod.1 = Y.to_prod.1)
(map_snd : to_fun X.to_prod.2 = Y.to_prod.2)

namespace hom

/-- The identity morphism of `X : Bipointed`. -/
@[simps] def id (X : Bipointed) : Bipointed.hom X X := ⟨id, rfl, rfl⟩

/-- Composition of morphisms of `Bipointed`. -/
@[simps] def comp {X Y Z : Bipointed.{u}} (f : Bipointed.hom X Y) (g : Bipointed.hom Y Z) :
  Bipointed.hom X Z :=
⟨g.to_fun ∘ f.to_fun, by rw [function.comp_apply, f.map_fst, g.map_fst],
  by rw [function.comp_apply, f.map_snd, g.map_snd]⟩

end hom

instance large_category : large_category Bipointed :=
{ hom := hom,
  id := hom.id,
  comp := @hom.comp,
  id_comp' := λ _ _ _, hom.ext _ _ rfl,
  comp_id' := λ _ _ _, hom.ext _ _ rfl,
  assoc' := λ _ _ _ _ _ _ _, hom.ext _ _ rfl }

instance concrete_category : concrete_category Bipointed :=
{ forget := { obj := Bipointed.X, map := @Bipointed.hom.to_fun },
  forget_faithful := ⟨@hom.ext⟩ }

/-- Swaps the pointed elements of a bipointed type. `prod.swap` as a functor. -/
@[simps] def swap : Bipointed ⥤ Bipointed :=
{ obj := λ X, ⟨X, X.to_prod.swap⟩, map := λ X Y f, ⟨f.to_fun, f.map_snd, f.map_fst⟩ }

/-- The equivalence between `Bipointed` and itself induced by `prod.swap` both ways. -/
def swap_equiv : Bipointed ≌ Bipointed :=
equivalence.mk swap swap
  (nat_iso.of_components (λ X, { hom := ⟨id, rfl, rfl⟩, inv := ⟨id, rfl, rfl⟩ }) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, { hom := ⟨id, rfl, rfl⟩, inv := ⟨id, rfl, rfl⟩ }) $ λ X Y f, rfl)

@[simp] lemma swap_equiv_symm : swap_equiv.symm = swap_equiv := rfl

end Bipointed

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the second point. -/
def Bipointed_to_Pointed_fst : Bipointed ⥤ Pointed :=
{ obj := λ X, ⟨X, X.to_prod.1⟩, map := λ X Y f, ⟨f.to_fun, f.map_fst⟩ }

/-- The forgetful functor from `Bipointed` to `Pointed` which forgets about the first point. -/
def Bipointed_to_Pointed_snd : Bipointed ⥤ Pointed :=
{ obj := λ X, ⟨X, X.to_prod.2⟩, map := λ X Y f, ⟨f.to_fun, f.map_snd⟩ }

@[simp] lemma Bipointed_to_Pointed_fst_comp_forget :
  Bipointed_to_Pointed_fst ⋙ forget Pointed = forget Bipointed := rfl

@[simp] lemma Bipointed_to_Pointed_snd_comp_forget :
  Bipointed_to_Pointed_snd ⋙ forget Pointed = forget Bipointed := rfl

@[simp] lemma swap_comp_Bipointed_to_Pointed_fst :
  Bipointed.swap ⋙ Bipointed_to_Pointed_fst = Bipointed_to_Pointed_snd := rfl

@[simp] lemma swap_comp_Bipointed_to_Pointed_snd :
  Bipointed.swap ⋙ Bipointed_to_Pointed_snd = Bipointed_to_Pointed_fst := rfl
