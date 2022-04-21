/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.category.Pointed

/-!
# The category of bipointed types

This defines `Bipointed`, the category of bipointed types.

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

instance : has_coe_to_sort Bipointed Type* := ⟨X⟩

attribute [protected] Bipointed.X

/-- Turns a bipointing into a bipointed type. -/
def of {X : Type*} (to_prod : X × X) : Bipointed := ⟨X, to_prod⟩

@[simp] lemma coe_of {X : Type*} (to_prod : X × X) : ↥(of to_prod) = X := rfl

alias of ← prod.Bipointed

instance : inhabited Bipointed := ⟨of ((), ())⟩

/-- Morphisms in `Bipointed`. -/
@[ext] protected structure hom (X Y : Bipointed.{u}) : Type u :=
(to_fun : X → Y)
(map_fst : to_fun X.to_prod.1 = Y.to_prod.1)
(map_snd : to_fun X.to_prod.2 = Y.to_prod.2)

namespace hom

/-- The identity morphism of `X : Bipointed`. -/
@[simps] def id (X : Bipointed) : hom X X := ⟨id, rfl, rfl⟩

instance (X : Bipointed) : inhabited (hom X X) := ⟨id X⟩

/-- Composition of morphisms of `Bipointed`. -/
@[simps] def comp {X Y Z : Bipointed.{u}} (f : hom X Y) (g : hom Y Z) : hom X Z :=
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
{ forget := { obj := Bipointed.X, map := @hom.to_fun },
  forget_faithful := ⟨@hom.ext⟩ }

/-- Swaps the pointed elements of a bipointed type. `prod.swap` as a functor. -/
@[simps] def swap : Bipointed ⥤ Bipointed :=
{ obj := λ X, ⟨X, X.to_prod.swap⟩, map := λ X Y f, ⟨f.to_fun, f.map_snd, f.map_fst⟩ }

/-- The equivalence between `Bipointed` and itself induced by `prod.swap` both ways. -/
@[simps] def swap_equiv : Bipointed ≌ Bipointed :=
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

/-- The functor from `Pointed` to `Bipointed` which bipoints the point. -/
def Pointed_to_Bipointed : Pointed.{u} ⥤ Bipointed :=
{ obj := λ X, ⟨X, X.point, X.point⟩, map := λ X Y f, ⟨f.to_fun, f.map_point, f.map_point⟩ }

/-- The functor from `Pointed` to `Bipointed` which adds a second point. -/
def Pointed_to_Bipointed_fst : Pointed.{u} ⥤ Bipointed :=
{ obj := λ X, ⟨option X, X.point, none⟩,
  map := λ X Y f, ⟨option.map f.to_fun, congr_arg _ f.map_point, rfl⟩,
  map_id' := λ X, Bipointed.hom.ext _ _ option.map_id,
  map_comp' := λ X Y Z f g, Bipointed.hom.ext _ _ (option.map_comp_map  _ _).symm }

/-- The functor from `Pointed` to `Bipointed` which adds a first point. -/
def Pointed_to_Bipointed_snd : Pointed.{u} ⥤ Bipointed :=
{ obj := λ X, ⟨option X, none, X.point⟩,
  map := λ X Y f, ⟨option.map f.to_fun, rfl, congr_arg _ f.map_point⟩,
  map_id' := λ X, Bipointed.hom.ext _ _ option.map_id,
  map_comp' := λ X Y Z f g, Bipointed.hom.ext _ _ (option.map_comp_map  _ _).symm }

@[simp] lemma Pointed_to_Bipointed_fst_comp_swap :
  Pointed_to_Bipointed_fst ⋙ Bipointed.swap = Pointed_to_Bipointed_snd := rfl

@[simp] lemma Pointed_to_Bipointed_snd_comp_swap :
  Pointed_to_Bipointed_snd ⋙ Bipointed.swap = Pointed_to_Bipointed_fst := rfl

/-- `Bipointed_to_Pointed_fst` is inverse to `Pointed_to_Bipointed`. -/
@[simps] def Pointed_to_Bipointed_comp_Bipointed_to_Pointed_fst :
  Pointed_to_Bipointed ⋙ Bipointed_to_Pointed_fst ≅ 𝟭 _ :=
nat_iso.of_components (λ X, { hom := ⟨id, rfl⟩, inv := ⟨id, rfl⟩ }) $ λ X Y f, rfl

/-- `Bipointed_to_Pointed_snd` is inverse to `Pointed_to_Bipointed`. -/
@[simps] def Pointed_to_Bipointed_comp_Bipointed_to_Pointed_snd :
  Pointed_to_Bipointed ⋙ Bipointed_to_Pointed_snd ≅ 𝟭 _ :=
nat_iso.of_components (λ X, { hom := ⟨id, rfl⟩, inv := ⟨id, rfl⟩ }) $ λ X Y f, rfl

/-- The free/forgetful adjunction between `Pointed_to_Bipointed_fst` and `Bipointed_to_Pointed_fst`.
-/
def Pointed_to_Bipointed_fst_Bipointed_to_Pointed_fst_adjunction :
  Pointed_to_Bipointed_fst ⊣ Bipointed_to_Pointed_fst :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, { to_fun := λ f, ⟨f.to_fun ∘ option.some, f.map_fst⟩,
                        inv_fun := λ f, ⟨λ o, o.elim Y.to_prod.2 f.to_fun, f.map_point, rfl⟩,
                        left_inv := λ f, by { ext, cases x, exact f.map_snd.symm, refl },
                        right_inv := λ f, Pointed.hom.ext _ _ rfl },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by { ext, cases x; refl } }

/-- The free/forgetful adjunction between `Pointed_to_Bipointed_snd` and `Bipointed_to_Pointed_snd`.
-/
def Pointed_to_Bipointed_snd_Bipointed_to_Pointed_snd_adjunction :
  Pointed_to_Bipointed_snd ⊣ Bipointed_to_Pointed_snd :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y, { to_fun := λ f, ⟨f.to_fun ∘ option.some, f.map_snd⟩,
                        inv_fun := λ f, ⟨λ o, o.elim Y.to_prod.1 f.to_fun, rfl, f.map_point⟩,
                        left_inv := λ f, by { ext, cases x, exact f.map_fst.symm, refl },
                        right_inv := λ f, Pointed.hom.ext _ _ rfl },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by { ext, cases x; refl } }
