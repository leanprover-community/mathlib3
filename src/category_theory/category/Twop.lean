/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import category_theory.category.Bipointed
import data.two_pointing

/-!
# The category of two-pointed types

This defines `Twop`, the category of two-pointed types.

## References

* [nLab, *coalgebra of the real interval*]
  (https://ncatlab.org/nlab/show/coalgebra+of+the+real+interval)
-/

open category_theory option

universes u
variables {α β : Type*}

/-- The category of two-pointed types. -/
structure Twop : Type.{u+1} :=
(X : Type.{u})
(to_two_pointing : two_pointing X)

namespace Twop

instance : has_coe_to_sort Twop Type* := ⟨X⟩

attribute [protected] Twop.X

/-- Turns a two-pointing into a two-pointed type. -/
def of {X : Type*} (to_two_pointing : two_pointing X) : Twop := ⟨X, to_two_pointing⟩

@[simp] lemma coe_of {X : Type*} (to_two_pointing : two_pointing X) :
  ↥(of to_two_pointing) = X := rfl

alias of ← two_pointing.Twop

instance : inhabited Twop := ⟨of two_pointing.bool⟩

/-- Turns a two-pointed type into a bipointed type, by forgetting that the pointed elements are
distinct. -/
def to_Bipointed (X : Twop) : Bipointed := X.to_two_pointing.to_prod.Bipointed

@[simp] lemma coe_to_Bipointed (X : Twop) : ↥X.to_Bipointed = ↥X := rfl

instance large_category : large_category Twop := induced_category.category to_Bipointed

instance concrete_category : concrete_category Twop :=
induced_category.concrete_category to_Bipointed

instance has_forget_to_Bipointed : has_forget₂ Twop Bipointed :=
induced_category.has_forget₂ to_Bipointed

/-- Swaps the pointed elements of a two-pointed type. `two_pointing.swap` as a functor. -/
@[simps] def swap : Twop ⥤ Twop :=
{ obj := λ X, ⟨X, X.to_two_pointing.swap⟩, map := λ X Y f, ⟨f.to_fun, f.map_snd, f.map_fst⟩ }

/-- The equivalence between `Twop` and itself induced by `prod.swap` both ways. -/
@[simps] def swap_equiv : Twop ≌ Twop :=
equivalence.mk swap swap
  (nat_iso.of_components (λ X, { hom := ⟨id, rfl, rfl⟩, inv := ⟨id, rfl, rfl⟩ }) $ λ X Y f, rfl)
  (nat_iso.of_components (λ X, { hom := ⟨id, rfl, rfl⟩, inv := ⟨id, rfl, rfl⟩ }) $ λ X Y f, rfl)

@[simp] lemma swap_equiv_symm : swap_equiv.symm = swap_equiv := rfl

end Twop

@[simp] lemma Twop_swap_comp_forget_to_Bipointed :
  Twop.swap ⋙ forget₂ Twop Bipointed = forget₂ Twop Bipointed ⋙ Bipointed.swap := rfl

/-- The functor from `Pointed` to `Twop` which adds a second point. -/
@[simps] def Pointed_to_Twop_fst : Pointed.{u} ⥤ Twop :=
{ obj := λ X, ⟨option X, ⟨X.point, none⟩, some_ne_none _⟩,
  map := λ X Y f, ⟨option.map f.to_fun, congr_arg _ f.map_point, rfl⟩,
  map_id' := λ X, Bipointed.hom.ext _ _ option.map_id,
  map_comp' := λ X Y Z f g, Bipointed.hom.ext _ _ (option.map_comp_map  _ _).symm }

/-- The functor from `Pointed` to `Twop` which adds a first point. -/
@[simps] def Pointed_to_Twop_snd : Pointed.{u} ⥤ Twop :=
{ obj := λ X, ⟨option X, ⟨none, X.point⟩, (some_ne_none _).symm⟩,
  map := λ X Y f, ⟨option.map f.to_fun, rfl, congr_arg _ f.map_point⟩,
  map_id' := λ X, Bipointed.hom.ext _ _ option.map_id,
  map_comp' := λ X Y Z f g, Bipointed.hom.ext _ _ (option.map_comp_map  _ _).symm }

@[simp] lemma Pointed_to_Twop_fst_comp_swap :
  Pointed_to_Twop_fst ⋙ Twop.swap = Pointed_to_Twop_snd := rfl

@[simp] lemma Pointed_to_Twop_snd_comp_swap :
  Pointed_to_Twop_snd ⋙ Twop.swap = Pointed_to_Twop_fst := rfl

@[simp] lemma Pointed_to_Twop_fst_comp_forget_to_Bipointed :
  Pointed_to_Twop_fst ⋙ forget₂ Twop Bipointed = Pointed_to_Bipointed_fst := rfl

@[simp] lemma Pointed_to_Twop_snd_comp_forget_to_Bipointed :
  Pointed_to_Twop_snd ⋙ forget₂ Twop Bipointed = Pointed_to_Bipointed_snd := rfl

/-- Adding a second point is left adjoint to forgetting the second point. -/
def Pointed_to_Twop_fst_forget_comp_Bipointed_to_Pointed_fst_adjunction :
  Pointed_to_Twop_fst ⊣ forget₂ Twop Bipointed ⋙ Bipointed_to_Pointed_fst :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, ⟨f.to_fun ∘ option.some, f.map_fst⟩,
    inv_fun := λ f, ⟨λ o, o.elim Y.to_two_pointing.to_prod.2 f.to_fun, f.map_point, rfl⟩,
    left_inv := λ f, by { ext, cases x, exact f.map_snd.symm, refl },
    right_inv := λ f, Pointed.hom.ext _ _ rfl },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by { ext, cases x; refl } }

/-- Adding a first point is left adjoint to forgetting the first point. -/
def Pointed_to_Twop_snd_forget_comp_Bipointed_to_Pointed_snd_adjunction :
  Pointed_to_Twop_snd ⊣ forget₂ Twop Bipointed ⋙ Bipointed_to_Pointed_snd :=
adjunction.mk_of_hom_equiv
{ hom_equiv := λ X Y,
  { to_fun := λ f, ⟨f.to_fun ∘ option.some, f.map_snd⟩,
    inv_fun := λ f, ⟨λ o, o.elim Y.to_two_pointing.to_prod.1 f.to_fun, rfl, f.map_point⟩,
    left_inv := λ f, by { ext, cases x, exact f.map_fst.symm, refl },
    right_inv := λ f, Pointed.hom.ext _ _ rfl },
  hom_equiv_naturality_left_symm' := λ X' X Y f g, by { ext, cases x; refl } }
