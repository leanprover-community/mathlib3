/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.epi_mono
import category_theory.limits.shapes.strong_epi
import category_theory.lifting_properties.adjunction

/-!
# Preservation and reflection of monomorphisms and epimorphisms

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We provide typeclasses that state that a functor preserves or reflects monomorphisms or
epimorphisms.
-/

open category_theory

universes v₁ v₂ v₃ u₁ u₂ u₃

namespace category_theory.functor
variables {C : Type u₁} [category.{v₁} C] {D : Type u₂} [category.{v₂} D]
  {E : Type u₃} [category.{v₃} E]

/-- A functor preserves monomorphisms if it maps monomorphisms to monomorphisms. -/
class preserves_monomorphisms (F : C ⥤ D) : Prop :=
(preserves : ∀ {X Y : C} (f : X ⟶ Y) [mono f], mono (F.map f))

instance map_mono (F : C ⥤ D) [preserves_monomorphisms F] {X Y : C} (f : X ⟶ Y) [mono f] :
  mono (F.map f) :=
preserves_monomorphisms.preserves f

/-- A functor preserves epimorphisms if it maps epimorphisms to epimorphisms. -/
class preserves_epimorphisms (F : C ⥤ D) : Prop :=
(preserves : ∀ {X Y : C} (f : X ⟶ Y) [epi f], epi (F.map f))

instance map_epi (F : C ⥤ D) [preserves_epimorphisms F] {X Y : C} (f : X ⟶ Y) [epi f] :
  epi (F.map f) :=
preserves_epimorphisms.preserves f

/-- A functor reflects monomorphisms if morphisms that are mapped to monomorphisms are themselves
    monomorphisms. -/
class reflects_monomorphisms (F : C ⥤ D) : Prop :=
(reflects : ∀ {X Y : C} (f : X ⟶ Y), mono (F.map f) → mono f)

lemma mono_of_mono_map (F : C ⥤ D) [reflects_monomorphisms F] {X Y : C} {f : X ⟶ Y}
  (h : mono (F.map f)) : mono f :=
reflects_monomorphisms.reflects f h

/-- A functor reflects epimorphisms if morphisms that are mapped to epimorphisms are themselves
    epimorphisms. -/
class reflects_epimorphisms (F : C ⥤ D) : Prop :=
(reflects : ∀ {X Y : C} (f : X ⟶ Y), epi (F.map f) → epi f)

lemma epi_of_epi_map (F : C ⥤ D) [reflects_epimorphisms F] {X Y : C} {f : X ⟶ Y}
  (h : epi (F.map f)) : epi f :=
reflects_epimorphisms.reflects f h

instance preserves_monomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [preserves_monomorphisms F]
  [preserves_monomorphisms G] : preserves_monomorphisms (F ⋙ G) :=
{ preserves := λ X Y f h, by { rw comp_map, exactI infer_instance } }

instance preserves_epimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [preserves_epimorphisms F]
  [preserves_epimorphisms G] : preserves_epimorphisms (F ⋙ G) :=
{ preserves := λ X Y f h, by { rw comp_map, exactI infer_instance } }

instance reflects_monomorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [reflects_monomorphisms F]
  [reflects_monomorphisms G] : reflects_monomorphisms (F ⋙ G) :=
{ reflects := λ X Y f h, (F.mono_of_mono_map (G.mono_of_mono_map h)) }

instance reflects_epimorphisms_comp (F : C ⥤ D) (G : D ⥤ E) [reflects_epimorphisms F]
  [reflects_epimorphisms G] : reflects_epimorphisms (F ⋙ G) :=
{ reflects := λ X Y f h, (F.epi_of_epi_map (G.epi_of_epi_map h)) }

lemma preserves_epimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
  [preserves_epimorphisms (F ⋙ G)] [reflects_epimorphisms G] : preserves_epimorphisms F :=
⟨λ X Y f hf, G.epi_of_epi_map $ show epi ((F ⋙ G).map f), by exactI infer_instance⟩

lemma preserves_monomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
  [preserves_monomorphisms (F ⋙ G)] [reflects_monomorphisms G] : preserves_monomorphisms F :=
⟨λ X Y f hf, G.mono_of_mono_map $ show mono ((F ⋙ G).map f), by exactI infer_instance⟩

lemma reflects_epimorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
  [preserves_epimorphisms G] [reflects_epimorphisms (F ⋙ G)] : reflects_epimorphisms F :=
⟨λ X Y f hf, (F ⋙ G).epi_of_epi_map $ show epi (G.map (F.map f)), by exactI infer_instance⟩

lemma reflects_monomorphisms_of_preserves_of_reflects (F : C ⥤ D) (G : D ⥤ E)
  [preserves_monomorphisms G] [reflects_monomorphisms (F ⋙ G)] : reflects_monomorphisms F :=
⟨λ X Y f hf, (F ⋙ G).mono_of_mono_map $ show mono (G.map (F.map f)), by exactI infer_instance⟩

lemma preserves_monomorphisms.of_iso {F G : C ⥤ D} [preserves_monomorphisms F] (α : F ≅ G) :
  preserves_monomorphisms G :=
{ preserves := λ X Y f h,
  begin
    haveI : mono (F.map f ≫ (α.app Y).hom) := by exactI mono_comp _ _,
    convert (mono_comp _ _ : mono ((α.app X).inv ≫ F.map f ≫ (α.app Y).hom)),
    rw [iso.eq_inv_comp, iso.app_hom, iso.app_hom, nat_trans.naturality]
  end }

lemma preserves_monomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
  preserves_monomorphisms F ↔ preserves_monomorphisms G :=
⟨λ h, by exactI preserves_monomorphisms.of_iso α,
 λ h, by exactI preserves_monomorphisms.of_iso α.symm⟩

lemma preserves_epimorphisms.of_iso {F G : C ⥤ D} [preserves_epimorphisms F] (α : F ≅ G) :
  preserves_epimorphisms G :=
{ preserves := λ X Y f h,
  begin
    haveI : epi (F.map f ≫ (α.app Y).hom) := by exactI epi_comp _ _,
    convert (epi_comp _ _ : epi ((α.app X).inv ≫ F.map f ≫ (α.app Y).hom)),
    rw [iso.eq_inv_comp, iso.app_hom, iso.app_hom, nat_trans.naturality]
  end }

lemma preserves_epimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
  preserves_epimorphisms F ↔ preserves_epimorphisms G :=
⟨λ h, by exactI preserves_epimorphisms.of_iso α,
 λ h, by exactI preserves_epimorphisms.of_iso α.symm⟩

lemma reflects_monomorphisms.of_iso {F G : C ⥤ D} [reflects_monomorphisms F] (α : F ≅ G) :
  reflects_monomorphisms G :=
{ reflects := λ X Y f h,
  begin
    apply F.mono_of_mono_map,
    haveI : mono (G.map f ≫ (α.app Y).inv) := by exactI mono_comp _ _,
    convert (mono_comp _ _ : mono ((α.app X).hom ≫ G.map f ≫ (α.app Y).inv)),
    rw [← category.assoc, iso.eq_comp_inv, iso.app_hom, iso.app_hom, nat_trans.naturality]
  end }

lemma reflects_monomorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
  reflects_monomorphisms F ↔ reflects_monomorphisms G :=
⟨λ h, by exactI reflects_monomorphisms.of_iso α,
 λ h, by exactI reflects_monomorphisms.of_iso α.symm⟩

lemma reflects_epimorphisms.of_iso {F G : C ⥤ D} [reflects_epimorphisms F] (α : F ≅ G) :
  reflects_epimorphisms G :=
{ reflects := λ X Y f h,
  begin
    apply F.epi_of_epi_map,
    haveI : epi (G.map f ≫ (α.app Y).inv) := by exactI epi_comp _ _,
    convert (epi_comp _ _ : epi ((α.app X).hom ≫ G.map f ≫ (α.app Y).inv)),
    rw [← category.assoc, iso.eq_comp_inv, iso.app_hom, iso.app_hom, nat_trans.naturality]
  end }

lemma reflects_epimorphisms.iso_iff {F G : C ⥤ D} (α : F ≅ G) :
  reflects_epimorphisms F ↔ reflects_epimorphisms G :=
⟨λ h, by exactI reflects_epimorphisms.of_iso α, λ h, by exactI reflects_epimorphisms.of_iso α.symm⟩

lemma preserves_epimorphsisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
 preserves_epimorphisms F :=
{ preserves := λ X Y f hf,
  ⟨begin
    introsI Z g h H,
    replace H := congr_arg (adj.hom_equiv X Z) H,
    rwa [adj.hom_equiv_naturality_left, adj.hom_equiv_naturality_left, cancel_epi,
      equiv.apply_eq_iff_eq] at H
  end⟩ }

@[priority 100]
instance preserves_epimorphisms_of_is_left_adjoint (F : C ⥤ D) [is_left_adjoint F] :
  preserves_epimorphisms F :=
preserves_epimorphsisms_of_adjunction (adjunction.of_left_adjoint F)

lemma preserves_monomorphisms_of_adjunction {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) :
  preserves_monomorphisms G :=
{ preserves := λ X Y f hf,
  ⟨begin
    introsI Z g h H,
    replace H := congr_arg (adj.hom_equiv Z Y).symm H,
    rwa [adj.hom_equiv_naturality_right_symm, adj.hom_equiv_naturality_right_symm,
      cancel_mono, equiv.apply_eq_iff_eq] at H
  end⟩ }

@[priority 100]
instance preserves_monomorphisms_of_is_right_adjoint (F : C ⥤ D) [is_right_adjoint F] :
  preserves_monomorphisms F :=
preserves_monomorphisms_of_adjunction (adjunction.of_right_adjoint F)

@[priority 100]
instance reflects_monomorphisms_of_faithful (F : C ⥤ D) [faithful F] : reflects_monomorphisms F :=
{ reflects := λ X Y f hf, ⟨λ Z g h hgh, by exactI F.map_injective ((cancel_mono (F.map f)).1
    (by rw [← F.map_comp, hgh, F.map_comp]))⟩ }

@[priority 100]
instance reflects_epimorphisms_of_faithful (F : C ⥤ D) [faithful F] : reflects_epimorphisms F :=
{ reflects := λ X Y f hf, ⟨λ Z g h hgh, by exactI F.map_injective ((cancel_epi (F.map f)).1
    (by rw [← F.map_comp, hgh, F.map_comp]))⟩ }

section

variables (F : C ⥤ D) {X Y : C} (f : X ⟶ Y)

/-- If `F` is a fully faithful functor, split epimorphisms are preserved and reflected by `F`. -/
def split_epi_equiv [full F] [faithful F] : split_epi f ≃ split_epi (F.map f) :=
{ to_fun := λ f, f.map F,
  inv_fun := λ s, begin
    refine ⟨F.preimage s.section_, _⟩,
    apply F.map_injective,
    simp only [map_comp, image_preimage, map_id],
    apply split_epi.id,
  end,
  left_inv := by tidy,
  right_inv := by tidy, }

@[simp]
lemma is_split_epi_iff [full F] [faithful F] : is_split_epi (F.map f) ↔ is_split_epi f :=
begin
  split,
  { intro h, exact is_split_epi.mk' ((split_epi_equiv F f).inv_fun h.exists_split_epi.some), },
  { intro h, exact is_split_epi.mk' ((split_epi_equiv F f).to_fun h.exists_split_epi.some), },
end

/-- If `F` is a fully faithful functor, split monomorphisms are preserved and reflected by `F`. -/
def split_mono_equiv [full F] [faithful F] : split_mono f ≃ split_mono (F.map f) :=
{ to_fun := λ f, f.map F,
  inv_fun := λ s, begin
    refine ⟨F.preimage s.retraction, _⟩,
    apply F.map_injective,
    simp only [map_comp, image_preimage, map_id],
    apply split_mono.id,
  end,
  left_inv := by tidy,
  right_inv := by tidy, }

@[simp]
lemma is_split_mono_iff [full F] [faithful F] : is_split_mono (F.map f) ↔ is_split_mono f :=
begin
  split,
  { intro h, exact is_split_mono.mk' ((split_mono_equiv F f).inv_fun h.exists_split_mono.some), },
  { intro h, exact is_split_mono.mk' ((split_mono_equiv F f).to_fun h.exists_split_mono.some), },
end

@[simp]
lemma epi_map_iff_epi [hF₁ : preserves_epimorphisms F] [hF₂ : reflects_epimorphisms F] :
  epi (F.map f) ↔ epi f :=
begin
  split,
  { exact F.epi_of_epi_map, },
  { introI h,
    exact F.map_epi f, },
end

@[simp]
lemma mono_map_iff_mono [hF₁ : preserves_monomorphisms F] [hF₂ : reflects_monomorphisms F] :
  mono (F.map f) ↔ mono f :=
begin
  split,
  { exact F.mono_of_mono_map, },
  { introI h,
    exact F.map_mono f, },
end

/-- If `F : C ⥤ D` is an equivalence of categories and `C` is a `split_epi_category`,
then `D` also is. -/
def split_epi_category_imp_of_is_equivalence [is_equivalence F] [split_epi_category C] :
  split_epi_category D :=
⟨λ X Y f, begin
  introI,
  rw ← F.inv.is_split_epi_iff f,
  apply is_split_epi_of_epi,
end⟩

end

end category_theory.functor

namespace category_theory.adjunction

variables {C D : Type*} [category C] [category D] {F : C ⥤ D} {F' : D ⥤ C} {A B : C}

lemma strong_epi_map_of_strong_epi (adj : F ⊣ F') (f : A ⟶ B)
  [h₁ : F'.preserves_monomorphisms] [h₂ : F.preserves_epimorphisms] [strong_epi f] :
  strong_epi (F.map f) :=
⟨infer_instance, λ X Y Z, by { introI, rw adj.has_lifting_property_iff, apply_instance, }⟩

instance strong_epi_map_of_is_equivalence [is_equivalence F] (f : A ⟶ B) [h : strong_epi f] :
  strong_epi (F.map f) :=
F.as_equivalence.to_adjunction.strong_epi_map_of_strong_epi f

end category_theory.adjunction

namespace category_theory.functor

variables {C D : Type*} [category C] [category D] {F : C ⥤ D} {A B : C} (f : A ⟶ B)

@[simp]
lemma strong_epi_map_iff_strong_epi_of_is_equivalence [is_equivalence F] :
  strong_epi (F.map f) ↔ strong_epi f  :=
begin
  split,
  { introI,
    have e : arrow.mk f ≅ arrow.mk (F.inv.map (F.map f)) :=
      arrow.iso_of_nat_iso F.as_equivalence.unit_iso (arrow.mk f),
    rw strong_epi.iff_of_arrow_iso e,
    apply_instance, },
  { introI,
    apply_instance, },
end

end category_theory.functor
