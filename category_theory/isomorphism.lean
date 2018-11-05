-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.functor

universes u v

namespace category_theory

structure iso {C : Type u} [category.{u v} C] (X Y : C) :=
(hom : X ⟶ Y)
(inv : Y ⟶ X)
(hom_inv_id' : hom ≫ inv = 𝟙 X . obviously)
(inv_hom_id' : inv ≫ hom = 𝟙 Y . obviously)

-- We restate the hom_inv_id' and inv_hom_id' lemmas below.

infixr ` ≅ `:10  := iso             -- type as \cong or \iso

variables {C : Type u} [𝒞 : category.{u v} C]
include 𝒞
variables {X Y Z : C}

namespace iso

instance : has_coe (iso.{u v} X Y) (X ⟶ Y) :=
{ coe := iso.hom }

@[extensionality] lemma ext
  (α β : X ≅ Y)
  (w : α.hom = β.hom) : α = β :=
  begin
    induction α with f g wα1 wα2,
    induction β with h k wβ1 wβ2,
    dsimp at *,
    have p : g = k,
      begin
        induction w,
        rw [← category.id_comp C k, ←wα2, category.assoc, wβ1, category.comp_id]
      end,
    induction p, induction w,
    refl
  end

@[symm] def symm (I : X ≅ Y) : Y ≅ X :=
{ hom := I.inv,
  inv := I.hom,
  hom_inv_id' := I.inv_hom_id',
  inv_hom_id' := I.hom_inv_id' }

-- These are the restated lemmas for iso.hom_inv_id' and iso.inv_hom_id'
@[simp] lemma hom_inv_id (α : X ≅ Y) : (α : X ⟶ Y) ≫ (α.symm : Y ⟶ X) = 𝟙 X :=
begin unfold_coes, unfold symm, have p := α.hom_inv_id', dsimp at p, rw p end
@[simp] lemma inv_hom_id (α : X ≅ Y) : (α.symm : Y ⟶ X) ≫ (α : X ⟶ Y) = 𝟙 Y :=
begin unfold_coes, unfold symm, have p := iso.inv_hom_id', dsimp at p, rw p end

-- We rewrite the projections `.hom` and `.inv` into coercions.
@[simp] lemma hom_eq_coe (α : X ≅ Y) : α.hom = (α : X ⟶ Y) := rfl
@[simp] lemma inv_eq_coe (α : X ≅ Y) : α.inv = (α.symm : Y ⟶ X) := rfl

@[refl] def refl (X : C) : X ≅ X :=
{ hom := 𝟙 X,
  inv := 𝟙 X }

@[simp] lemma refl_coe (X : C) : ((iso.refl X) : X ⟶ X) = 𝟙 X := rfl
@[simp] lemma refl_symm_coe  (X : C) : ((iso.refl X).symm : X ⟶ X)  = 𝟙 X := rfl

@[trans] def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z :=
{ hom := (α : X ⟶ Y) ≫ (β : Y ⟶ Z),
  inv := (β.symm : Z ⟶ Y) ≫ (α.symm : Y ⟶ X),
  hom_inv_id' := begin /- `obviously'` says: -/ erw [category.assoc], conv { to_lhs, congr, skip, rw ← category.assoc }, rw iso.hom_inv_id, rw category.id_comp, rw iso.hom_inv_id end,
  inv_hom_id' := begin /- `obviously'` says: -/ erw [category.assoc], conv { to_lhs, congr, skip, rw ← category.assoc }, rw iso.inv_hom_id, rw category.id_comp, rw iso.inv_hom_id end }

infixr ` ≪≫ `:80 := iso.trans -- type as `\ll \gg`.

@[simp] lemma trans_coe (α : X ≅ Y) (β : Y ≅ Z) : ((α ≪≫ β) : X ⟶ Z) = (α : X ⟶ Y) ≫ (β : Y ⟶ Z) := rfl
@[simp] lemma trans_symm_coe (α : X ≅ Y) (β : Y ≅ Z) : ((α ≪≫ β).symm : Z ⟶ X)  = (β.symm : Z ⟶ Y) ≫ (α.symm : Y ⟶ X) := rfl

@[simp] lemma refl_symm (X : C) : ((iso.refl X).symm : X ⟶ X)  = 𝟙 X := rfl
@[simp] lemma trans_symm (α : X ≅ Y) (β : Y ≅ Z) : ((α ≪≫ β).symm : Z ⟶ X) = (β.symm : Z ⟶ Y) ≫ (α.symm : Y ⟶ X) := rfl

end iso

/-- `is_iso` typeclass expressing that a morphism is invertible.
    This contains the data of the inverse, but is a subsingleton type. -/
class is_iso (f : X ⟶ Y) :=
(inv : Y ⟶ X)
(hom_inv_id' : f ≫ inv = 𝟙 X . obviously)
(inv_hom_id' : inv ≫ f = 𝟙 Y . obviously)

def inv (f : X ⟶ Y) [is_iso f] := is_iso.inv f

namespace is_iso

instance (f : X ⟶ Y) : subsingleton (is_iso f) :=
⟨ λ a b, begin
          cases a, cases b,
          dsimp at *, congr,
          rw [← category.id_comp _ a_inv, ← b_inv_hom_id', category.assoc, a_hom_inv_id', category.comp_id]
         end ⟩

@[simp] def hom_inv_id (f : X ⟶ Y) [is_iso f] : f ≫ category_theory.inv f = 𝟙 X :=
is_iso.hom_inv_id' f
@[simp] def inv_hom_id (f : X ⟶ Y) [is_iso f] : category_theory.inv f ≫ f = 𝟙 Y :=
is_iso.inv_hom_id' f

instance (X : C) : is_iso (𝟙 X) :=
{ inv := 𝟙 X }

instance of_iso         (f : X ≅ Y) : is_iso (f : X ⟶ Y) :=
{ inv := (f.symm : Y ⟶ X) }
instance of_iso_inverse (f : X ≅ Y) : is_iso (f.symm : Y ⟶ X)  :=
{ inv := (f : X ⟶ Y) }

end is_iso

namespace functor

universes u₁ v₁ u₂ v₂
variables {D : Type u₂}

variables [𝒟 : category.{u₂ v₂} D]
include 𝒟

def on_iso (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : (F X) ≅ (F Y) :=
{ hom := F.map i.hom,
  inv := F.map i.inv,
  hom_inv_id' := by erw [←map_comp, iso.hom_inv_id, ←map_id],
  inv_hom_id' := by erw [←map_comp, iso.inv_hom_id, ←map_id] }

@[simp] lemma on_iso_hom (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : ((F.on_iso i) : F X ⟶ F Y) = F.map (i : X ⟶ Y) := rfl
@[simp] lemma on_iso_inv (F : C ⥤ D) {X Y : C} (i : X ≅ Y) : ((F.on_iso i).symm : F Y ⟶ F X) = F.map (i.symm : Y ⟶ X) := rfl

instance (F : C ⥤ D) (f : X ⟶ Y) [is_iso f] : is_iso (F.map f) :=
{ inv := F.map (inv f),
  hom_inv_id' := begin rw ← F.map_comp, erw is_iso.hom_inv_id, rw map_id, end,
  inv_hom_id' := begin rw ← F.map_comp, erw is_iso.inv_hom_id, rw map_id, end }

end functor

instance epi_of_iso  (f : X ⟶ Y) [is_iso f] : epi f  :=
{ left_cancellation := begin
                         -- This is an interesting test case for better rewrite automation.
                         intros,
                         rw [←category.id_comp C g, ←category.id_comp C h],
                         rw [← is_iso.inv_hom_id f],
                         erw [category.assoc, w, category.assoc],
                       end }
instance mono_of_iso (f : X ⟶ Y) [is_iso f] : mono f :=
{ right_cancellation := begin
                         intros,
                         rw [←category.comp_id C g, ←category.comp_id C h],
                         rw [← is_iso.hom_inv_id f],
                         erw [←category.assoc, w, ←category.assoc]
                       end }

def eq_to_iso {X Y : C} (p : X = Y) : X ≅ Y := by rw p

@[simp] lemma eq_to_iso_refl (X : C) (p : X = X) : eq_to_iso p = (iso.refl X) := rfl

@[simp] lemma eq_to_iso_trans {X Y Z : C} (p : X = Y) (q : Y = Z) : (eq_to_iso p) ≪≫ (eq_to_iso q) = eq_to_iso (p.trans q) :=
begin /- obviously' says: -/ ext, induction q, induction p, dsimp at *, simp at * end

namespace functor

universes u₁ v₁ u₂ v₂

variables {D : Type u₂} [𝒟 : category.{u₂ v₂} D]
include 𝒟

@[simp] lemma eq_to_iso (F : C ⥤ D) {X Y : C} (p : X = Y) : F.on_iso (eq_to_iso p) = eq_to_iso (congr_arg F.obj p) :=
begin /- obviously says: -/ ext1, induction p, dsimp at *, simp at * end
end functor

def Aut (X : C) := X ≅ X

attribute [extensionality Aut] iso.ext

instance {X : C} : group (Aut X) :=
by refine { one := iso.refl X,
            inv := iso.symm,
            mul := iso.trans, .. } ; obviously

end category_theory
