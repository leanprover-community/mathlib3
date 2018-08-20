-- Copyright (c) 2017 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Tim Baumann, Stephen Morgan, Scott Morrison

import category_theory.functor

-- TODO remove these once everything is merged
import tactic.tidy
@[obviously] meta def obviously' := tactic.tidy

universes u v

namespace category_theory

structure iso {C : Type u} [category.{u v} C] (X Y : C) :=
(hom : X ⟶ Y)
(inv : Y ⟶ X)
(hom_inv_id' : hom ≫ inv = 𝟙 X . obviously)
(inv_hom_id' : inv ≫ hom = 𝟙 Y . obviously)

restate_axiom iso.hom_inv_id'
restate_axiom iso.inv_hom_id'
attribute [simp] iso.hom_inv_id iso.inv_hom_id

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

@[refl] def refl (X : C) : X ≅ X := 
{ hom := 𝟙 X,
  inv := 𝟙 X }

@[simp] lemma refl_map (X : C) : (iso.refl X).hom = 𝟙 X := rfl
@[simp] lemma refl_coe (X : C) : ((iso.refl X) : X ⟶ X) = 𝟙 X := rfl
@[simp] lemma refl_inv  (X : C) : (iso.refl X).inv  = 𝟙 X := rfl

@[trans] def trans (α : X ≅ Y) (β : Y ≅ Z) : X ≅ Z := 
{ hom := α.hom ≫ β.hom,
  inv := β.inv ≫ α.inv,
  hom_inv_id' := begin /- `obviously'` says: -/ erw [category.assoc], conv { to_lhs, congr, skip, rw ← category.assoc }, rw iso.hom_inv_id, rw category.id_comp, rw iso.hom_inv_id end,
  inv_hom_id' := begin /- `obviously'` says: -/ erw [category.assoc], conv { to_lhs, congr, skip, rw ← category.assoc }, rw iso.inv_hom_id, rw category.id_comp, rw iso.inv_hom_id end }

infixr ` ≪≫ `:80 := iso.trans -- type as `\ll \gg`.

@[simp] lemma trans_hom (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).hom = α.hom ≫ β.hom := rfl
@[simp] lemma trans_coe (α : X ≅ Y) (β : Y ≅ Z) : ((α ≪≫ β) : X ⟶ Z) = (α : X ⟶ Y) ≫ (β : Y ⟶ Z) := rfl
@[simp] lemma trans_inv (α : X ≅ Y) (β : Y ≅ Z) : (α ≪≫ β).inv  = β.inv ≫ α.inv   := rfl

@[symm] def symm (I : X ≅ Y) : Y ≅ X := 
{ hom := I.inv,
  inv := I.hom }

@[simp] lemma refl_symm_coe (X : C) : ((iso.refl X).symm : X ⟶ X)  = 𝟙 X := rfl
@[simp] lemma trans_symm_coe (α : X ≅ Y) (β : Y ≅ Z) : ((α ≪≫ β).symm : Z ⟶ X) = (β.symm : Z ⟶ Y) ≫ (α.symm : Y ⟶ X) := rfl

-- These next two aggressively rewrite the projections `.hom` and `.inv` into coercions.
-- I'm not certain it is a good idea.
@[simp] lemma hom_coe (α : X ≅ Y) : α.hom = (α : X ⟶ Y) := rfl
@[simp] lemma inv_coe (α : X ≅ Y) : α.inv = (α.symm : Y ⟶ X) := rfl

-- FIXME these are actually the ones we want to use
@[simp] lemma hom_inv_id_coe (α : X ≅ Y) : (α : X ⟶ Y) ≫ (α.symm : Y ⟶ X) = 𝟙 X := begin unfold_coes, unfold symm, rw iso.hom_inv_id, end
@[simp] lemma inv_hom_id_coe (α : X ≅ Y) : (α.symm : Y ⟶ X) ≫ (α : X ⟶ Y) = 𝟙 Y := begin unfold_coes, unfold symm, rw iso.inv_hom_id, end

end iso

class is_iso (f : X ⟶ Y) :=
(inv : Y ⟶ X)
(hom_inv_id' : f ≫ inv = 𝟙 X . obviously)
(inv_hom_id' : inv ≫ f = 𝟙 Y . obviously)

restate_axiom is_iso.hom_inv_id'
restate_axiom is_iso.inv_hom_id'
attribute [simp,ematch] is_iso.hom_inv_id is_iso.inv_hom_id

def inv' {f : X ⟶ Y} (p : is_iso f) := is_iso.inv f 
def hom_inv_id' {f : X ⟶ Y} (p : is_iso f) : f ≫ inv' p = 𝟙 X := is_iso.hom_inv_id f 
def inv_hom_id' {f : X ⟶ Y} (p : is_iso f) : inv' p ≫ f = 𝟙 Y := is_iso.inv_hom_id f 

namespace is_iso

instance (X : C) : is_iso (𝟙 X) := 
{ inv := 𝟙 X }

instance of_iso         (f : X ≅ Y) : is_iso (f : X ⟶ Y) :=
{ inv   := f.inv }
instance of_iso_inverse (f : X ≅ Y) : is_iso (f.symm : Y ⟶ X)  := 
{ inv   := f.hom }

end is_iso

namespace functor

universes u₁ v₁ u₂ v₂ 
variables {D : Type u₂}

variables [𝒟 : category.{u₂ v₂} D]
include 𝒟

def on_isos (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F X) ≅ (F Y) :=
{ hom := F.map i.hom,
  inv := F.map i.inv,
  hom_inv_id' := begin /- `obviously'` says: -/ dsimp at *, erw [←map_comp, iso.hom_inv_id_coe, ←map_id] end,
  inv_hom_id' := begin /- `obviously'` says: -/ dsimp at *, erw [←map_comp, iso.inv_hom_id_coe, ←map_id] end }

@[simp,ematch] lemma on_isos_hom (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F.on_isos i).hom = F.map i.hom := rfl
@[simp,ematch] lemma on_isos_inv (F : C ↝ D) {X Y : C} (i : X ≅ Y) : (F.on_isos i).inv = F.map i.inv := rfl

end functor

class epi  (f : X ⟶ Y) := 
(left_cancellation : Π {Z : C} (g h : Y ⟶ Z) (w : f ≫ g = f ≫ h), g = h)
class mono (f : X ⟶ Y) :=
(right_cancellation : Π {Z : C} (g h : Z ⟶ X) (w : g ≫ f = h ≫ f), g = h)

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

@[simp] lemma cancel_epi  (f : X ⟶ Y) [epi f]  (g h : Y ⟶ Z) : (f ≫ g = f ≫ h) ↔ g = h := 
⟨ λ p, epi.left_cancellation g h p, by tidy ⟩
@[simp] lemma cancel_mono (f : X ⟶ Y) [mono f] (g h : Z ⟶ X) : (g ≫ f = h ≫ f) ↔ g = h := 
⟨ λ p, mono.right_cancellation g h p, by tidy ⟩

end category_theory