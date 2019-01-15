-- Copyright (c) 2018 Johan Commelin. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Johan Commelin

import category_theory.sheaf_theory.sheaf

universes v u

lemma equiv_subsingleton {α β : Type*} [subsingleton α] [subsingleton β] (f : α → β) (g : β → α) :
α ≃ β :=
{ to_fun := f,
  inv_fun := g,
  left_inv := λ _, subsingleton.elim _ _,
  right_inv := λ _, subsingleton.elim _ _, }

namespace category_theory
open category_theory

variables {C : Type u} [cat : category.{v} C]
include cat

variables {X Y Z : C}

def is_iso_comp (f : X ⟶ Y) (hf : is_iso f) (g : Y ⟶ Z) (hg : is_iso g) : is_iso (f ≫ g) :=
{ inv := hg.inv ≫ hf.inv,
  hom_inv_id' := sorry,
  inv_hom_id' := sorry }

end category_theory

namespace category_theory
open category_theory

variables {X : Type u} [𝒳 : category.{v} X]
include 𝒳

local notation a `∈`:50 b:50 := b a

def covering_family.is_sieve {U : X} (c : covering_family U) : Prop :=
∀ Ui {fi : Ui ⟶ U} (H : fi ∈ c) V (g : V ⟶ Ui), (g ≫ fi) ∈ c

def sieve (U : X) : Type (max u v) := { S : covering_family U // S.is_sieve }

namespace sieve
variables {U : X}

def to_presheaf (S : sieve U) : presheaf X :=
{ obj := λ V, { f : V ⟶ U // f ∈ S.val },
  map := λ V₁ V₂ f g, ⟨f ≫ g.1, by apply S.property _ g.2⟩,
  map_id' := by tidy; exact category.id_comp _ _,
  map_comp' := by tidy; erw category.assoc }

@[simp] lemma to_presheaf_obj (S : sieve U) {V : X} :
S.to_presheaf.obj V = { f : V ⟶ U // f ∈ S.val } := rfl

@[simp] lemma to_presheaf_map (S : sieve U) {V₁ V₂ : X} (f : V₁ ⟶ V₂) (g) :
(S.to_presheaf.map f g) = ⟨f ≫ g.1, by apply S.property _ g.2⟩ :=
by cases g; refl

def inclusion (S : sieve U) : S.to_presheaf ⟶ yoneda.obj U :=
{ app := λ V, subtype.val }

@[simp] lemma inclusion_app (S : sieve U) (V) :
S.inclusion.app V = subtype.val := rfl

def sheaf_condition (S : sieve U) (F : presheaf X) :=
is_iso $ (yoneda.obj F).map S.inclusion

instance sheaf_condition.subsingleton {S : sieve U} {F : presheaf X} :
subsingleton (S.sheaf_condition F) := by delta sheaf_condition; apply_instance

end sieve

namespace covering_family
variables {U : X}

def generate_sieve (c : covering_family U) : sieve U :=
{ val := λ V g, ∃ (Ui : X) (fi : Ui ⟶ U) (h : V ⟶ Ui), fi ∈ c ∧ g = h ≫ fi,
  property :=
  begin
    intros Ui fi H V g,
    rcases H with ⟨Ui', fi', h, H⟩,
    use [Ui', fi', g ≫ h, H.1],
    simp [H.2]
  end }

@[simp] lemma generate_sieve_val (c : covering_family U) :
c.generate_sieve.val = λ V g, ∃ (Ui : X) (fi : Ui ⟶ U) (h : V ⟶ Ui), fi ∈ c ∧ g = h ≫ fi := rfl

lemma subset_generate_sieve (c : covering_family U) :
Π {{V}} (f : V ⟶ U), f ∈ c → f ∈ c.generate_sieve.val :=
begin
  intros Ui fi H,
  use [Ui, fi, 𝟙 _, H],
  simp
end

end covering_family

namespace sieve
variables {U : X}

lemma generate_sieve {U : X} (S : sieve U) : S.val.generate_sieve = S :=
begin
  apply subtype.ext.mpr,
  ext V g,
  split, swap,
  { apply S.val.subset_generate_sieve },
  { intro H,
    rcases H with ⟨Ui, fi, h, H⟩,
    rw H.2,
    apply S.property,
    exact H.1 }
end

def matching_sections_of_sieve_section (S : sieve U) :
(coyoneda.obj S.to_presheaf) ⟶ S.val.matching_sections :=
{ app := λ F (α : S.to_presheaf ⟶ F), show S.val.matching_sections.obj F, from
  { val := λ Ui fi h, α.app _ ⟨fi, h⟩,
    property :=
    begin
      intros,
      show (α.app _ ≫ F.map _) _ = (α.app _ ≫ F.map _) _,
      repeat {erw ← α.naturality},
      simp only [category_theory.types_comp],
      congr,
      simpa,
    end } }

@[simp] lemma matching_sections_of_sieve_section_app_val {S : sieve U} {F : presheaf X} (α : S.to_presheaf ⟶ F) :
(S.matching_sections_of_sieve_section.app F α).val = λ Ui fi h, α.app _ ⟨fi, h⟩ := rfl

def sieve_section_of_matching_sections (S : sieve U) :
S.val.matching_sections ⟶ (coyoneda.obj S.to_presheaf) :=
{ app := λ F (s : S.val.matching_sections.obj F), show S.to_presheaf ⟶ F, from
  { app := λ V f, s.1 f.2,
    naturality' := λ V₁ V₂ g,
    begin
      ext1 f,
      change X at V₁, change X at V₂,
      change V₂ ⟶ V₁ at g,
      simpa using s.2 (S.property _ f.2 _ _) f.2 (𝟙 _) g (show _ ≫ (g ≫ f.1) = g ≫ f.1, by simp)
    end } }

def sieve_section_iso_matching_sections (S : sieve U) :
(coyoneda.obj S.to_presheaf) ≅ S.val.matching_sections :=
{ hom := matching_sections_of_sieve_section S,
  inv := sieve_section_of_matching_sections S }

lemma commutes (S : sieve U) :
S.val.matching_sections_of_sections = (coyoneda.map S.inclusion) ≫ S.matching_sections_of_sieve_section :=
begin
  ext F s,
  apply subtype.ext.mpr,
  dsimp at *,
  funext Ui fi h,
  change (s.app U ≫ F.map fi) _ = _,
  simp [(s.naturality fi).symm]
end

lemma sheaf_condition_iff (S : sieve U) (F : presheaf X) :
S.val.sheaf_condition F ≃ S.sheaf_condition F :=
begin
  delta covering_family.sheaf_condition sheaf_condition,
  erw commutes S,
  simp only [functor.category.comp_app],
  apply equiv_subsingleton; intro H,
  { convert is_iso_comp _ H (S.sieve_section_of_matching_sections.app F) _,
    have := functor.on_iso (yoneda.obj F) S.sieve_section_iso_matching_sections,
    sorry },
   { apply is_iso_comp _ H, }
end
-- { to_fun    := λ H, -- show S.sheaf_condition F, from
--   { inv := λ s,
--     begin
--       apply H.inv,
--       exact S.matching_sections_of_sieve_section.app F s,
--     end,
--     hom_inv_id' :=
--     begin
--       ext1 s,
--       dsimp at *,
--     end,
--     inv_hom_id' :=
--     begin
--       ext s Ui fi,
--       dsimp at *,
--     end },
--   inv_fun   := _,
--   left_inv  := λ _, subsingleton.elim _ _,
--   right_inv := λ _, subsingleton.elim _ _ }

end sieve

end category_theory
