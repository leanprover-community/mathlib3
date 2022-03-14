/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.coherence

namespace category_theory

namespace bicategory

open category
open_locale bicategory

universes w₁ w₂ v₁ v₂ u₁ u₂

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {a b c d : B}

@[nolint has_inhabited_instance]
structure adjunction (f : a ⟶ b) (g : b ⟶ a) :=
(unit : 𝟙 a ⟶ f ≫ g)
(counit : g ≫ f ⟶ 𝟙 b)
(left_triangle' : (unit ▷ f) ≫ (α_ f g f).hom ≫ (f ◁ counit) =
  (λ_ f).hom ≫ (ρ_ f).inv . obviously)
(right_triangle' : (g ◁ unit) ≫ (α_ g f g).inv ≫ (counit ▷ g) =
  (ρ_ g).hom ≫ (λ_ g).inv . obviously)

localized "infix ` ⊣ `:15 := adjunction" in bicategory

namespace adjunction

restate_axiom left_triangle'
restate_axiom right_triangle'
attribute [simp, reassoc] left_triangle right_triangle

@[simp, reassoc]
lemma associator_inv_naturality_left_symm {f f' : a ⟶ b} (η : f ⟶ f') (g : b ⟶ c) (h : c ⟶ d) :
  (α_ f g h).inv ≫ ((η ▷ g) ▷ h) = (η ▷ (g ≫ h)) ≫ (α_ f' g h).inv :=
(associator_inv_naturality_left η g h).symm

@[simp, reassoc]
lemma associator_inv_naturality_middle_symm (f : a ⟶ b) {g g' : b ⟶ c} (η : g ⟶ g') (h : c ⟶ d) :
  (α_ f g h).inv ≫ ((f ◁ η) ▷ h) = (f ◁ (η ▷ h)) ≫ (α_ f g' h).inv :=
(associator_inv_naturality_middle f η h).symm

@[simp, reassoc]
lemma associator_inv_naturality_right_symm (f : a ⟶ b) (g : b ⟶ c) {h h' : c ⟶ d} (η : h ⟶ h') :
  (α_ f g h).inv ≫ ((f ≫ g) ◁ η) = (f ◁ (g ◁ η)) ≫ (α_ f g h').inv :=
(associator_inv_naturality_right f g η).symm

@[simp, reassoc]
lemma left_unitor_inv_naturality_symm {f f' : a ⟶ b} (η : f ⟶ f') :
  (λ_ f).inv ≫ (𝟙 a ◁ η) = η ≫ (λ_ f').inv :=
(left_unitor_inv_naturality η).symm

@[simp, reassoc]
lemma right_unitor_inv_naturality_symm {f f' : a ⟶ b} (η : f ⟶ f') :
  (ρ_ f ).inv ≫ (η ▷ 𝟙 b) = η ≫ (ρ_ f').inv :=
(right_unitor_inv_naturality η).symm

local attribute [simp]
  associator_naturality_left
  associator_naturality_middle
  associator_naturality_right
  associator_naturality_left_assoc
  associator_naturality_middle_assoc
  associator_naturality_right_assoc
  left_unitor_naturality
  left_unitor_naturality_assoc
  right_unitor_naturality
  right_unitor_naturality_assoc

lemma right_adjoint_uniq_aux {f : a ⟶ b} {g₁ g₂ : b ⟶ a} (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) :
  ((ρ_ g₁).inv ≫ (g₁ ◁ adj₂.unit) ≫ (α_ g₁ f g₂).inv ≫ (adj₁.counit ▷ g₂) ≫ (λ_ g₂).hom) ≫
    (ρ_ g₂).inv ≫ (g₂ ◁ adj₁.unit) ≫ (α_ g₂ f g₁).inv ≫ (adj₂.counit ▷ g₁) ≫ (λ_ g₁).hom =
      𝟙 g₁ :=
begin
  apply (cancel_epi (ρ_ g₁).hom).1,
  apply (cancel_mono (λ_ g₁).inv).1,
  apply (cancel_epi (g₁ ◁ (ρ_ (𝟙 a)).hom)).1,
  apply (cancel_mono ((λ_ (𝟙 b)).inv ▷ g₁)).1,
  simp only [iso.hom_inv_id_assoc, assoc, comp_id],
  calc
    _   =
    (α_ _ _ _).inv ≫ ((g₁ ◁ adj₂.unit) ▷ _) ≫ ((α_ g₁ f g₂).inv ▷ _) ≫
      ((adj₁.counit ▷ g₂) ▷ _) ≫ (α_ _ _ _).hom ≫ (_ ◁ (g₂ ◁ adj₁.unit)) ≫
        (_ ◁ (α_ g₂ f g₁).inv) ≫ (_ ◁ (adj₂.counit ▷ g₁)) ≫ (α_ _ _ _).inv : _
    ... =
    (g₁ ◁ (ρ_ _).hom) ≫ (g₁ ◁ adj₁.unit) ≫ (g₁ ◁ (((λ_ f).inv ≫ (adj₂.unit ▷ f) ≫
      (α_ _ _ _).hom ≫ (f ◁ adj₂.counit) ≫ (ρ_ f).hom) ▷ g₁)) ≫ (α_ _ _ _).inv ≫
        (adj₁.counit ▷ g₁) ≫ ((λ_ _).inv ▷ g₁) : _
    ... = _ : _,
  { simp_rw [
      ←whisker_left_comp_assoc, ←right_unitor_naturality, right_unitor_comp, whisker_left_comp,
      ←whisker_right_comp, left_unitor_inv_naturality, left_unitor_comp_inv, whisker_right_comp,
      assoc, ←associator_inv_naturality_left_assoc, associator_inv_naturality_right_assoc,
      whisker_exchange_assoc, left_unitor_right_unitor_inv_assoc, hom_inv_whisker_right_assoc,
      hom_inv_whisker_left_assoc, ←associator_inv_naturality_right_assoc,
      associator_naturality_left_assoc, ←associator_inv_naturality_middle_assoc,
      pentagon_inv_inv_hom_hom_inv_assoc, associator_inv_naturality_middle,
      pentagon_inv_inv_hom_inv_inv_assoc] },
  { apply (cancel_epi (g₁ ◁ (ρ_ (𝟙 a)).inv)).1,
    apply (cancel_mono ((λ_ (𝟙 b)).hom ▷ g₁)).1,
    simp_rw [associator_naturality_left_assoc, ←associator_inv_naturality_middle_assoc,
      pentagon_inv_inv_hom_hom_inv_assoc, ←whisker_exchange_assoc,
      ←associator_inv_naturality_right_assoc,
      associator_inv_naturality_left, ←pentagon_inv_assoc, ←whisker_left_comp_assoc g₁,
      associator_inv_naturality_middle, ←associator_naturality_right_assoc,
      pentagon_hom_inv_inv_inv_hom_assoc, ←whisker_exchange_assoc,
      associator_inv_naturality_left_assoc, ←unitors_inv_equal,
      ←left_unitor_inv_naturality_assoc, left_unitor_comp_inv_assoc, iso.hom_inv_id_assoc,
      whisker_right_comp, whisker_left_comp_assoc, associator_inv_naturality_middle_assoc g₁,
      ←whisker_right_comp, unitors_inv_equal, right_unitor_inv_naturality,
      right_unitor_comp_inv_assoc, hom_inv_whisker_left_assoc, inv_hom_whisker_left_assoc] },
  { simp_rw [left_triangle_assoc, iso.inv_hom_id_assoc, iso.inv_hom_id,
      whisker_right_id, whisker_left_id, id_comp, right_triangle_assoc] }
end

def right_adjoint_uniq {f : a ⟶ b} {g₁ g₂ : b ⟶ a}
  (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) : g₁ ≅ g₂ :=
{ hom := (ρ_ g₁).inv ≫ (g₁ ◁ adj₂.unit) ≫ (α_ g₁ f g₂).inv ≫ (adj₁.counit ▷ g₂) ≫ (λ_ g₂).hom,
  inv := (ρ_ g₂).inv ≫ (g₂ ◁ adj₁.unit) ≫ (α_ g₂ f g₁).inv ≫ (adj₂.counit ▷ g₁) ≫ (λ_ g₁).hom,
  hom_inv_id' := right_adjoint_uniq_aux adj₁ adj₂,
  inv_hom_id' := right_adjoint_uniq_aux adj₂ adj₁ }

example
  {f₁ : a ⟶ b}
  {g₁ : b ⟶ a}
  {f₂ : b ⟶ c}
  {g₂ : c ⟶ b}
  (adj₁ : f₁ ⊣ g₁)
  (adj₂ : f₂ ⊣ g₂) :
(𝟙 a ≫ 𝟙 a) ≫ f₁ ≫ f₂ ⟶ (f₁ ≫ f₂) ≫ 𝟙 c ≫ 𝟙 c :=
begin
  refine (α_ _ _ _).hom ≫
  (𝟙 a ◁ adj₁.unit ▷ f₁ ≫ f₂) ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv))) ≫
    (𝟙 a ◁ f₁ ◁ adj₁.counit ▷ f₂) ≫ (α_ _ _ _).inv ≫
      (((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ 𝟙 b ≫ f₂) ≫ (α_ _ _ _).hom ≫
        (f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv)) ≫ 𝟙 _ ≫
          (f₁ ◁ adj₂.unit ▷ f₂ ≫ 𝟙 c) ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv))) ≫
            (f₁ ◁ f₂ ◁ adj₂.counit ▷ 𝟙 c) ≫ (α_ _ _ _).inv,
end

example {B : Type u₁}
  [bicategory B]
  {a b c : B}
  {f₁ : a ⟶ b}
  {g₁ : b ⟶ a}
  {f₂ : b ⟶ c}
  {g₂ : c ⟶ b}
  (adj₁ : f₁ ⊣ g₁)
  (adj₂ : f₂ ⊣ g₂) :
  ((𝟙 a ◁ adj₁.unit) ≫
           (α_ (𝟙 a) f₁ g₁).inv ≫
             ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ g₁) ≫
               (α_ f₁ (𝟙 b) g₁).hom ≫
                 (f₁ ◁ adj₂.unit ▷ g₁) ≫
                   (f₁ ◁ (α_ f₂ g₂ g₁).hom) ≫
                     (α_ f₁ f₂ (g₂ ≫ g₁)).inv ▷
         f₁ ≫ f₂) ≫
      (α_ (f₁ ≫ f₂) (g₂ ≫ g₁) (f₁ ≫ f₂)).hom ≫
        (f₁ ≫ f₂ ◁
           (α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫
             (g₂ ◁ (α_ g₁ f₁ f₂).inv) ≫
               (g₂ ◁ adj₁.counit ▷ f₂) ≫
                 (g₂ ◁ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                   (α_ g₂ f₂ (𝟙 c)).inv ≫
                     (adj₂.counit ▷ 𝟙 c)) =
  (α_ _ _ _).hom ≫
    (𝟙 a ◁ adj₁.unit ▷ f₁ ≫ f₂) ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv))) ≫
      (𝟙 a ◁ f₁ ◁ adj₁.counit ▷ f₂) ≫ (α_ _ _ _).inv ≫
        (((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ 𝟙 b ≫ f₂) ≫ (α_ _ _ _).hom ≫
          (f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv)) ≫ 𝟙 _ ≫
            (f₁ ◁ adj₂.unit ▷ f₂ ≫ 𝟙 c) ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv))) ≫
              (f₁ ◁ f₂ ◁ adj₂.counit ▷ 𝟙 c) ≫ (α_ _ _ _).inv :=
begin
  simp_rw [whisker_right_comp_assoc, whisker_left_comp],
  apply (cancel_epi (α_ (𝟙 a) (𝟙 a) (f₁ ≫ f₂)).inv).1,
  simp_rw [←associator_inv_naturality_middle_assoc,
    ←pentagon_hom_inv_inv_inv_inv_assoc,
    ←associator_inv_naturality_left_assoc,
    ←pentagon_hom_inv_inv_inv_hom_assoc,
    ←associator_inv_naturality_middle_assoc,
    pentagon_inv_inv_hom_hom_inv_assoc,
    ←associator_inv_naturality_right_assoc],
  simp_rw [←whisker_left_comp_assoc f₁, pentagon_assoc,
    ←associator_inv_naturality_left_assoc, iso.inv_hom_id_assoc,
    ←associator_naturality_right_assoc, ←associator_naturality_right,
    ←whisker_exchange_assoc,
    whisker_left_comp_assoc, whisker_left_comp],
  simp_rw ←associator_naturality_right_assoc,
  simp_rw ←associator_naturality_middle_assoc,
  simp_rw ←whisker_exchange_assoc,
  simp_rw ←associator_inv_naturality_right_assoc,
  simp_rw assoc,
  congr' 7,
  apply (cancel_mono (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).hom).1,
  simp_rw assoc,
  simp only [associator_naturality_right, associator_naturality_right_assoc, iso.inv_hom_id_assoc,
  associator_naturality_middle_assoc, iso.inv_hom_id, comp_id, id_comp, iso.cancel_iso_hom_left],
  simp_rw [←whisker_left_comp f₁],
  congr' 1,
  simp only [whisker_exchange_assoc, associator_naturality_right_assoc],
end

example {B : Type u₁}
  [bicategory B]
  {a b c : B}
  {f₁ : a ⟶ b}
  {g₁ : b ⟶ a}
  {f₂ : b ⟶ c}
  {g₂ : c ⟶ b}
  (adj₁ : f₁ ⊣ g₁)
  (adj₂ : f₂ ⊣ g₂) :
  ((𝟙 a ◁ adj₁.unit) ≫
           (α_ (𝟙 a) f₁ g₁).inv ≫
             ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ g₁) ≫
               (α_ f₁ (𝟙 b) g₁).hom ≫
                 (f₁ ◁ adj₂.unit ▷ g₁) ≫
                   (f₁ ◁ (α_ f₂ g₂ g₁).hom) ≫
                     (α_ f₁ f₂ (g₂ ≫ g₁)).inv ▷
         f₁ ≫ f₂) ≫
      (α_ (f₁ ≫ f₂) (g₂ ≫ g₁) (f₁ ≫ f₂)).hom ≫
        (f₁ ≫ f₂ ◁
           (α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫
             (g₂ ◁ (α_ g₁ f₁ f₂).inv) ≫
               (g₂ ◁ adj₁.counit ▷ f₂) ≫
                 (g₂ ◁ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                   (α_ g₂ f₂ (𝟙 c)).inv ≫
                     (adj₂.counit ▷ 𝟙 c)) =
  (α_ _ _ _).hom ≫
    (𝟙 a ◁ adj₁.unit ▷ f₁ ≫ f₂) ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv))) ≫
      (𝟙 a ◁ f₁ ◁ adj₁.counit ▷ f₂) ≫ (α_ _ _ _).inv ≫
        (((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ 𝟙 b ≫ f₂) ≫ (α_ _ _ _).hom ≫
          (f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv)) ≫ 𝟙 _ ≫
            (f₁ ◁ adj₂.unit ▷ f₂ ≫ 𝟙 c) ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv))) ≫
              (f₁ ◁ f₂ ◁ adj₂.counit ▷ 𝟙 c) ≫ (α_ _ _ _).inv :=
begin
  apply (cancel_mono (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).hom).1,
  simp only [whisker_right_comp, assoc, triangle_assoc_comp_right_inv_assoc, whisker_left_comp, associator_naturality_right,
  associator_naturality_right_assoc, associator_inv_naturality_right_assoc, id_comp, left_unitor_comp_inv,
  whisker_exchange_assoc, iso.inv_hom_id_assoc],
  simp_rw [←whisker_left_comp f₁],
  simp only [whisker_exchange_assoc, associator_naturality_right_assoc],
  simp_rw [whisker_left_comp, ←assoc], congr' 4, simp_rw assoc,
  apply (cancel_mono (f₁ ◁ (α_ f₂ g₂ (𝟙 b ≫ f₂)).inv)).1,
  simp_rw [assoc, ←whisker_left_comp f₁],
  simp_rw [associator_inv_naturality_right, associator_inv_naturality_right_assoc,
    iso.hom_inv_id, comp_id],
  simp_rw [←pentagon_inv_inv_hom_hom_inv_assoc, whisker_left_comp, pentagon_hom_hom_inv_hom_hom_assoc],
  simp only [inv_hom_whisker_right_assoc, associator_naturality_middle_assoc, associator_naturality_left_assoc,
  associator_inv_naturality_middle_assoc, iso.hom_inv_id_assoc],
  simp_rw [←whisker_left_comp f₁],
  congr' 5,
  simp only [hom_inv_whisker_right_assoc, associator_naturality_left_assoc],
  simp only [←whisker_exchange_assoc, ←whisker_exchange],
  simp_rw ←assoc, congr' 1, simp_rw assoc,
  apply (cancel_mono (α_ (𝟙 b) (𝟙 b) f₂).inv).1,
  simp only [assoc, associator_inv_naturality_middle, iso.hom_inv_id, comp_id],
  rw pentagon_hom_inv_inv_inv_hom_assoc,
  simp only [associator_inv_naturality_left_assoc, iso.cancel_iso_inv_left],
  simp_rw [←whisker_right_comp _ _ f₂],
  congr' 1,
  rw [left_unitor_inv_naturality],
  simp only [left_unitor_comp_inv, assoc]
end

example {B : Type u₁}
  [bicategory B]
  {a b c : B}
  {f₁ : a ⟶ b}
  {g₁ : b ⟶ a}
  {f₂ : b ⟶ c}
  {g₂ : c ⟶ b}
  (adj₁ : f₁ ⊣ g₁)
  (adj₂ : f₂ ⊣ g₂) :
  (α_ (𝟙 a) (𝟙 a) (f₁ ≫ f₂)).hom ≫
      (𝟙 a ◁ adj₁.unit ▷ f₁ ≫ f₂) ≫
        (𝟙 a ◁
             (α_ f₁ g₁ (f₁ ≫ f₂)).hom ≫
               (f₁ ◁ (α_ g₁ f₁ f₂).inv)) ≫
          (𝟙 a ◁ f₁ ◁ adj₁.counit ▷ f₂) ≫
            (α_ (𝟙 a) f₁ (𝟙 b ≫ f₂)).inv ≫
              ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ 𝟙 b ≫ f₂) ≫
                (α_ f₁ (𝟙 b) (𝟙 b ≫ f₂)).hom ≫
                  (f₁ ◁ 𝟙 b ◁ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                    𝟙 (f₁ ≫ 𝟙 b ≫ f₂ ≫ 𝟙 c) ≫
                      (f₁ ◁ adj₂.unit ▷ f₂ ≫ 𝟙 c) ≫
                        (f₁ ◁
                             (α_ f₂ g₂ (f₂ ≫ 𝟙 c)).hom ≫
                               (f₂ ◁ (α_ g₂ f₂ (𝟙 c)).inv)) ≫
                          (f₁ ◁ f₂ ◁ adj₂.counit ▷ 𝟙 c) ≫
                            (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).inv =
    (α_ (𝟙 a) (𝟙 a) (f₁ ≫ f₂)).hom ≫
      (𝟙 a ◁ (α_ (𝟙 a) f₁ f₂).inv) ≫
        (𝟙 a ◁ (λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ f₂) ≫
          (𝟙 a ◁ (α_ f₁ (𝟙 b) f₂).hom) ≫
            (α_ (𝟙 a) f₁ (𝟙 b ≫ f₂)).inv ≫
              ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ 𝟙 b ≫ f₂) ≫
                (α_ f₁ (𝟙 b) (𝟙 b ≫ f₂)).hom ≫
                  (f₁ ◁ 𝟙 b ◁ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                    (f₁ ◁ (α_ (𝟙 b) f₂ (𝟙 c)).inv) ≫
                      (f₁ ◁
                           (λ_ f₂).hom ≫ (ρ_ f₂).inv ▷ 𝟙 c) ≫
                        (f₁ ◁ (α_ f₂ (𝟙 c) (𝟙 c)).hom) ≫
                          (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).inv :=
begin
  simp only [whisker_left_comp, whisker_right_comp, assoc],
  simp_rw ←whisker_left_comp_assoc (𝟙 a),
  have :
    (adj₁.unit ▷ f₁ ≫ f₂) ≫ (α_ f₁ g₁ (f₁ ≫ f₂)).hom ≫
      (f₁ ◁ (α_ g₁ f₁ f₂).inv) ≫ (f₁ ◁ adj₁.counit ▷ f₂) =
    (α_ (𝟙 a) f₁ f₂).inv ≫ ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ f₂) ≫ (α_ f₁ (𝟙 b) f₂).hom,
  { apply (cancel_mono (α_ f₁ (𝟙 b) f₂).inv).1,
    simp only [pentagon_hom_inv_inv_inv_hom_assoc, whisker_left_comp, assoc, associator_inv_naturality_middle,
    associator_inv_naturality_left_assoc, whisker_right_comp, triangle_assoc_comp_right_inv, triangle_assoc_comp_left_inv,
    iso.cancel_iso_inv_left],
    simp_rw ←whisker_right_comp, congr' 1,
    simp only [left_triangle] },
  rw this,
  simp only [whisker_left_comp, whisker_right_comp, assoc, id_comp],
  congr' 11, simp_rw ←assoc, congr' 1, simp_rw [assoc, ←whisker_left_comp f₁], congr' 1,
  apply (cancel_mono (α_ f₂ (𝟙 c) (𝟙 c)).inv).1,
  simp only [pentagon_hom_inv_inv_inv_hom_assoc, assoc, associator_inv_naturality_middle, associator_inv_naturality_left_assoc,
  triangle_assoc_comp_right_inv, triangle_assoc_comp_left_inv, iso.cancel_iso_inv_left],
  simp_rw ←whisker_right_comp, congr' 1,
  simp only [left_triangle]
end

open free_bicategory

lemma comp_aux_free
  {B : Type u₁}
  [quiver.{v₁+1} B]
  {a b c : free_bicategory B}
  (f₁ : a ⟶ b)
  (g₁ : b ⟶ a)
  (f₂ : b ⟶ c)
  (g₂ : c ⟶ b) :
  (α_ (𝟙 a) (𝟙 a) (f₁ ≫ f₂)).hom ≫
      (𝟙 a ◁ (α_ (𝟙 a) f₁ f₂).inv) ≫
        (𝟙 a ◁ (λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ f₂) ≫
          (𝟙 a ◁ (α_ f₁ (𝟙 b) f₂).hom) ≫
            (α_ (𝟙 a) f₁ (𝟙 b ≫ f₂)).inv ≫
              ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ 𝟙 b ≫ f₂) ≫
                (α_ f₁ (𝟙 b) (𝟙 b ≫ f₂)).hom ≫
                  (f₁ ◁ 𝟙 b ◁ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                    (f₁ ◁ (α_ (𝟙 b) f₂ (𝟙 c)).inv) ≫
                      (f₁ ◁
                           (λ_ f₂).hom ≫ (ρ_ f₂).inv ▷ 𝟙 c) ≫
                        (f₁ ◁ (α_ f₂ (𝟙 c) (𝟙 c)).hom) ≫
                          (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).inv =
    (((λ_ (𝟙 a)).hom ▷ f₁ ≫ f₂) ≫
         (λ_ (f₁ ≫ f₂)).hom ≫ (ρ_ (f₁ ≫ f₂)).inv) ≫
      (f₁ ≫ f₂ ◁ (λ_ (𝟙 c)).inv) :=
subsingleton.elim _ _

lemma comp_triangle_aux {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
  (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
    ((λ_ (𝟙 a)).inv ≫
      (𝟙 a ◁ adj₁.unit) ≫
        (α_ (𝟙 a) f₁ g₁).inv ≫ ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ g₁) ≫ (α_ f₁ (𝟙 b) g₁).hom ≫
          (f₁ ◁ adj₂.unit ▷ g₁) ≫ (f₁ ◁ (α_ f₂ g₂ g₁).hom) ≫ (α_ f₁ f₂ (g₂ ≫ g₁)).inv ▷
      f₁ ≫ f₂) ≫
        (α_ (f₁ ≫ f₂) (g₂ ≫ g₁) (f₁ ≫ f₂)).hom ≫
          (f₁ ≫ f₂ ◁
            (α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫ (g₂ ◁ (α_ g₁ f₁ f₂).inv) ≫ (g₂ ◁ adj₁.counit ▷ f₂) ≫
              (g₂ ◁ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫ (α_ g₂ f₂ (𝟙 c)).inv ≫
                (adj₂.counit ▷ 𝟙 c) ≫ (λ_ (𝟙 c)).hom) =
    (λ_ (f₁ ≫ f₂)).hom ≫ (ρ_ (f₁ ≫ f₂)).inv :=
begin
  apply (cancel_epi ((λ_ (𝟙 a )).hom ▷ (f₁ ≫ f₂))).1,
  apply (cancel_mono ((f₁ ≫ f₂) ◁ (λ_ (𝟙 c )).inv)).1,
  calc _
  =
  (α_ _ _ _).hom ≫
    (𝟙 a ◁ adj₁.unit ▷ f₁ ≫ f₂) ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv))) ≫
      (𝟙 a ◁ f₁ ◁ adj₁.counit ▷ f₂) ≫ (α_ _ _ _).inv ≫
        (((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ 𝟙 b ≫ f₂) ≫ (α_ _ _ _).hom ≫
          (f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv)) ≫ 𝟙 _ ≫
            (f₁ ◁ adj₂.unit ▷ f₂ ≫ 𝟙 c) ≫ (_ ◁ ((α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv))) ≫
              (f₁ ◁ f₂ ◁ adj₂.counit ▷ 𝟙 c) ≫ (α_ _ _ _).inv : _
  ... =
  (α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv) ≫
    (𝟙 a ◁ ((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ f₂) ≫ (_ ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫
      (((λ_ f₁).hom ≫ (ρ_ f₁).inv) ▷ 𝟙 b ≫ f₂) ≫ (α_ _ _ _).hom ≫
        (f₁ ◁ 𝟙 b ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv)) ≫ (_ ◁ (α_ _ _ _).inv) ≫
          (f₁ ◁ ((λ_ f₂).hom ≫ (ρ_ f₂).inv) ▷ 𝟙 c) ≫ (_ ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv : _
  ... = _ : _,
  { simp_rw [assoc, ←whisker_left_comp (f₁ ≫ f₂), assoc, iso.hom_inv_id, comp_id],
    simp_rw [←whisker_right_comp_assoc, iso.hom_inv_id_assoc],
    apply (cancel_mono (α_ f₁ f₂ (𝟙 c ≫ 𝟙 c)).hom).1,
    simp only [whisker_right_comp, assoc, triangle_assoc_comp_right_inv_assoc, whisker_left_comp, associator_naturality_right,
    associator_naturality_right_assoc, associator_inv_naturality_right_assoc, id_comp, left_unitor_comp_inv,
    whisker_exchange_assoc, iso.inv_hom_id_assoc],
    simp_rw [←whisker_left_comp f₁],
    simp only [whisker_exchange_assoc, associator_naturality_right_assoc],
    simp_rw [whisker_left_comp, ←assoc], congr' 4, simp_rw assoc,
    apply (cancel_mono (f₁ ◁ (α_ f₂ g₂ (𝟙 b ≫ f₂)).inv)).1,
    simp_rw [assoc, ←whisker_left_comp f₁],
    simp_rw [associator_inv_naturality_right, associator_inv_naturality_right_assoc,
      iso.hom_inv_id, comp_id],
    simp_rw [←pentagon_inv_inv_hom_hom_inv_assoc, whisker_left_comp, pentagon_hom_hom_inv_hom_hom_assoc],
    simp only [inv_hom_whisker_right_assoc, associator_naturality_middle_assoc, associator_naturality_left_assoc,
    associator_inv_naturality_middle_assoc, iso.hom_inv_id_assoc],
    simp_rw [←whisker_left_comp f₁],
    congr' 5,
    simp only [hom_inv_whisker_right_assoc, associator_naturality_left_assoc],
    simp only [←whisker_exchange_assoc, ←whisker_exchange],
    simp_rw ←assoc, congr' 1, simp_rw assoc,
    apply (cancel_mono (α_ (𝟙 b) (𝟙 b) f₂).inv).1,
    simp only [assoc, associator_inv_naturality_middle, iso.hom_inv_id, comp_id],
    rw pentagon_hom_inv_inv_inv_hom_assoc,
    simp only [associator_inv_naturality_left_assoc, iso.cancel_iso_inv_left],
    simp_rw [←whisker_right_comp _ _ f₂],
    congr' 1,
    rw [left_unitor_inv_naturality],
    simp only [left_unitor_comp_inv, assoc] },
  { simp only [whisker_left_comp, whisker_right_comp, assoc],
    simp_rw ←whisker_left_comp_assoc (𝟙 a),
    have :
      (adj₁.unit ▷ f₁ ≫ f₂) ≫ (α_ f₁ g₁ (f₁ ≫ f₂)).hom ≫
        (f₁ ◁ (α_ g₁ f₁ f₂).inv) ≫ (f₁ ◁ adj₁.counit ▷ f₂) =
      (α_ (𝟙 a) f₁ f₂).inv ≫ ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ f₂) ≫ (α_ f₁ (𝟙 b) f₂).hom,
    { apply (cancel_mono (α_ f₁ (𝟙 b) f₂).inv).1,
      simp only [pentagon_hom_inv_inv_inv_hom_assoc, whisker_left_comp, assoc, associator_inv_naturality_middle,
      associator_inv_naturality_left_assoc, whisker_right_comp, triangle_assoc_comp_right_inv, triangle_assoc_comp_left_inv,
      iso.cancel_iso_inv_left],
      simp_rw ←whisker_right_comp, congr' 1,
      simp only [left_triangle] },
    rw this,
    simp only [whisker_left_comp, whisker_right_comp, assoc, id_comp],
    congr' 11, simp_rw ←assoc, congr' 1, simp_rw [assoc, ←whisker_left_comp f₁], congr' 1,
    apply (cancel_mono (α_ f₂ (𝟙 c) (𝟙 c)).inv).1,
    simp only [pentagon_hom_inv_inv_inv_hom_assoc, assoc, associator_inv_naturality_middle, associator_inv_naturality_left_assoc,
    triangle_assoc_comp_right_inv, triangle_assoc_comp_left_inv, iso.cancel_iso_inv_left],
    simp_rw ←whisker_right_comp, congr' 1,
    simp only [left_triangle] },
  { apply congr_arg
      (λ η, (free_bicategory.lift (prefunctor.id B)).map₂ η)
      (comp_aux_free (of.map f₁) (of.map g₁) (of.map f₂) (of.map g₂)) }
end

example {B : Type u₁}
  [bicategory B]
  {a b c : B}
  {f₁ : a ⟶ b}
  {g₁ : b ⟶ a}
  {f₂ : b ⟶ c}
  {g₂ : c ⟶ b}
  (adj₁ : f₁ ⊣ g₁)
  (adj₂ : f₂ ⊣ g₂) :
  (g₂ ≫ g₁ ◁
         (λ_ (𝟙 a)).inv ≫
           (𝟙 a ◁ adj₁.unit) ≫
             (α_ (𝟙 a) f₁ g₁).inv ≫
               ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ g₁) ≫
                 (α_ f₁ (𝟙 b) g₁).hom ≫
                   (f₁ ◁ adj₂.unit ▷ g₁) ≫
                     (f₁ ◁ (α_ f₂ g₂ g₁).hom) ≫
                       (α_ f₁ f₂ (g₂ ≫ g₁)).inv) ≫
      (α_ (g₂ ≫ g₁) (f₁ ≫ f₂) (g₂ ≫ g₁)).inv ≫
        ((α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫
             (g₂ ◁ (α_ g₁ f₁ f₂).inv) ≫
               (g₂ ◁ adj₁.counit ▷ f₂) ≫
                 (g₂ ◁ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
                   (α_ g₂ f₂ (𝟙 c)).inv ≫
                     (adj₂.counit ▷ 𝟙 c) ≫ (λ_ (𝟙 c)).hom ▷
           g₂ ≫ g₁) =
    (ρ_ (g₂ ≫ g₁)).hom ≫ (λ_ (g₂ ≫ g₁)).inv :=
begin
  admit,
end

def comp {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
  (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (f₁ ≫ f₂ ⊣ g₂ ≫ g₁) :=
{ unit :=
    (λ_ _).inv ≫ (_ ◁ adj₁.unit) ≫ (α_ _ _ _).inv ≫
      ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (f₁ ◁ adj₂.unit ▷ g₁) ≫
        (_ ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv,
  counit :=
    (α_ _ _ _).hom ≫ (g₂ ◁ (α_ _ _ _).inv) ≫ (g₂ ◁ adj₁.counit ▷ f₂) ≫
      (_ ◁ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫ (α_ _ _ _).inv ≫
        (adj₂.counit ▷ _) ≫ (λ_ _).hom,
  left_triangle' := comp_triangle_aux adj₁ adj₂,
  right_triangle' := begin
    extract_goal,
  end, }


def comp_unit {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}
  (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
(λ_ _).inv ≫ (_ ◁ adj₁.unit) ≫ (α_ _ _ _).inv ≫
  ((λ_ f₁).hom ≫ (ρ_ f₁).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (f₁ ◁ adj₂.unit ▷ g₁) ≫
    (_ ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv

def id (a : B) : 𝟙 a ⊣ 𝟙 a :=
{ unit := (ρ_ _).inv,
  counit := (ρ_ _).hom,
  left_triangle' := by
  { rw [triangle_assoc_comp_right_inv_assoc, unitors_inv_equal, unitors_equal], simp },
  right_triangle' := by
  { rw [triangle_assoc_comp_right, unitors_inv_equal, unitors_equal], simp } }

/-- The right adjoint mate `fᘁ : Xᘁ ⟶ Yᘁ` of a morphism `f : X ⟶ Y`. -/
def right_adjoint_mate {a b a' b': B} {f : a ⟶ b} {u : b ⟶ a} {f' : a' ⟶ b'} {u' : b' ⟶ a'}
{x : a ⟶ a'} {y : b ⟶ b'}
  (adj : f ⊣ u) (adj' : f' ⊣ u') (η : x ≫ f' ⟶ f ≫ y) :
    u ≫ x ⟶ y ≫ u' :=
(_ ◁ (ρ_ _).inv) ≫ (u ◁ x ◁ adj'.unit) ≫ (_ ◁ (α_ _ _ _).inv) ≫
  (u ◁ η ▷ u') ≫ (_ ◁ (α_ _ _ _).hom) ≫ (α_ _ _ _).inv ≫
    (adj.counit ▷ y ≫ u') ≫ (α_ _ _ _).inv ≫ ((λ_ _).hom ▷ _)

/-- The left adjoint mate `ᘁf : ᘁY ⟶ ᘁX` of a morphism `f : X ⟶ Y`. -/
def left_adjoint_mate
  {a b a' b': B} {f : a ⟶ b} {u : b ⟶ a} {f' : a' ⟶ b'} {u' : b' ⟶ a'}
  {x : a ⟶ a'} {y : b ⟶ b'}
  (adj : f ⊣ u) (adj' : f' ⊣ u') (η : u ≫ x ⟶ y ≫ u') :
    x ≫ f' ⟶ f ≫ y :=
((λ_ _).inv ▷ _) ≫ (α_ _ _ _).hom ≫ (adj.unit ▷ x ≫ f') ≫
  (α_ _ _ _).hom ≫ (_ ◁ (α_ _ _ _).inv) ≫ (_ ◁ η ▷ _) ≫
    (_ ◁ (α_ _ _ _).hom) ≫ (f ◁ y ◁ adj'.counit) ≫ (_ ◁ (ρ_ _).hom)

section
variables
  {a' b': B} {f : a ⟶ b} {u : b ⟶ a} {f' : a' ⟶ b'} {u' : b' ⟶ a'}
  {x : a ⟶ a'} {y : b ⟶ b'}
  (adj : f ⊣ u) (adj' : f' ⊣ u') (η : u ≫ x ⟶ y ≫ u')

lemma right_adjoint_mate_unitors_aux
  {a b : free_bicategory B}
  (f : a ⟶ b)
  (u : b ⟶ a) :
  (u ◁ (λ_ (f ≫ u)).inv) ≫
      (u ◁ (α_ (𝟙 a) f u).inv) ≫
        (u ◁ (λ_ f).hom ≫ (ρ_ f).inv ▷ u) ≫
          (u ◁ (α_ f (𝟙 b) u).hom) ≫
            (α_ u f (𝟙 b ≫ u)).inv ≫ (u ≫ f ◁ (λ_ u).hom) =
    (α_ u f u).inv :=
subsingleton.elim _ _

#print right_adjoint_mate

@[simp]
lemma right_adjoint_mate_unitors {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u) :
  right_adjoint_mate adj adj ((λ_ f).hom ≫ (ρ_ f).inv) =
    (ρ_ u).hom ≫ (λ_ u).inv :=
begin
  rw right_adjoint_mate,
  rw [←whisker_left_comp_assoc u, ←unitors_inv_equal,
      ←left_unitor_inv_naturality, whisker_left_comp,
      unitors_equal, triangle_assoc_comp_right, ←whisker_exchange],
  rw ←adj.right_triangle,
  simp_rw ←assoc, congr' 1, simp_rw assoc, congr' 1,
  simp [-whisker_left_comp, ←whisker_left_comp_assoc u]
  -- apply congr_arg
  --   (λ η, (free_bicategory.lift (prefunctor.id B)).map₂ η)
  --   (right_adjoint_mate_unitors_aux (of.map f) (of.map u))
end

lemma left_adjoint_mate_unitors_aux
  {a b : free_bicategory B}
  (f : a ⟶ b)
  (u : b ⟶ a) :
  (f ≫ u ◁ (λ_ f).inv) ≫
      (α_ f u (𝟙 a ≫ f)).hom ≫
        (f ◁ (α_ u (𝟙 a) f).inv) ≫
          (f ◁ (ρ_ u).hom ≫ (λ_ u).inv ▷ f) ≫
            (f ◁ (α_ (𝟙 b) u f).hom) ≫ (f ◁ (λ_ (u ≫ f)).hom) =
    (α_ f u f).hom :=
subsingleton.elim _ _

@[simp]
lemma left_adjoint_mate_unitors {f : a ⟶ b} {u : b ⟶ a} (adj : f ⊣ u) :
  left_adjoint_mate adj adj ((ρ_ u).hom ≫ (λ_ u).inv) =
    (λ_ f).hom ≫ (ρ_ f).inv :=
begin
  rw left_adjoint_mate,
  rw [unitors_inv_equal, triangle_assoc_comp_right_inv_assoc, whisker_exchange_assoc,
    ←whisker_left_comp f, ←unitors_equal, left_unitor_naturality, whisker_left_comp],
  rw ←adj.left_triangle,
  congr' 1, simp_rw ←assoc, congr' 1, simp_rw assoc,
  simp [-whisker_left_comp, ←whisker_left_comp f]
  -- apply congr_arg
  --   (λ η, (free_bicategory.lift (prefunctor.id B)).map₂ η)
  --   (left_adjoint_mate_unitors_aux (of.map f) (of.map u))
end

end

end adjunction

end bicategory

end category_theory
