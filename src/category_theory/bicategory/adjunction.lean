/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.basic

namespace category_theory

namespace bicategory

open category
open_locale bicategory

universes w₁ w₂ v₁ v₂ u₁ u₂

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {a b : B}

@[nolint has_inhabited_instance]
structure adjunction (f : a ⟶ b) (g : b ⟶ a) :=
(unit : 𝟙 a ⟶ f ≫ g)
(counit : g ≫ f ⟶ 𝟙 b)
(left_triangle' : (unit ▷ f) ≫ (α_ f g f).hom ≫ (f ◁ counit) =
  (λ_ f).hom ≫ (ρ_ f).inv . obviously)
(right_triangle' : (g ◁ unit) ≫ (α_ g f g).inv ≫ (counit ▷ g) =
  (ρ_ g).hom ≫ (λ_ g).inv . obviously)

localized "infix ` ⊣ `:15 := adjunction" in bicategory

restate_axiom adjunction.left_triangle'
restate_axiom adjunction.right_triangle'
attribute [simp, reassoc] adjunction.left_triangle adjunction.right_triangle

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
    (g₁ ◁ (ρ_ _).hom) ≫ (g₁ ◁ adj₂.unit) ≫ (α_ g₁ f g₂).inv ≫ (adj₁.counit ▷ g₂) ≫ (λ_ g₂).hom ≫
      (ρ_ g₂).inv ≫ (g₂ ◁ adj₁.unit) ≫ (α_ g₂ f g₁).inv ≫ (adj₂.counit ▷ g₁) ≫ ((λ_ _).inv ▷ g₁)
    =
    (α_ _ _ _).inv ≫ ((g₁ ◁ adj₂.unit) ▷ _) ≫ ((α_ g₁ f g₂).inv ▷ _) ≫
      ((adj₁.counit ▷ g₂) ▷ _) ≫ (α_ _ _ _).hom ≫ (_ ◁ (g₂ ◁ adj₁.unit)) ≫
        (_ ◁ (α_ g₂ f g₁).inv) ≫ (_ ◁ (adj₂.counit ▷ g₁)) ≫ (α_ _ _ _).inv : _
    ... =
    (g₁ ◁ (ρ_ _).hom) ≫ (g₁ ◁ adj₁.unit) ≫ (g₁ ◁ (((λ_ f).inv ≫ (adj₂.unit ▷ f) ≫
      (α_ _ _ _).hom ≫ (f ◁ adj₂.counit) ≫ (ρ_ f).hom) ▷ g₁)) ≫ (α_ _ _ _).inv ≫
        (adj₁.counit ▷ g₁) ≫ ((λ_ _).inv ▷ g₁) : _
    ... =
    (g₁ ◁ (ρ_ _).hom) ≫ (ρ_ g₁).hom ≫ (λ_ g₁).inv ≫ ((λ_ _).inv ▷ g₁) : _,
  { simp_rw [←whisker_left_comp_assoc, ←right_unitor_naturality, whisker_left_comp_assoc,
      ←whisker_right_comp, left_unitor_inv_naturality, whisker_right_comp, right_unitor_comp,
      whisker_left_comp, left_unitor_comp_inv, whisker_right_comp, assoc,
      ←associator_inv_naturality_left_assoc, associator_inv_naturality_right_assoc,
      whisker_exchange_assoc, left_unitor_right_unitor_inv_assoc, hom_inv_whisker_right_assoc,
      hom_inv_whisker_left_assoc, ←associator_inv_naturality_right_assoc,
      associator_naturality_left_assoc, ←associator_inv_naturality_middle_assoc,
      pentagon_inv_inv_hom_hom_inv_assoc,
      associator_inv_naturality_middle, pentagon_inv_inv_hom_inv_inv_assoc] },
  { apply (cancel_epi (g₁ ◁ (ρ_ (𝟙 a)).inv)).1,
    apply (cancel_mono ((λ_ (𝟙 b)).hom ▷ g₁)).1,
    simp_rw [associator_naturality_left_assoc, ←associator_inv_naturality_middle_assoc,
      pentagon_inv_inv_hom_hom_inv_assoc, ←whisker_exchange_assoc,
      ←associator_inv_naturality_right_assoc,
      associator_inv_naturality_left, ←pentagon_inv_assoc, ←whisker_left_comp_assoc g₁,
      associator_inv_naturality_middle, ←associator_naturality_right_assoc,
      pentagon_hom_inv_inv_inv_hom_assoc, ←whisker_exchange_assoc,
      associator_inv_naturality_left_assoc, iso.inv_hom_id_assoc, ←unitors_inv_equal,
      ←left_unitor_inv_naturality_assoc, left_unitor_comp_inv_assoc, iso.hom_inv_id_assoc,
      whisker_right_comp, whisker_left_comp_assoc, associator_inv_naturality_middle_assoc g₁,
      ←whisker_right_comp, unitors_inv_equal, right_unitor_inv_naturality,
      right_unitor_comp_inv_assoc, hom_inv_whisker_left_assoc] },
  { simp_rw [adjunction.left_triangle_assoc, iso.inv_hom_id_assoc, iso.inv_hom_id,
      whisker_right_id, whisker_left_id, id_comp, adjunction.right_triangle_assoc] }
end

def right_adjoint_uniq {f : a ⟶ b} {g₁ g₂ : b ⟶ a}
  (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) : g₁ ≅ g₂ :=
{ hom := (ρ_ g₁).inv ≫ (g₁ ◁ adj₂.unit) ≫ (α_ g₁ f g₂).inv ≫ (adj₁.counit ▷ g₂) ≫ (λ_ g₂).hom,
  inv := (ρ_ g₂).inv ≫ (g₂ ◁ adj₁.unit) ≫ (α_ g₂ f g₁).inv ≫ (adj₂.counit ▷ g₁) ≫ (λ_ g₁).hom,
  hom_inv_id' := right_adjoint_uniq_aux adj₁ adj₂,
  inv_hom_id' := right_adjoint_uniq_aux adj₂ adj₁ }

end bicategory

end category_theory
