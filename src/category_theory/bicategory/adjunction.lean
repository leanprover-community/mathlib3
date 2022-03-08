/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import category_theory.bicategory.basic

namespace category_theory

namespace bicategory

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

@[reassoc] lemma left_unitor_right_unitor_inv (f : a ⟶ b) :
(λ_ f).hom ≫ (ρ_ f).inv
= (𝟙 a ◁ (ρ_ f).inv) ≫ (α_ (𝟙 a) f (𝟙 b)).inv ≫ ((λ_ f).hom ▷ 𝟙 b) :=
begin
  apply (cancel_mono (((λ_ f).inv ▷ 𝟙 b) ≫ (α_ (𝟙 a) f (𝟙 b)).hom ≫ (λ_ (f ≫ 𝟙 b)).hom)).1,
  simp_rw [category.assoc, ←left_unitor_naturality, left_unitor_comp, iso.hom_inv_id_assoc,
    inv_hom_whisker_right, category.comp_id]
end

lemma right_adjoint_uniq_aux {f : a ⟶ b} {g g' : b ⟶ a} (adj₁ : f ⊣ g) (adj₂ : f ⊣ g') :
  ((ρ_ g).inv ≫ (g ◁ adj₂.unit) ≫ (α_ g f g').inv ≫ (adj₁.counit ▷ g') ≫ (λ_ g').hom) ≫
    (ρ_ g').inv ≫ (g' ◁ adj₁.unit) ≫ (α_ g' f g).inv ≫ (adj₂.counit ▷ g) ≫ (λ_ g).hom =
      𝟙 g :=
begin
  apply (cancel_epi (ρ_ g).hom).1,
  apply (cancel_mono (λ_ g).inv).1,
  apply (cancel_epi (g ◁ (ρ_ (𝟙 a)).hom)).1,
  apply (cancel_mono ((λ_ (𝟙 b)).inv ▷ g)).1,
  simp only [iso.hom_inv_id_assoc, category.assoc, category.comp_id],
  calc
    (g ◁ (ρ_ _).hom) ≫ (g ◁ adj₂.unit) ≫ (α_ g f g').inv ≫ (adj₁.counit ▷ g') ≫ (λ_ g').hom ≫
      (ρ_ g').inv ≫ (g' ◁ adj₁.unit) ≫ (α_ g' f g).inv ≫ (adj₂.counit ▷ g) ≫ ((λ_ _).inv ▷ g)
    =
    (α_ _ _ _).inv ≫ ((g ◁ adj₂.unit) ▷ _) ≫ ((α_ g f g').inv ▷ _) ≫
      ((adj₁.counit ▷ g') ▷ _) ≫ (α_ _ _ _).hom ≫ (_ ◁ (g' ◁ adj₁.unit)) ≫
        (_ ◁ (α_ g' f g).inv) ≫ (_ ◁ (adj₂.counit ▷ g)) ≫ (α_ _ _ _).inv : _
    ... =
    (g ◁ (ρ_ _).hom) ≫ (g ◁ adj₁.unit) ≫ (g ◁ (((λ_ f).inv ≫ (adj₂.unit ▷ f) ≫ (α_ _ _ _).hom ≫
      (f ◁ adj₂.counit) ≫ (ρ_ f).hom) ▷ g)) ≫ (α_ _ _ _).inv ≫ (adj₁.counit ▷ g) ≫
        ((λ_ _).inv ▷ g) : _
    ... = (g ◁ (ρ_ _).hom) ≫ (ρ_ g).hom ≫ (λ_ g).inv ≫ ((λ_ _).inv ▷ g) : _,
  { rw ←whisker_left_comp_assoc,
    rw ←right_unitor_naturality,
    rw whisker_left_comp_assoc,
    rw ←whisker_right_comp,
    rw left_unitor_inv_naturality,
    rw whisker_right_comp,
    simp_rw [right_unitor_comp, whisker_left_comp, left_unitor_comp_inv, whisker_right_comp,
      category.assoc],
    rw ←associator_inv_naturality_left_assoc,
    rw whisker_exchange_assoc,
    rw associator_inv_naturality_right_assoc,
    rw whisker_exchange_assoc,
    rw left_unitor_right_unitor_inv_assoc,
    rw [hom_inv_whisker_right_assoc, hom_inv_whisker_left_assoc],
    rw ←associator_inv_naturality_right_assoc,
    rw associator_naturality_left_assoc,
    rw ←associator_inv_naturality_middle_assoc,
    rw pentagon_inv_inv_hom_hom_inv_assoc,
    rw associator_inv_naturality_middle,
    rw pentagon_inv_inv_hom_inv_inv_assoc },
  { rw associator_naturality_left_assoc,
    rw ←associator_inv_naturality_middle_assoc,
    rw pentagon_inv_inv_hom_hom_inv_assoc,
    simp_rw [←whisker_exchange_assoc, ←associator_inv_naturality_right_assoc],
    rw associator_inv_naturality_left,
    rw ←pentagon_inv_assoc,
    simp_rw [←whisker_left_comp_assoc g],
    rw associator_inv_naturality_middle,
    rw ←associator_naturality_right_assoc,
    rw pentagon_hom_inv_inv_inv_hom_assoc,
    rw ←whisker_exchange_assoc,
    rw associator_inv_naturality_left_assoc,
    apply (cancel_epi (g ◁ (ρ_ (𝟙 a)).inv)).1,
    simp_rw [←whisker_left_comp_assoc, iso.inv_hom_id_assoc, ←unitors_inv_equal,
      ←left_unitor_inv_naturality_assoc, left_unitor_comp_inv_assoc, iso.hom_inv_id_assoc,
      whisker_right_comp, whisker_left_comp_assoc],
    congr' 5,
    rw associator_inv_naturality_middle_assoc,
    congr' 1,
    simp_rw [←whisker_right_comp],
    congr' 1,
    apply (cancel_mono ((λ_ (𝟙 b)).hom)).1,
    simp_rw [category.assoc, iso.inv_hom_id, category.comp_id, unitors_equal,
      right_unitor_naturality, right_unitor_comp_assoc, iso.inv_hom_id_assoc] },
  { simp_rw [adjunction.left_triangle_assoc,
      iso.inv_hom_id_assoc, iso.inv_hom_id, whisker_right_id, whisker_left_id, category.id_comp,
      adjunction.right_triangle_assoc] }
end

def right_adjoint_uniq {f : a ⟶ b} {g g' : b ⟶ a}
  (adj₁ : f ⊣ g) (adj₂ : f ⊣ g') : g ≅ g' :=
{ hom := (ρ_ g).inv ≫ (g ◁ adj₂.unit) ≫ (α_ _ _ _).inv ≫ (adj₁.counit ▷ g') ≫ (λ_ g').hom,
  inv := (ρ_ g').inv ≫ (g' ◁ adj₁.unit) ≫ (α_ _ _ _).inv ≫ (adj₂.counit ▷ g) ≫ (λ_ g).hom,
  hom_inv_id' := right_adjoint_uniq_aux adj₁ adj₂,
  inv_hom_id' := right_adjoint_uniq_aux adj₂ adj₁ }

end bicategory

end category_theory
