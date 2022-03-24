/-
Copyright (c) 2022 Yuma Mizuno. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuma Mizuno
-/
import tactic.coherence

namespace category_theory

namespace bicategory

open category
open_locale bicategory

universes w₁ w₂ v₁ v₂ u₁ u₂

variables {B : Type u₁} [bicategory.{w₁ v₁} B] {a b c : B}

/-- Adjunction between two 1-morphisms. -/
@[nolint has_inhabited_instance]
structure adjunction (f : a ⟶ b) (g : b ⟶ a) :=
(unit   : 𝟙 a ⟶ f ≫ g)
(counit : g ≫ f ⟶ 𝟙 b)
(left_triangle'  : unit ▷ f ≫ (α_ f g f).hom ≫ f ◁ counit = (λ_ f).hom ≫ (ρ_ f).inv . obviously)
(right_triangle' : g ◁ unit ≫ (α_ g f g).inv ≫ counit ▷ g = (ρ_ g).hom ≫ (λ_ g).inv . obviously)

localized "infix ` ⊣ `:15 := adjunction" in bicategory

namespace adjunction

restate_axiom left_triangle'
restate_axiom right_triangle'
attribute [simp, reassoc] left_triangle right_triangle

local attribute [-simp] id_whisker_left whisker_right_id

lemma right_adjoint_uniq_aux {f : a ⟶ b} {g₁ g₂ : b ⟶ a} (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) :
  ((ρ_ g₁).inv ≫ g₁ ◁ adj₂.unit ≫ (α_ g₁ f g₂).inv ≫ adj₁.counit ▷ g₂ ≫ (λ_ g₂).hom) ≫
    (ρ_ g₂).inv ≫ g₂ ◁ adj₁.unit ≫ (α_ g₂ f g₁).inv ≫ adj₂.counit ▷ g₁ ≫ (λ_ g₁).hom =
      𝟙 g₁ :=
begin
  rw [←cancel_mono (λ_ g₁).inv, ←cancel_mono $ (λ_ (𝟙 b)).inv ▷ g₁],
  calc _  = (ρ_ g₁).inv ≫ (ρ_ g₁).hom ≫ (λ_ g₁).inv ≫ _ ◁ (λ_ g₁).inv ≫ (α_ _ _ _).inv : _
  ...     = _ : by coherence,
  simp_rw [assoc, iso.hom_inv_id_assoc, right_unitor_inv_naturality_assoc, ←whisker_exchange_assoc,
    associator_inv_naturality_left_assoc, ←comp_whisker_right _ _ g₁, left_unitor_inv_naturality,
    left_unitor_comp_inv_assoc, hom_inv_whisker_right_assoc, associator_naturality_left_assoc,
    ←whisker_exchange, comp_whisker_left_assoc, pentagon_inv_hom_hom_hom_hom_assoc,
    associator_naturality_middle_assoc, ←whisker_left_comp_assoc g₁, left_triangle,
    ←right_triangle_assoc adj₁, ←whisker_exchange_assoc, associator_inv_naturality_left],
  congr' 2, simp_rw [comp_whisker_right, ←assoc], congr' 1, coherence
end

lemma left_adjoint_uniq_aux {f₁ f₂ : a ⟶ b} {g : b ⟶ a} (adj₁ : f₁ ⊣ g) (adj₂ : f₂ ⊣ g) :
  ((λ_ f₁).inv ≫ adj₂.unit ▷ f₁ ≫ (α_ f₂ g f₁).hom ≫ f₂ ◁ adj₁.counit ≫ (ρ_ f₂).hom) ≫
    (λ_ f₂).inv ≫ adj₁.unit ▷ f₂ ≫ (α_ f₁ g f₂).hom ≫ f₁ ◁ adj₂.counit ≫ (ρ_ f₁).hom =
      𝟙 f₁ :=
begin
  rw [←cancel_mono (ρ_ f₁).inv, ←cancel_mono $ f₁ ◁ (ρ_ (𝟙 b)).inv],
  calc _  = (λ_ f₁).inv ≫ (λ_ f₁).hom ≫ (ρ_ f₁).inv ≫ (ρ_ f₁).inv ▷ _ ≫ (α_ _ _ _).hom : _
  ...     = _ : by coherence,
  simp_rw [assoc, iso.hom_inv_id_assoc, left_unitor_inv_naturality_assoc, whisker_exchange_assoc,
    associator_naturality_right_assoc, ←whisker_left_comp f₁, right_unitor_inv_naturality,
    right_unitor_comp_inv_assoc, hom_inv_whisker_left_assoc, associator_inv_naturality_right_assoc,
    whisker_exchange, whisker_right_comp_assoc, pentagon_hom_inv_inv_inv_inv_assoc,
    associator_inv_naturality_middle_assoc, ←comp_whisker_right_assoc _ _ f₁, right_triangle,
    ←left_triangle_assoc adj₁, whisker_exchange_assoc, associator_naturality_right],
  congr' 2, simp_rw [whisker_left_comp, ←assoc], congr' 1, coherence
end

/-- If `g₁` and `g₂` are both right adjoint to `f`, then they are isomorphic. -/
def right_adjoint_uniq {f : a ⟶ b} {g₁ g₂ : b ⟶ a}
  (adj₁ : f ⊣ g₁) (adj₂ : f ⊣ g₂) : g₁ ≅ g₂ :=
{ hom := (ρ_ g₁).inv ≫ g₁ ◁ adj₂.unit ≫ (α_ g₁ f g₂).inv ≫ adj₁.counit ▷ g₂ ≫ (λ_ g₂).hom,
  inv := (ρ_ g₂).inv ≫ g₂ ◁ adj₁.unit ≫ (α_ g₂ f g₁).inv ≫ adj₂.counit ▷ g₁ ≫ (λ_ g₁).hom,
  hom_inv_id' := right_adjoint_uniq_aux adj₁ adj₂,
  inv_hom_id' := right_adjoint_uniq_aux adj₂ adj₁ }

/-- If `f₁` and `f₂` are both left adjoint to `g`, then they are isomorphic. -/
def left_adjoint_uniq {f₁ f₂ : a ⟶ b} {g : b ⟶ a}
  (adj₁ : f₁ ⊣ g) (adj₂ : f₂ ⊣ g) : f₁ ≅ f₂ :=
{ hom := (λ_ f₁).inv ≫ adj₂.unit ▷ f₁ ≫ (α_ f₂ g f₁).hom ≫ f₂ ◁ adj₁.counit ≫ (ρ_ f₂).hom,
  inv := (λ_ f₂).inv ≫ adj₁.unit ▷ f₂ ≫ (α_ f₁ g f₂).hom ≫ f₁ ◁ adj₂.counit ≫ (ρ_ f₁).hom,
  hom_inv_id' := left_adjoint_uniq_aux adj₁ adj₂,
  inv_hom_id' := left_adjoint_uniq_aux adj₂ adj₁ }

/-- Adjunction between identities. -/
def id (a : B) : 𝟙 a ⊣ 𝟙 a :=
{ unit            := (ρ_ _).inv,
  counit          := (ρ_ _).hom,
  left_triangle'  := by coherence,
  right_triangle' := by coherence }

section composition
variables {f₁ : a ⟶ b} {g₁ : b ⟶ a} {f₂ : b ⟶ c} {g₂ : c ⟶ b}

/-- Auxiliary definition for `adjunction.comp`. -/
def comp_unit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : 𝟙 a ⟶ (f₁ ≫ f₂) ≫ g₂ ≫ g₁ :=
(λ_ (𝟙 a)).inv ≫
  𝟙 a ◁ adj₁.unit ≫ (α_ (𝟙 a) f₁ g₁).inv ≫
    (adj₁.unit ▷ f₁ ≫ (α_ f₁ g₁ f₁).hom ≫ f₁ ◁ adj₁.counit) ▷ g₁ ≫ (α_ f₁ (𝟙 b) g₁).hom ≫
      f₁ ◁ adj₂.unit ▷ g₁ ≫ f₁ ◁ (α_ f₂ g₂ g₁).hom ≫ (α_ f₁ f₂ (g₂ ≫ g₁)).inv

lemma comp_unit_eq (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
  comp_unit adj₁ adj₂ = (λ_ (𝟙 a)).inv ≫
    𝟙 a ◁ adj₁.unit ≫ (α_ (𝟙 a) f₁ g₁).inv ≫
      (adj₁.unit ▷ f₁ ≫ (α_ f₁ g₁ f₁).hom ≫ f₁ ◁ adj₁.counit) ▷ g₁ ≫ (α_ f₁ (𝟙 b) g₁).hom ≫
        f₁ ◁ adj₂.unit ▷ g₁ ≫ f₁ ◁ (α_ f₂ g₂ g₁).hom ≫ (α_ f₁ f₂ (g₂ ≫ g₁)).inv :=
rfl

/-- Another expression for `comp_unit`. -/
lemma comp_unit_eq' (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
  comp_unit adj₁ adj₂ = (ρ_ (𝟙 a)).inv ≫
    adj₁.unit ▷ 𝟙 a ≫ (α_ f₁ g₁ (𝟙 a)).hom ≫
      f₁ ◁ (g₁ ◁ adj₁.unit ≫ (α_ g₁ f₁ g₁).inv ≫ adj₁.counit ▷ g₁) ≫
        f₁ ◁ adj₂.unit ▷ g₁ ≫ f₁ ◁ (α_ f₂ g₂ g₁).hom ≫ (α_ f₁ f₂ (g₂ ≫ g₁)).inv :=
begin
  rw [comp_unit_eq, ←left_unitor_inv_naturality_assoc, ←right_unitor_inv_naturality_assoc,
    left_triangle, right_triangle],
  congr' 1, simp_rw ←assoc, congr' 3,
  coherence
end

/-- Auxiliary definition for `adjunction.comp`. -/
def comp_counit (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (g₂ ≫ g₁) ≫ f₁ ≫ f₂ ⟶ 𝟙 c :=
(α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫ g₂ ◁ (α_ g₁ f₁ f₂).inv ≫
  g₂ ◁ adj₁.counit ▷ f₂ ≫
    g₂ ◁ (adj₂.unit ▷ f₂ ≫ (α_ f₂ g₂ f₂).hom ≫ f₂ ◁ adj₂.counit) ≫ (α_ g₂ f₂ (𝟙 c)).inv ≫
      adj₂.counit ▷ 𝟙 c ≫ (ρ_ (𝟙 c)).hom

lemma comp_counit_eq (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
  comp_counit adj₁ adj₂ = (α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫ g₂ ◁ (α_ g₁ f₁ f₂).inv ≫
    g₂ ◁ adj₁.counit ▷ f₂ ≫
      g₂ ◁ (adj₂.unit ▷ f₂ ≫ (α_ f₂ g₂ f₂).hom ≫ f₂ ◁ adj₂.counit) ≫ (α_ g₂ f₂ (𝟙 c)).inv ≫
        adj₂.counit ▷ 𝟙 c ≫ (ρ_ (𝟙 c)).hom :=
rfl

/-- Another expression for `comp_counit`. -/
lemma comp_counit_eq' (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
  comp_counit adj₁ adj₂ = (α_ g₂ g₁ (f₁ ≫ f₂)).hom ≫ g₂ ◁ (α_ g₁ f₁ f₂).inv ≫
    g₂ ◁ adj₁.counit ▷ f₂ ≫ (α_ g₂ (𝟙 b) f₂).inv ≫
      (g₂ ◁ adj₂.unit ≫ (α_ g₂ f₂ g₂).inv ≫ adj₂.counit ▷ g₂) ▷ f₂ ≫ (α_ (𝟙 c) g₂ f₂).hom ≫
        𝟙 c ◁ adj₂.counit ≫ (λ_ (𝟙 c)).hom :=
begin
  rw [comp_counit_eq, left_unitor_naturality, right_unitor_naturality,
    left_triangle, right_triangle],
  congr' 3, simp_rw ←assoc, congr' 1,
  coherence
end

lemma comp_left_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
  adj₁.comp_unit adj₂ ▷ (f₁ ≫ f₂) ≫ (α_ (f₁ ≫ f₂) (g₂ ≫ g₁) (f₁ ≫ f₂)).hom ≫
    (f₁ ≫ f₂) ◁ adj₁.comp_counit adj₂ =
      (λ_ (f₁ ≫ f₂)).hom ≫ (ρ_ (f₁ ≫ f₂)).inv :=
begin
  calc _ =
  (λ_ _).inv ▷ _ ≫ (_ ◁ adj₁.unit) ▷ _ ≫ (α_ _ _ _).inv ▷ _ ≫ (α_ _ _ _).hom ≫
    ((λ_ _).hom ≫ (ρ_ f₁).inv ≫ f₁ ◁ adj₂.unit) ▷ (g₁ ≫ f₁ ≫ f₂) ≫
      (f₁ ≫ f₂ ≫ g₂) ◁ ((α_ _ _ _).inv ≫ adj₁.counit ▷ f₂ ≫ (λ_ f₂).hom ≫ (ρ_ f₂).inv) ≫
        (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).hom ≫ (α_ _ _ _).inv ≫ _ ◁ (α_ _ _ _).inv ≫
          (α_ _ _ _).hom ≫ _ ◁ _ ◁ adj₂.counit ▷ _ ≫ (α_ _ _ _).inv ≫ _ ◁ (ρ_ _).hom : _
  ... = _ : _,
  { simp_rw [comp_unit_eq, comp_counit_eq, left_triangle, ←associator_naturality_middle_assoc,
      comp_whisker_right, whisker_left_comp, assoc, ←whisker_right_comp_conj_assoc _ g₁,
      comp_whisker_left_assoc f₁ f₂, iso.inv_hom_id_assoc, ←whisker_left_comp_assoc f₁,
      ←comp_whisker_left_conj_assoc f₂, iso.hom_inv_id_assoc, whisker_left_comp,
      ←comp_whisker_left_conj_assoc f₁, iso.hom_inv_id_assoc],
    congr' 7, simp_rw ←assoc, congr' 12, coherence },
  { simp_rw [←whisker_exchange_assoc, whisker_left_comp, comp_whisker_right, assoc,
      comp_whisker_left_assoc (𝟙 a), iso.inv_hom_id_assoc, pentagon_inv_hom_hom_hom_hom_assoc,
      associator_naturality_middle_assoc, ←whisker_left_comp_assoc (𝟙 a),
      whisker_right_comp_assoc adj₁.unit, pentagon_hom_hom_inv_hom_hom_assoc,
      ←associator_naturality_middle_assoc _ adj₁.counit, ←comp_whisker_right_assoc _ _ f₂,
      left_triangle, comp_whisker_left_conj_assoc, ←whisker_left_comp_assoc f₁,
      whisker_right_comp_assoc adj₂.unit, pentagon_hom_hom_inv_hom_hom_assoc,
      ←associator_naturality_middle, ←comp_whisker_right_assoc _ _ (𝟙 c), left_triangle],
    coherence }
end

lemma comp_right_triangle_aux (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) :
  (g₂ ≫ g₁) ◁ adj₁.comp_unit adj₂ ≫ (α_ (g₂ ≫ g₁) (f₁ ≫ f₂) (g₂ ≫ g₁)).inv ≫
    adj₁.comp_counit adj₂ ▷ (g₂ ≫ g₁) = (ρ_ (g₂ ≫ g₁)).hom ≫ (λ_ (g₂ ≫ g₁)).inv :=
begin
  calc _ =
  _ ◁ (ρ_ _).inv ≫ _ ◁ adj₁.unit ▷ _ ≫ _ ◁ (α_ _ _ _).hom ≫
    (α_ _ _ _).hom ≫ _ ◁ (α_ _ _ _).inv ≫ (α_ _ _ _).inv ≫
      (g₂ ≫ g₁ ≫ f₁) ◁ ((ρ_ g₁).hom ≫ (λ_ g₁).inv ≫ adj₂.unit ▷ g₁ ≫ (α_ _ _ _).hom) ≫
        (g₂ ◁ adj₁.counit ≫ (ρ_ g₂).hom ≫ (λ_ g₂).inv) ▷ (f₂ ≫ g₂ ≫ g₁) ≫ (α_ _ _ _).inv ≫
          (α_ _ _ _).hom ▷ _ ≫ (_ ◁ adj₂.counit) ▷ _ ≫ (λ_ (𝟙 c)).hom ▷ _ : _
  ... = _ : _,
  { simp_rw [comp_unit_eq', comp_counit_eq', right_triangle,
      associator_inv_naturality_middle_assoc,
      comp_whisker_right, whisker_left_comp, assoc, ←whisker_right_comp_conj_assoc _ f₂,
      comp_whisker_left_assoc g₂ g₁, iso.inv_hom_id_assoc, ←whisker_left_comp_assoc g₂,
      ←comp_whisker_left_conj_assoc g₁, iso.hom_inv_id_assoc, whisker_left_comp,
      ←comp_whisker_left_conj_assoc g₂, assoc, iso.hom_inv_id_assoc],
    congr' 10, simp_rw ←assoc, congr' 6, convert id_comp _, coherence },
  { simp_rw [whisker_exchange_assoc, whisker_left_comp, comp_whisker_right, assoc,
      comp_whisker_left_assoc (𝟙 c), iso.inv_hom_id_assoc, pentagon_inv_inv_hom_inv_inv_assoc,
      ←associator_inv_naturality_middle_assoc, ←whisker_left_comp_assoc (𝟙 c),
      whisker_right_comp adj₂.counit, pentagon_hom_inv_inv_inv_inv_assoc,
      associator_inv_naturality_middle_assoc _ adj₂.unit, ←comp_whisker_right_assoc _ _ g₁,
      right_triangle, comp_whisker_left_assoc g₂, iso.inv_hom_id_assoc,
      ←whisker_left_comp_assoc g₂, whisker_right_comp adj₁.counit,
      pentagon_hom_inv_inv_inv_inv_assoc, associator_inv_naturality_middle_assoc,
      ←comp_whisker_right_assoc _ _ (𝟙 a), right_triangle],
    coherence }
end

/-- Composition of adjunctions. -/
def comp (adj₁ : f₁ ⊣ g₁) (adj₂ : f₂ ⊣ g₂) : (f₁ ≫ f₂ ⊣ g₂ ≫ g₁) :=
{ unit            := comp_unit adj₁ adj₂,
  counit          := comp_counit adj₁ adj₂,
  left_triangle'  := by apply comp_left_triangle_aux,
  right_triangle' := by apply comp_right_triangle_aux }

end composition

end adjunction

end bicategory

end category_theory
