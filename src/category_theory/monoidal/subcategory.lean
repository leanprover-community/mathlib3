/-
Copyright (c) 2022 Antoine Labelle. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Labelle
-/
import category_theory.monoidal.braided
import category_theory.concrete_category.basic

/-!
# Full monoidal subcategories

Given a monidal category `C` and a monoidal predicate on `C`, that is a function `P : C → Prop`
closed under `𝟙_` and `⊗`, we can put a monoidal structure on `{X : C // P X}` (the category
structure is defined in `category_theory.full_subcategory`).

When `C` is also braided/symmetric, the full monoidal subcategory also inherits the
braided/symmetric structure.
-/

universes u v

namespace category_theory

namespace monoidal_category

open iso

variables (C : Type u) [category.{v} C] [monoidal_category C]

/--
A property of objects of a monoidal category `C` which is closed under `𝟙_` and `⊗`.
-/
@[nolint has_inhabited_instance]
structure monoidal_predicate :=
  (P : C → Prop)
  (h_id : P (𝟙_ C))
  (h_tensor : ∀ {X Y}, P X → P Y → P (X ⊗ Y))

variables {C} (p : monoidal_predicate C)

/--
`full_monoidal_subcategory p`, where `p : monoidal_predicate C`, is a typeclass synonym for the full
subcategory `{X : C // p.P X}`, which provides a monoidal structure induced by that of `C`.
-/
@[nolint has_inhabited_instance, derive category]
def full_monoidal_subcategory := {X : C // p.P X}

instance full_monoidal_subcategory.concrete_category [concrete_category C] :
  concrete_category (full_monoidal_subcategory p) := full_subcategory.concrete_category p.P
instance full_subcategory.has_forget₂ [concrete_category C] :
  has_forget₂ (full_monoidal_subcategory p) C := full_subcategory.has_forget₂ p.P

/--
The monoidal structure on `full_monoidal_subcategory p`
-/
instance full_monoidal_subcategory.monoidal : monoidal_category (full_monoidal_subcategory p) :=
{ tensor_obj := λ X Y, ⟨X.1 ⊗ Y.1, p.h_tensor X.2 Y.2⟩,
  tensor_hom := λ X₁ Y₁ X₂ Y₂ f g, by { change X₁.1 ⊗ X₂.1 ⟶ Y₁.1 ⊗ Y₂.1,
    change X₁.1 ⟶ Y₁.1 at f, change X₂.1 ⟶ Y₂.1 at g, exact f ⊗ g },
  tensor_unit := ⟨𝟙_ C, p.h_id⟩,
  associator := λ X Y Z,
    ⟨(α_ X.1 Y.1 Z.1).hom, (α_ X.1 Y.1 Z.1).inv,
     hom_inv_id (α_ X.1 Y.1 Z.1), inv_hom_id (α_ X.1 Y.1 Z.1)⟩,
  left_unitor := λ X, ⟨(λ_ X.1).hom, (λ_ X.1).inv, hom_inv_id (λ_ X.1), inv_hom_id (λ_ X.1)⟩,
  right_unitor := λ X, ⟨(ρ_ X.1).hom, (ρ_ X.1).inv, hom_inv_id (ρ_ X.1), inv_hom_id (ρ_ X.1)⟩,
  tensor_id' := λ X Y, tensor_id X.1 Y.1,
  tensor_comp' := λ X₁ Y₁ Z₁ X₂ Y₂ Z₂ f₁ f₂ g₁ g₂, tensor_comp f₁ f₂ g₁ g₂,
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃, associator_naturality f₁ f₂ f₃,
  left_unitor_naturality' := λ X Y f, left_unitor_naturality f,
  right_unitor_naturality' := λ X Y f, right_unitor_naturality f,
  pentagon' := λ W X Y Z, pentagon W.1 X.1 Y.1 Z.1,
  triangle' := λ X Y, triangle X.1 Y.1 }

/--
The forgetful monoidal functor from a full monoidal subcategory into the original category
("forgetting" the condition).
-/
@[simps]
def full_monoidal_subcategory_inclusion : monoidal_functor (full_monoidal_subcategory p) C :=
{ to_functor := full_subcategory_inclusion p.P,
  ε := 𝟙 _,
  μ := λ X Y, 𝟙 _ }

instance full_monoidal_subcategory.full :
  full (full_monoidal_subcategory_inclusion p).to_functor := full_subcategory.full p.P
instance full_monoidal_subcategory.faithful :
  faithful (full_monoidal_subcategory_inclusion p).to_functor := full_subcategory.faithful p.P

variables {p} {p' : monoidal_predicate C}

/-- An implication of predicates `p.P → p'.P` induces a monoidal functor between full monoidal
subcategories. -/
@[simps]
def full_monoidal_subcategory.map (h : ∀ ⦃X⦄, p.P X → p'.P X) :
  monoidal_functor (full_monoidal_subcategory p) (full_monoidal_subcategory p')  :=
{ to_functor := full_subcategory.map h,
  ε := 𝟙 _,
  μ := λ X Y, 𝟙 _ }

instance full_monoidal_subcategory.map_full (h : ∀ ⦃X⦄, p.P X → p'.P X) :
  full (full_monoidal_subcategory.map h).to_functor := { preimage := λ X Y f, f }
instance full_monoidal_subcategory.map_faithful (h : ∀ ⦃X⦄, p.P X → p'.P X) :
  faithful (full_monoidal_subcategory.map h).to_functor := {}

section braided

variables (p) [braided_category C]

/--
The monoidal structure on `full_monoidal_subcategory p` inherited by the braided structure on `C`.
-/
instance full_braided_subcategory : braided_category (full_monoidal_subcategory p) :=
braided_category_of_faithful (full_monoidal_subcategory_inclusion p)
  (λ X Y, ⟨(β_ X.1 Y.1).hom, (β_ X.1 Y.1).inv, (β_ X.1 Y.1).hom_inv_id, (β_ X.1 Y.1).inv_hom_id⟩)
  (λ X Y, by tidy)

/--
The forgetful braided functor from a full braided subcategory into the original category
("forgetting" the condition).
-/
@[simps]
def full_braided_subcategory_inclusion : braided_functor (full_monoidal_subcategory p) C :=
{ to_monoidal_functor := full_monoidal_subcategory_inclusion p,
  braided' := λ X Y, by { rw [is_iso.eq_inv_comp], tidy }  }

instance full_braided_subcategory.full :
  full (full_braided_subcategory_inclusion p).to_functor := full_monoidal_subcategory.full p
instance full_braided_subcategory.faithful :
  faithful (full_braided_subcategory_inclusion p).to_functor := full_monoidal_subcategory.faithful p

variables {p}

/-- An implication of predicates `p.P → p'.P` induces a braided functor between full braided
subcategories. -/
@[simps]
def full_braided_subcategory.map (h : ∀ ⦃X⦄, p.P X → p'.P X) :
  braided_functor (full_monoidal_subcategory p) (full_monoidal_subcategory p')  :=
{ to_monoidal_functor := full_monoidal_subcategory.map h,
  braided' := λ X Y, by { rw [is_iso.eq_inv_comp], tidy }  }

instance full_braided_subcategory.map_full (h : ∀ ⦃X⦄, p.P X → p'.P X) :
  full (full_braided_subcategory.map h).to_functor := full_monoidal_subcategory.map_full h
instance full_braided_subcategory.map_faithful (h : ∀ ⦃X⦄, p.P X → p'.P X) :
  faithful (full_braided_subcategory.map h).to_functor := full_monoidal_subcategory.map_faithful h

end braided

section symmetric

variables (p) [symmetric_category C]

instance full_symmetric_subcategory : symmetric_category (full_monoidal_subcategory p) :=
symmetric_category_of_faithful (full_braided_subcategory_inclusion p)

end symmetric

end monoidal_category

end category_theory
