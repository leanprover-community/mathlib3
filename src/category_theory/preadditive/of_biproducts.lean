/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.limits.shapes.biproducts
import group_theory.eckmann_hilton

/-!
# Constructing a semiadditive structure from binary biproducts

We show that any category with zero morphisms and binary biproducts is enriched over the category
of commutative monoids.

-/

noncomputable theory

universes v u

open category_theory
open category_theory.limits

namespace category_theory.semiadditive_of_binary_biproducts
variables {C : Type u} [category.{v} C] [has_zero_morphisms C] [has_binary_biproducts C]

section
variables (X Y : C)

/-- `f +ₗ g` is the composite `X ⟶ Y ⊞ Y ⟶ Y`, where the first map is `(f, g)` and the second map
    is `(𝟙 𝟙)`. -/
@[simp] def left_add (f g : X ⟶ Y) : X ⟶ Y :=
biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y)

/-- `f +ᵣ g` is the composite `X ⟶ X ⊞ X ⟶ Y`, where the first map is `(𝟙, 𝟙)` and the second map
    is `(f g)`. -/
@[simp] def right_add (f g : X ⟶ Y) : X ⟶ Y :=
biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g

local infixr ` +ₗ `:65 := left_add X Y
local infixr ` +ᵣ `:65 := right_add X Y

lemma is_unital_left_add : eckmann_hilton.is_unital (+ₗ) 0 :=
⟨⟨λ f, by simp [show biprod.lift (0 : X ⟶ Y) f = f ≫ biprod.inr, by ext; simp]⟩,
 ⟨λ f, by simp [show biprod.lift f (0 : X ⟶ Y) = f ≫ biprod.inl, by ext; simp]⟩⟩

lemma is_unital_right_add : eckmann_hilton.is_unital (+ᵣ) 0 :=
⟨⟨λ f, by simp [show biprod.desc (0 : X ⟶ Y) f = biprod.snd ≫ f, by ext; simp]⟩,
 ⟨λ f, by simp [show biprod.desc f (0 : X ⟶ Y) = biprod.fst ≫ f, by ext; simp]⟩⟩

lemma distrib (f g h k : X ⟶ Y) : (f +ᵣ g) +ₗ (h +ᵣ k) = (f +ₗ h) +ᵣ (g +ₗ k) :=
begin
  let diag : X ⊞ X ⟶ Y ⊞ Y := biprod.lift (biprod.desc f g) (biprod.desc h k),
  have hd₁ : biprod.inl ≫ diag = biprod.lift f h := by { ext; simp },
  have hd₂ : biprod.inr ≫ diag = biprod.lift g k := by { ext; simp },
  have h₁ : biprod.lift (f +ᵣ g) (h +ᵣ k) = biprod.lift (𝟙 X) (𝟙 X) ≫ diag := by { ext; simp },
  have h₂ : diag ≫ biprod.desc (𝟙 Y) (𝟙 Y) = biprod.desc (f +ₗ h) (g +ₗ k),
  { ext; simp [reassoc_of hd₁, reassoc_of hd₂] },
  rw [left_add, h₁, category.assoc, h₂, right_add]
end

/-- In a category with binary biproducts, the morphisms form a commutative monoid. -/
def add_comm_monoid_hom_of_has_binary_biproducts : add_comm_monoid (X ⟶ Y) :=
{ add := (+ᵣ),
  add_assoc := (eckmann_hilton.mul_assoc (is_unital_left_add X Y)
    (is_unital_right_add X Y) (distrib X Y)).assoc,
  zero := 0,
  zero_add := (is_unital_right_add X Y).left_id,
  add_zero := (is_unital_right_add X Y).right_id,
  add_comm := (eckmann_hilton.mul_comm (is_unital_left_add X Y)
    (is_unital_right_add X Y) (distrib  X Y)).comm }

end

section
variables {X Y Z : C}

local attribute [instance] add_comm_monoid_hom_of_has_binary_biproducts

lemma add_eq_right_addition (f g : X ⟶ Y) : f + g = biprod.lift (𝟙 X) (𝟙 X) ≫ biprod.desc f g :=
rfl

lemma add_eq_left_addition (f g : X ⟶ Y) : f + g = biprod.lift f g ≫ biprod.desc (𝟙 Y) (𝟙 Y) :=
congr_fun₂
  (eckmann_hilton.mul (is_unital_left_add X Y) (is_unital_right_add X Y) (distrib  X Y)).symm f g

lemma add_comp (f g : X ⟶ Y) (h : Y ⟶ Z) : (f + g) ≫ h = f ≫ h + g ≫ h :=
by { simp only [add_eq_right_addition, category.assoc], congr, ext; simp }

lemma comp_add (f : X ⟶ Y) (g h : Y ⟶ Z) : f ≫ (g + h) = f ≫ g + f ≫ h :=
by { simp only [add_eq_left_addition, ← category.assoc], congr, ext; simp }

end

end category_theory.semiadditive_of_binary_biproducts
