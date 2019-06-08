import category_theory.monoidal.functor
import category_theory.full_subcategory
import category_theory.eq_to_hom

universes v₁ u₁

open category_theory
open category_theory.monoidal_category

namespace category_theory

variables {C : Type u₁} [𝒞 : monoidal_category.{v₁} C]
include 𝒞

local notation `𝟙_` := tensor_unit
local notation `α_` := associator
local notation `λ_` := left_unitor
local notation `ρ_` := right_unitor

def tensor : list C → C
| [] := 𝟙_ C
| (X :: w) := X ⊗ (tensor w)

def tensorator : Π (w z : list C), (tensor w) ⊗ (tensor z) ≅ tensor (w ++ z)
| [] z := (λ_ _)
| (X :: w) z := (α_ _ _ _) ≪≫ (tensor_iso (iso.refl _) (tensorator w z))

def tensorator_congr_left {w w' : list C} (h : w = w') (z : list C) :
  tensorator w z =
    (tensor_iso (eq_to_iso (by { cases h, refl })) (iso.refl _)) ≪≫
    tensorator w' z ≪≫ eq_to_iso (by { cases h, refl }) :=
by { cases h, simp }

instance : category.{v₁} (list C) :=
{ hom := λ X Y, (tensor X) ⟶ (tensor Y),
  id := λ X, 𝟙 (tensor X),
  comp := λ X Y Z f g, f ≫ g, }

def unpack {X Y : list C} (f : X ⟶ Y) : tensor X ⟶ tensor Y := f
def pack {X Y : list C} (f : tensor X ⟶ tensor Y) : X ⟶ Y := f

@[simp] lemma unpack_id (X : list C) : unpack (𝟙 X) = 𝟙 (tensor X) := rfl
@[simp] lemma pack_id (X : list C) : pack (𝟙 (tensor X)) = 𝟙 X := rfl
-- @[simp] lemma unpack_comp (X Y Z : list C) (f : X ⟶ Y) (g : Y ⟶ Z) : unpack (f ≫ g) = unpack f ≫ unpack g := rfl
-- @[simp] lemma pack_comp (X Y Z : list C) (f : tensor X ⟶ tensor Y) (g : tensor Y ⟶ tensor Z) : pack (f ≫ g) = pack f ≫ pack g := rfl

open category monoidal_category

lemma cancel_left {X Y Z : C} {f : X ⟶ Y} [is_iso f] {g : Y ⟶ Z} {h : X ⟶ Z} : (f ≫ g = h) ↔ (g = (inv f) ≫ h) :=
sorry

instance : monoidal_category.{v₁} (list C) :=
{ tensor_obj := λ X Y, X ++ Y,
  tensor_unit := [],
  tensor_hom := λ W X Y Z f g,
  pack $ (tensorator W Y).inv ≫ ((unpack f) ⊗ (unpack g)) ≫ (tensorator X Z).hom,
  associator   := λ X Y Z, eq_to_iso (list.append_assoc _ _ _),
  left_unitor  := λ X, iso.refl _,
  right_unitor := λ X, eq_to_iso (list.append_nil _),
  tensor_id' := sorry, --λ X Y, by simp,
  tensor_comp' := sorry, --λ U V W X Y Z f g h k, begin dsimp [pack], erw [assoc, assoc], simp, dsimp [unpack], erw [tensor_comp, assoc], end,
  associator_naturality' := λ X₁ X₂ X₃ Y₁ Y₂ Y₃ f₁ f₂ f₃, begin dsimp [pack, unpack], sorry end,
  left_unitor_naturality' := λ X Y f, begin dsimp [tensorator, pack, unpack], simp, erw [left_unitor_naturality], simp, end,
  right_unitor_naturality' := λ X Y f, begin dsimp, sorry end,
  pentagon' := sorry,
  triangle' := λ X Y, begin dsimp, rw tensorator_congr_left (list.append_nil X), simp, end
}

end category_theory
