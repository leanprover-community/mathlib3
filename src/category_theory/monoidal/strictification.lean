import category_theory.monoidal.functor
import category_theory.full_subcategory
import category_theory.eq_to_hom
import category_theory.equivalence

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

@[simp] lemma tensor_nil : tensor [] = 𝟙_ C := rfl
@[simp] lemma tensor_cons {X : C} {w : list C} : tensor (X :: w) = X ⊗ tensor w := rfl

def tensorator : Π (w z : list C), (tensor w) ⊗ (tensor z) ≅ tensor (w ++ z)
| [] z := (λ_ _)
| (X :: w) z := (α_ _ _ _) ≪≫ (tensor_iso (iso.refl _) (tensorator w z))

@[simp] lemma tensorator_nil {z : list C} : tensorator [] z = (λ_ _) := rfl
@[simp] lemma tensorator_cons {X} {w z : list C} : tensorator (X :: w) z = (α_ _ _ _) ≪≫ (tensor_iso (iso.refl _) (tensorator w z)) := rfl

def tensorator_congr_left {w w' : list C} (h : w = w') (z : list C) :
  tensorator w z =
    (tensor_iso (eq_to_iso (by { cases h, refl })) (iso.refl _)) ≪≫
    tensorator w' z ≪≫ eq_to_iso (by { cases h, refl }) :=
by { cases h, simp }
def tensorator_congr_right (w : list C) {z z' : list C} (h : z = z') :
  tensorator w z =
    (tensor_iso (iso.refl _) (eq_to_iso (by { cases h, refl }))) ≪≫
    tensorator w z' ≪≫ eq_to_iso (by { cases h, refl }) :=
by { cases h, simp }

lemma tensorator_assoc : Π (u v w : list C),
  ((tensorator u v).hom ⊗ 𝟙 _) ≫ (tensorator (u ++ v) w).hom =
  (α_ _ _ _).hom ≫ (𝟙 _ ⊗ (tensorator v w).hom) ≫ (tensorator u (v ++ w)).hom ≫ eq_to_hom (by rw list.append_assoc) :=
begin
  intros,
  induction u,
  { dsimp, simp, sorry, },
  { dsimp, simp,
    rw ←comp_tensor_id,
    slice_lhs 2 3 { erw associator_naturality, },
    slice_lhs 3 4 { rw id_tensor_comp, },
    rw u_ih,
    slice_lhs 1 3 { rw pentagon, },
    slice_rhs 2 3 { rw ←tensor_id, rw associator_naturality, },
     }
end

instance : category.{v₁} (list C) :=
{ hom := λ X Y, (tensor X) ⟶ (tensor Y),
  id := λ X, 𝟙 (tensor X),
  comp := λ X Y Z f g, f ≫ g, }

-- lemma tensorator_natural {w w' z z' : list C} (f : w ⟶ w') (g : z ⟶ z') : (f ⊗ g) ≫ (tensorator w' z').hom = sorry

def unpack {X Y : list C} (f : X ⟶ Y) : tensor X ⟶ tensor Y := f
def pack {X Y : list C} (f : tensor X ⟶ tensor Y) : X ⟶ Y := f

@[simp] lemma unpack_id (X : list C) : unpack (𝟙 X) = 𝟙 (tensor X) := rfl
@[simp] lemma pack_id (X : list C) : pack (𝟙 (tensor X)) = 𝟙 X := rfl
-- @[simp] lemma unpack_comp (X Y Z : list C) (f : X ⟶ Y) (g : Y ⟶ Z) : unpack (f ≫ g) = unpack f ≫ unpack g := rfl
lemma pack_comp (X Y Z : list C) (f : tensor X ⟶ tensor Y) (g : tensor Y ⟶ tensor Z) : pack (f ≫ g) = pack f ≫ pack g := rfl

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
  right_unitor_naturality' := λ X Y f, begin dsimp [tensorator, pack, unpack], sorry, end,
  pentagon' := λ W X Y Z,
  begin
    sorry
    -- dsimp [pack, unpack],
    -- rw tensorator_congr_left (list.append_assoc _ _ _) _,
    -- rw tensorator_congr_right _ (list.append_assoc _ _ _),
    -- dsimp,
    -- simp,
    -- slice_lhs 5 6 { erw id_tensor_comp },
    -- erw eq_to_hom_trans_assoc,
    -- erw eq_to_hom_trans,

    -- erw comp_tensor_id_assoc,
    -- erw eq_to_hom_trans,
    -- simp,
    -- erw eq_to_hom_trans_assoc,
    -- simp,
    -- erw comp_id,
    -- rw list.append_assoc W X Y,
    -- rw list.append_assoc W X Y,
    -- rw list.append_assoc X Y Z,
    -- rw list.append_assoc X Y Z,
  end,
  triangle' := λ X Y,
  begin
    sorry
    -- dsimp,
    -- rw tensorator_congr_left (list.append_nil X),
    -- simp,
    -- apply congr_arg unpack,
    -- slice_rhs 3 4 { rw comp_tensor_id },
    -- dsimp [unpack],
    -- erw eq_to_hom_trans,
    -- dsimp, simp,
    -- refl,
    -- rw list.append_nil,
  end
}.

variables (C)
def strictification : (list C) ⥤ C :=
{ obj := λ X, tensor X,
  map := λ X Y f, f }

namespace strictification
instance : ess_surj (strictification C) :=
{ obj_preimage := λ X, [X],
  iso' := λ X, ρ_ X }

instance : full (strictification C) :=
{ preimage := λ X Y f, f }

instance : faithful (strictification C) :=
{}

instance : is_equivalence (strictification C) := equivalence.equivalence_of_fully_faithfully_ess_surj _

end strictification

-- TODO We're not there yet! We want a monoidal equivalence, of course.

def monoidal_strictification : monoidal_functor.{v₁ v₁} (list C) C :=
{ ε := 𝟙 _,
  μ := λ X Y, (tensorator X Y).hom,
  μ_is_iso := λ X Y, is_iso.of_iso _,
  μ_natural' := sorry,
  associativity' := sorry,
  left_unitality' := sorry,
  right_unitality' := sorry,
  ..(strictification C) }

-- Finally, we need to prove that a monoidal functor which is part of an equivalence is part of a monoidal equivalence.
-- err... and think about whether that's really the condition we want (3-categories, etc.)

end category_theory
