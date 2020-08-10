import category_theory.monoidal.braided
import category_theory.monoidal.unitors
import category_theory.monoidal.internal
import category_theory.monoidal.End

universes v u

open category_theory
open category_theory.monoidal_category
open category_theory.braided_category

variables {C : Type u} [category.{v} C] [monoidal_category.{v} C] [braided_category.{v} C]

lemma tensor_obj_one_mul (X Y : Mon_ C) :
  ((λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one) ⊗ 𝟙 (X.X ⊗ Y.X)) ≫
      (α_ X.X Y.X (X.X ⊗ Y.X)).hom ≫
        (𝟙 X.X ⊗ (α_ Y.X X.X Y.X).inv ≫
          ((β_ Y.X X.X).hom ⊗ 𝟙 Y.X) ≫ (α_ X.X Y.X Y.X).hom) ≫
          (α_ X.X X.X (Y.X ⊗ Y.X)).inv ≫ (X.mul ⊗ Y.mul) =
    (λ_ (X.X ⊗ Y.X)).hom :=
begin
  rw [←tensor_id_comp_id_tensor X.one Y.one],
  rw [←tensor_id_comp_id_tensor X.mul Y.mul],
  sorry,
end

local attribute [instance] endofunctor_monoidal_category

lemma tensor_obj_mul_assoc (X Y : Mon_ C) :
  ((α_ X.X Y.X (X.X ⊗ Y.X)).hom ≫
  (𝟙 X.X ⊗
    (α_ Y.X X.X Y.X).inv ≫
    ((β_ Y.X X.X).hom ⊗ 𝟙 Y.X) ≫
    (α_ X.X Y.X Y.X).hom) ≫
  (α_ X.X X.X (Y.X ⊗ Y.X)).inv ≫ (X.mul ⊗ Y.mul) ⊗ 𝟙 (X.X ⊗ Y.X)) ≫
  (α_ X.X Y.X (X.X ⊗ Y.X)).hom ≫
    (𝟙 X.X ⊗ (α_ Y.X X.X Y.X).inv ≫
    ((β_ Y.X X.X).hom ⊗ 𝟙 Y.X) ≫ (α_ X.X Y.X Y.X).hom) ≫
    (α_ X.X X.X (Y.X ⊗ Y.X)).inv ≫ (X.mul ⊗ Y.mul) =
    (α_ (X.X ⊗ Y.X) (X.X ⊗ Y.X) (X.X ⊗ Y.X)).hom ≫
      (𝟙 (X.X ⊗ Y.X) ⊗ (α_ X.X Y.X (X.X ⊗ Y.X)).hom ≫
      (𝟙 X.X ⊗ (α_ Y.X X.X Y.X).inv ≫
        ((β_ Y.X X.X).hom ⊗ 𝟙 Y.X) ≫ (α_ X.X Y.X Y.X).hom) ≫
        (α_ X.X X.X (Y.X ⊗ Y.X)).inv ≫ (X.mul ⊗ Y.mul)) ≫
  (α_ X.X Y.X (X.X ⊗ Y.X)).hom ≫
    (𝟙 X.X ⊗ (α_ Y.X X.X Y.X).inv ≫
    ((β_ Y.X X.X).hom ⊗ 𝟙 Y.X) ≫ (α_ X.X Y.X Y.X).hom) ≫
    (α_ X.X X.X (Y.X ⊗ Y.X)).inv ≫ (X.mul ⊗ Y.mul) :=
begin
  -- The key lemmas are `X.mul_assoc` and `Y.mul_assoc`,
  -- but we need to do a lot of rearranging before they can be applied.
  -- We keep everything "in slices", i.e. expanded out according to
  -- `id_tensor_comp` and `comp_tensor_id`, undoing this locally as necessary.
  -- The general plan is to push `Y.mul` as high as possible, after than `X.mul`,
  -- and keep the braidings low.

  -- We begin by separating both occurrences of `X.mul ⊗ Y.mul` into separate slices.
  simp only [comp_tensor_id, id_tensor_comp, category.assoc],
  conv_lhs {
    rw [←tensor_id_comp_id_tensor X.mul Y.mul],
    rw [comp_tensor_id],
  },

  -- Now we start pushing the first occurrence of `Y.mul` upwards,
  -- trying to get it close to the second occurrence.
  slice_lhs 7 8 {
    rw associator_naturality,
  },
  slice_lhs 8 9 {
    rw [←id_tensor_comp],
    rw [←tensor_id],
    rw [associator_inv_naturality],
    rw [id_tensor_comp],
  },
  slice_lhs 9 10 {
    rw [←id_tensor_comp, ←comp_tensor_id],
    rw [braiding_naturality],
    rw [comp_tensor_id, id_tensor_comp],
  },
  slice_lhs 10 11 {
    rw [←id_tensor_comp, associator_naturality, id_tensor_comp],
  },
  slice_lhs 11 12 {
    rw [associator_inv_naturality],
  },
  slice_lhs 12 13 {
    rw tensor_id,
    rw id_tensor_comp_tensor_id,
    rw ←tensor_id_comp_id_tensor,
  },
  slice_lhs 13 14 {
    rw [←id_tensor_comp, Y.mul_assoc, id_tensor_comp, id_tensor_comp],
  },
  -- Success!
  -- Now time to move `X.mul` so we can apply `X.mul_assoc`.
  slice_lhs 6 7 {
    rw [associator_naturality],
  },
  slice_lhs 7 8 {
    rw [tensor_id],
    rw tensor_id_comp_id_tensor,
    rw ←id_tensor_comp_tensor_id,
  },
  slice_lhs 8 9 {
    rw tensor_id_comp_id_tensor,
    rw ←id_tensor_comp_tensor_id,
  },
  slice_lhs 9 10 {
    rw tensor_id_comp_id_tensor,
    rw ←id_tensor_comp_tensor_id,
  },
  slice_lhs 10 11 {
    rw [←tensor_id],
    rw associator_inv_naturality,
  },
  slice_lhs 11 12 {
    rw [←comp_tensor_id, X.mul_assoc, comp_tensor_id, comp_tensor_id],
  },
  -- We've successfully used `X.mul_assoc`, but there's still one more associator above:
  slice_lhs 13 14 {
    rw [tensor_id_comp_id_tensor],
    rw [←id_tensor_comp_tensor_id],
  },
  slice_lhs 12 13 {
    rw [tensor_id_comp_id_tensor],
    rw [←id_tensor_comp_tensor_id],
  },

  -- Now we turn to the right hand side. There's less work to do here:
  -- we don't need to use associativity of the monoid objects,
  -- just split things into slices and arrange into
  -- 'junk', then 'X.mul', then 'Y.mul'.
  conv_rhs {
    rw [←tensor_id_comp_id_tensor X.mul Y.mul],
    rw [id_tensor_comp],
  },
  slice_rhs 8 9 {
    rw ←tensor_id,
    rw associator_naturality,
  },
  slice_rhs 9 10 {
    rw [←id_tensor_comp, associator_inv_naturality, id_tensor_comp],
  },
  slice_rhs 10 11 {
    rw [←id_tensor_comp],
    rw [tensor_id],
    rw [id_tensor_comp_tensor_id],
    rw [←tensor_id_comp_id_tensor _ Y.mul],
    rw [id_tensor_comp],
  },
  slice_rhs 11 12 {
    rw [←id_tensor_comp, ←tensor_id, associator_naturality, id_tensor_comp],
  },
  slice_rhs 12 13 {
    rw [associator_inv_naturality],
  },
  slice_rhs 13 14 {
    rw [tensor_id],
    rw [id_tensor_comp_tensor_id],
    rw [←tensor_id_comp_id_tensor],
  },
  slice_rhs 7 8 {
    rw [←tensor_id],
    rw associator_naturality,
  },
  slice_rhs 8 9 {
    rw [←id_tensor_comp, associator_inv_naturality, id_tensor_comp],
  },
  slice_rhs 9 10 {
    rw [←id_tensor_comp, ←comp_tensor_id],
    rw [braiding_naturality],
    rw [comp_tensor_id, id_tensor_comp],
  },
  slice_rhs 10 11 {
    rw [←id_tensor_comp, associator_naturality, id_tensor_comp],
  },
  slice_rhs 11 12 {
    rw associator_inv_naturality,
  },


  -- By associating the wrong way, we can strip off everything about `X.mul` and `Y.mul`,
  -- obtaining a goal just about braidings and associators.
  simp only [←category.assoc, tensor_id],
  congr' 4,
  simp only [category.assoc],

  -- We still need to use the hexagon identities!
  simp only [hexagon_forward, hexagon_reverse, pentagon_middle, pentagon_inv_middle,
    id_tensor_comp, comp_tensor_id, category.assoc],

  simp only [id_tensor_inv_hom_assoc, id_tensor_hom_inv_tensor_id_assoc,
    tensor_id, category.id_comp],

  -- Ignoring associators(!), this is essentially the easy equation
  --   `σ₂ σ₄ σ₃ = σ₄ σ₂ σ₃`
  -- in the braid group.
  -- So let's deal with that first, pushing the `σ₄` appearing on the right hand side later.
  slice_rhs 7 8 { rw [←tensor_id, associator_naturality] },
  slice_rhs 8 9 { rw [←id_tensor_comp, ←id_tensor_comp, iso.inv_hom_id], },
  slice_rhs 8 9 { rw [tensor_id, tensor_id, category.id_comp], },
  slice_rhs 9 10 { rw [←id_tensor_comp, ←associator_inv_naturality, id_tensor_comp], },
  slice_rhs 6 7 { rw [←tensor_id, associator_naturality], },
  slice_rhs 7 8 { rw [←id_tensor_comp, associator_inv_naturality, id_tensor_comp], },
  slice_rhs 8 9 {
    rw [←id_tensor_comp, tensor_id, tensor_id,
      id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor (β_ _ _).hom, id_tensor_comp], },
  slice_rhs 5 6 { rw [←tensor_id, associator_naturality], },
  slice_rhs 6 7 { rw [←id_tensor_comp, associator_inv_naturality, id_tensor_comp], },
  slice_rhs 7 8 { rw [←id_tensor_comp, tensor_id,
      id_tensor_comp_tensor_id, ←tensor_id_comp_id_tensor (β_ _ _).hom, id_tensor_comp], },

  -- From here on, it's "just" associators.
  simp only [tensor_id_comp_id_tensor, category.assoc],
  rw [is_iso.is_iso_comp_eq, is_iso.is_iso_comp_eq],
  simp only [is_iso.iso.inv_hom, is_iso.inv_id, is_iso.iso.inv_inv, inv_tensor],

  slice_rhs 6 7 { rw [←tensor_id, associator_naturality], },
  slice_rhs 7 8 { rw [←id_tensor_comp, associator_inv_naturality, id_tensor_comp], },
  slice_rhs 8 9 {
    rw [←id_tensor_comp, tensor_id, id_tensor_comp_tensor_id,
      ←tensor_id_comp_id_tensor (β_ _ _).hom, id_tensor_comp], },
  simp only [category.assoc],
  -- apply (tensoring_right_monoidal C).to_functor.map_injective,
  -- simp [functor.map_comp],
  -- simp [monoidal_functor.map_tensor],
  sorry,
end

instance : monoidal_category (Mon_ C) :=
{ tensor_obj := λ X Y,
  { X := X.X ⊗ Y.X,
    one := (λ_ (𝟙_ C)).inv ≫ (X.one ⊗ Y.one),
    mul := (α_ X.X Y.X (X.X ⊗ Y.X)).hom ≫ (𝟙 X.X ⊗ ((α_ Y.X X.X Y.X).inv ≫ ((β_ Y.X X.X).hom ⊗ 𝟙 Y.X) ≫ (α_ X.X Y.X Y.X).hom)) ≫ (α_ X.X X.X (Y.X ⊗ Y.X)).inv ≫ (X.mul ⊗ Y.mul),
    one_mul' := tensor_obj_one_mul _ _,
    mul_one' := sorry,
    mul_assoc' := tensor_obj_mul_assoc _ _, },
  tensor_hom := λ W X Y Z f g,
  { hom := f.hom ⊗ g.hom, },
  tensor_unit :=
  { X := 𝟙_ C,
    one := 𝟙 _,
    mul := (λ_ (𝟙_ C)).hom,
    one_mul' := by simp,
    mul_one' := by simp [unitors_equal],
    mul_assoc' := begin sorry end, },
  associator := λ X Y Z,
  { hom := { hom := (α_ X.X Y.X Z.X).hom },
    inv := { hom := (α_ X.X Y.X Z.X).inv } },
  left_unitor := λ X,
  { hom := { hom := (λ_ X.X).hom },
    inv := { hom := (λ_ X.X).inv } },
  right_unitor := λ X,
  { hom := { hom := (ρ_ X.X).hom },
    inv := { hom := (ρ_ X.X).inv } } }
