/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.abelian.basic
import category_theory.preadditive.opposite
import category_theory.limits.opposites
import category_theory.limits.constructions.limits_of_products_and_equalizers

/-!
# The opposite of an abelian category is abelian.
-/

noncomputable theory

namespace category_theory

open category_theory.limits

variables (C : Type*) [category C] [abelian C]

local attribute [instance]
  finite_limits_from_equalizers_and_finite_products
  finite_colimits_from_coequalizers_and_finite_coproducts
  has_finite_limits_opposite has_finite_colimits_opposite has_finite_products_opposite

instance : abelian Cᵒᵖ :=
{ normal_mono := λ X Y f m, by exactI
    normal_mono_of_normal_epi_unop _ (abelian.normal_epi f.unop),
  normal_epi := λ X Y f m, by exactI
    normal_epi_of_normal_mono_unop _ (abelian.normal_mono f.unop), }

section

variables {X Y : C} (f : X ⟶ Y)

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernel_op_unop : (kernel f.op).unop ≅ cokernel f :=
{ hom := (kernel.lift f.op (cokernel.π f).op $ by simp [← op_comp]).unop,
  inv := cokernel.desc f (kernel.ι f.op).unop $
    by { erw [← f.unop_op, ← unop_comp, f.unop_op], simp },
  hom_inv_id' := begin
    rw [← unop_id, ← (cokernel.desc f _ _).unop_op, ← unop_comp],
    congr' 1,
    dsimp,
    ext,
    simp [← op_comp],
  end,
  inv_hom_id' := begin
    dsimp,
    ext,
    simp [← unop_comp],
  end }

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernel_op_unop : (cokernel f.op).unop ≅ kernel f :=
{ hom := kernel.lift f (cokernel.π f.op).unop $
    by { erw [← f.unop_op, ← unop_comp, f.unop_op], simp },
  inv := (cokernel.desc f.op (kernel.ι f).op $ by simp [← op_comp]).unop,
  hom_inv_id' := begin
    rw [← unop_id, ← (kernel.lift f _ _).unop_op, ← unop_comp],
    congr' 1,
    dsimp,
    ext,
    simp [← op_comp],
  end,
  inv_hom_id' := begin
    dsimp,
    ext,
    simp [← unop_comp],
  end }

end

end category_theory
