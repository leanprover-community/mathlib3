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

variables {C} {X Y : C} (f : X ⟶ Y) {A B : Cᵒᵖ} (g : A ⟶ B)

-- TODO: Generalize (this will work whenever f has a cokernel)
-- (The abelian case is probably sufficient for most applications.)
/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernel_op_unop : (kernel f.op).unop ≅ cokernel f :=
{ hom := (kernel.lift f.op (cokernel.π f).op $ by simp [← op_comp]).unop,
  inv := cokernel.desc f (kernel.ι f.op).unop $
    by { rw [← f.unop_op, ← unop_comp, f.unop_op], simp },
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

-- TODO: Generalize (this will work whenever f has a kernel)
-- (The abelian case is probably sufficient for most applications.)
/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernel_op_unop : (cokernel f.op).unop ≅ kernel f :=
{ hom := kernel.lift f (cokernel.π f.op).unop $
    by { rw [← f.unop_op, ← unop_comp, f.unop_op], simp },
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

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps]
def kernel_unop_op : opposite.op (kernel g.unop) ≅ cokernel g :=
(cokernel_op_unop g.unop).op

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernel_unop_op : opposite.op (cokernel g.unop) ≅ kernel g :=
(kernel_op_unop g.unop).op

/-- The kernel of `f.op` is the opposite of `cokernel f`. -/
@[simps]
def kernel_op_op : kernel f.op ≅ opposite.op (cokernel f) :=
(kernel_op_unop f).op.symm

/-- The cokernel of `f.op` is the opposite of `kernel f`. -/
@[simps]
def cokernel_op_op : cokernel f.op ≅ opposite.op (kernel f) :=
(cokernel_op_unop f).op.symm

/-- The kernel of `g.unop` is the opposite of `cokernel g`. -/
@[simps]
def kernel_unop_unop : kernel g.unop ≅ (cokernel g).unop :=
(kernel_unop_op g).unop.symm

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernel_unop_unop : cokernel g.unop ≅ (kernel g).unop :=
(cokernel_unop_op g).unop.symm

end

end category_theory
