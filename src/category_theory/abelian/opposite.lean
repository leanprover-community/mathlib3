/-
Copyright (c) 2021 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import category_theory.abelian.basic
import category_theory.preadditive.opposite
import category_theory.limits.opposites

/-!
# The opposite of an abelian category is abelian.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

noncomputable theory

namespace category_theory

open category_theory.limits

variables (C : Type*) [category C] [abelian C]

local attribute [instance]
  has_finite_limits_of_has_equalizers_and_finite_products
  has_finite_colimits_of_has_coequalizers_and_finite_coproducts

instance : abelian Cᵒᵖ :=
{ normal_mono_of_mono := λ X Y f m, by exactI
    normal_mono_of_normal_epi_unop _ (normal_epi_of_epi f.unop),
  normal_epi_of_epi := λ X Y f m, by exactI
    normal_epi_of_normal_mono_unop _ (normal_mono_of_mono f.unop), }

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

lemma cokernel.π_op : (cokernel.π f.op).unop =
  (cokernel_op_unop f).hom ≫ kernel.ι f ≫ eq_to_hom (opposite.unop_op _).symm :=
by simp [cokernel_op_unop]

lemma kernel.ι_op : (kernel.ι f.op).unop =
  eq_to_hom (opposite.unop_op _) ≫ cokernel.π f ≫ (kernel_op_unop f).inv :=
by simp [kernel_op_unop]

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

lemma kernel.ι_unop : (kernel.ι g.unop).op =
  eq_to_hom (opposite.op_unop _) ≫ cokernel.π g ≫ (kernel_unop_op g).inv :=
by simp

lemma cokernel.π_unop : (cokernel.π g.unop).op =
  (cokernel_unop_op g).hom ≫ kernel.ι g ≫ eq_to_hom (opposite.op_unop _).symm :=
by simp

/-- The cokernel of `g.unop` is the opposite of `kernel g`. -/
@[simps]
def cokernel_unop_unop : cokernel g.unop ≅ (kernel g).unop :=
(cokernel_unop_op g).unop.symm

/-- The opposite of the image of `g.unop` is the image of `g.` -/
def image_unop_op : opposite.op (image g.unop) ≅ image g :=
(abelian.image_iso_image _).op ≪≫ (cokernel_op_op _).symm ≪≫
  cokernel_iso_of_eq (cokernel.π_unop _) ≪≫ (cokernel_epi_comp _ _)
  ≪≫ (cokernel_comp_is_iso _ _) ≪≫ (abelian.coimage_iso_image' _)

/-- The opposite of the image of `f` is the image of `f.op`. -/
def image_op_op : opposite.op (image f) ≅ image f.op := image_unop_op f.op

/-- The image of `f.op` is the opposite of the image of `f`. -/
def image_op_unop : (image f.op).unop ≅ image f := (image_unop_op f.op).unop

/-- The image of `g` is the opposite of the image of `g.unop.` -/
def image_unop_unop : (image g).unop ≅ image g.unop := (image_unop_op g).unop

lemma image_ι_op_comp_image_unop_op_hom :
  (image.ι g.unop).op ≫ (image_unop_op g).hom = factor_thru_image g :=
begin
  dunfold image_unop_op,
  simp only [←category.assoc, ←op_comp, iso.trans_hom, iso.symm_hom, iso.op_hom, cokernel_op_op_inv,
    cokernel_comp_is_iso_hom, cokernel_epi_comp_hom, cokernel_iso_of_eq_hom_comp_desc_assoc,
    abelian.coimage_iso_image'_hom, eq_to_hom_refl, is_iso.inv_id,
    category.id_comp (cokernel.π (kernel.ι g))],
  simp only [category.assoc, abelian.image_iso_image_hom_comp_image_ι, kernel.lift_ι,
    quiver.hom.op_unop, cokernel.π_desc],
end

lemma image_unop_op_hom_comp_image_ι :
  (image_unop_op g).hom ≫ image.ι g = (factor_thru_image g.unop).op :=
by simp only [←cancel_epi (image.ι g.unop).op, ←category.assoc, image_ι_op_comp_image_unop_op_hom,
  ←op_comp, image.fac, quiver.hom.op_unop]

lemma factor_thru_image_comp_image_unop_op_inv :
  factor_thru_image g ≫ (image_unop_op g).inv = (image.ι g.unop).op :=
by rw [iso.comp_inv_eq, image_ι_op_comp_image_unop_op_hom]

lemma image_unop_op_inv_comp_op_factor_thru_image :
  (image_unop_op g).inv ≫ (factor_thru_image g.unop).op = image.ι g :=
by rw [iso.inv_comp_eq, image_unop_op_hom_comp_image_ι]

end

end category_theory
