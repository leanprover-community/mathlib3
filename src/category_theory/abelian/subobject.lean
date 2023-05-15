/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.subobject.limits
import category_theory.abelian.basic

/-!
# Equivalence between subobjects and quotients in an abelian category

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

open category_theory category_theory.limits opposite

universes v u

noncomputable theory

namespace category_theory.abelian
variables {C : Type u} [category.{v} C]

/-- In an abelian category, the subobjects and quotient objects of an object `X` are
    order-isomorphic via taking kernels and cokernels.
    Implemented here using subobjects in the opposite category,
    since mathlib does not have a notion of quotient objects at the time of writing. -/
@[simps]
def subobject_iso_subobject_op [abelian C] (X : C) : subobject X ≃o (subobject (op X))ᵒᵈ :=
begin
  refine order_iso.of_hom_inv (cokernel_order_hom X) (kernel_order_hom X) _ _,
  { change (cokernel_order_hom X).comp (kernel_order_hom X) = _,
    refine order_hom.ext _ _ (funext (subobject.ind _ _)),
    introsI A f hf,
    dsimp only [order_hom.comp_coe, function.comp_app, kernel_order_hom_coe, subobject.lift_mk,
      cokernel_order_hom_coe, order_hom.id_coe, id.def],
    refine subobject.mk_eq_mk_of_comm _ _ ⟨_, _, quiver.hom.unop_inj _, quiver.hom.unop_inj _⟩ _,
    { exact (abelian.epi_desc f.unop _ (cokernel.condition (kernel.ι f.unop))).op },
    { exact (cokernel.desc _ _ (kernel.condition f.unop)).op },
    { simp only [← cancel_epi (cokernel.π (kernel.ι f.unop)), unop_comp, quiver.hom.unop_op,
        unop_id_op, cokernel.π_desc_assoc, comp_epi_desc, category.comp_id] },
    { simp only [← cancel_epi f.unop, unop_comp, quiver.hom.unop_op, unop_id, comp_epi_desc_assoc,
        cokernel.π_desc, category.comp_id] },
    { exact quiver.hom.unop_inj (by simp only [unop_comp, quiver.hom.unop_op, comp_epi_desc]) } },
  { change (kernel_order_hom X).comp (cokernel_order_hom X) = _,
    refine order_hom.ext _ _ (funext (subobject.ind _ _)),
    introsI A f hf,
    dsimp only [order_hom.comp_coe, function.comp_app, cokernel_order_hom_coe, subobject.lift_mk,
      kernel_order_hom_coe, order_hom.id_coe, id.def, unop_op, quiver.hom.unop_op],
    refine subobject.mk_eq_mk_of_comm _ _ ⟨_, _, _, _⟩ _,
    { exact abelian.mono_lift f _ (kernel.condition (cokernel.π f)) },
    { exact kernel.lift _ _ (cokernel.condition f) },
    { simp only [← cancel_mono (kernel.ι (cokernel.π f)), category.assoc, image.fac, mono_lift_comp,
        category.id_comp, auto_param_eq] },
    { simp only [← cancel_mono f, category.assoc, mono_lift_comp, image.fac, category.id_comp,
        auto_param_eq] },
    { simp only [mono_lift_comp] } }
end

/-- A well-powered abelian category is also well-copowered. -/
instance well_powered_opposite [abelian C] [well_powered C] : well_powered Cᵒᵖ :=
{ subobject_small := λ X,
    (small_congr (subobject_iso_subobject_op (unop X)).to_equiv).1 infer_instance }

end category_theory.abelian
