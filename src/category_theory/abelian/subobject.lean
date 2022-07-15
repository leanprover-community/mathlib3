/-
Copyright (c) 2022 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel
-/
import category_theory.abelian.opposite
import category_theory.subobject.limits

/-!
# Equivalence between subobjects and quotients in abelian categories

-/

open category_theory category_theory.limits opposite

universes v u

noncomputable theory

variables {C : Type u} [category.{v} C] [abelian C]

namespace category_theory.abelian

def order_iso (X : C) : subobject X ≃o (subobject (op X))ᵒᵈ :=
{ to_fun := subobject.lift (λ A f hf, subobject.mk (cokernel.π f).op)
  begin
    rintros A B f g hf hg i rfl,
    refine subobject.mk_eq_mk_of_comm _ _ (iso.op _) (quiver.hom.unop_inj _),
    { exact (is_colimit.cocone_point_unique_up_to_iso (colimit.is_colimit _)
        (is_cokernel_epi_comp (colimit.is_colimit _) i.hom rfl)).symm },
    { simp only [iso.comp_inv_eq, iso.op_hom, iso.symm_hom, unop_comp, quiver.hom.unop_op,
        colimit.comp_cocone_point_unique_up_to_iso_hom, cofork.of_π_ι_app, coequalizer.cofork_π] }
  end ,
  inv_fun := subobject.lift (λ A f hf, subobject.mk (kernel.ι f.unop))
  begin
    rintros A B f g hf hg i rfl,
    refine subobject.mk_eq_mk_of_comm _ _ _ _,
    { exact is_limit.cone_point_unique_up_to_iso (limit.is_limit _)
        (is_kernel_comp_mono (limit.is_limit (parallel_pair g.unop 0)) i.unop.hom rfl) },
    { dsimp,
      simp only [←iso.eq_inv_comp, limit.cone_point_unique_up_to_iso_inv_comp, fork.of_ι_π_app] }
  end,
  left_inv :=
  begin
    apply subobject.ind,
    introsI,
    dsimp,
    refine subobject.mk_eq_mk_of_comm _ _ ⟨_, _, _, _⟩ _,
    { exact abelian.mono_lift f _ (kernel.condition (cokernel.π f)) },
    { exact kernel.lift _ _ (cokernel.condition f) },
    { simp [← cancel_mono (kernel.ι (cokernel.π f))] },
    { simp [← cancel_mono f] },
    { simp }
  end,
  right_inv :=
  begin
    apply subobject.ind,
    introsI,
    dsimp,
    refine subobject.mk_eq_mk_of_comm _ _ ⟨_, _, quiver.hom.unop_inj _, quiver.hom.unop_inj _⟩ _,
    { exact (abelian.epi_desc f.unop _ (cokernel.condition (kernel.ι f.unop))).op },
    { exact (cokernel.desc _ _ (kernel.condition f.unop)).op },
    { simp [← cancel_epi (cokernel.π (kernel.ι f.unop))] },
    { simp [← cancel_epi f.unop] },
    { exact quiver.hom.unop_inj (by simp) }
  end,
  map_rel_iff' :=
  begin
    apply subobject.ind₂,
    dsimp,
    introsI,
    refine ⟨λ h, subobject.mk_le_mk_of_comm _ _, λ h, subobject.mk_le_mk_of_comm _ _⟩,
    { refine abelian.mono_lift g f (quiver.hom.op_inj _),
      dsimp,
      rw [← subobject.of_mk_le_mk_comp h],
      refine quiver.hom.unop_inj _,
      simp only [category.assoc, unop_comp, quiver.hom.unop_op, cokernel.condition, zero_comp,
        unop_zero] },
    { exact abelian.mono_lift_comp _ _ _ },
    { refine (cokernel.desc f (cokernel.π g) _).op,
      rw [← subobject.of_mk_le_mk_comp h, category.assoc, cokernel.condition, comp_zero] },
    { refine quiver.hom.unop_inj (cokernel.π_desc _ _ _) }
  end }

end category_theory.abelian
