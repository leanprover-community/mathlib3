/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.morphisms.basic
import ring_theory.local_properties

/-!

# Properties of morphisms from properties of ring homs.

-/

universe u

open category_theory opposite topological_space category_theory.limits algebraic_geometry

variable (P : ∀ {R S : Type u} [comm_ring R] [comm_ring S] (f : by exactI R →+* S), Prop)

instance {C : Type*} [category C] {X Y : Cᵒᵖ} (f : X ⟶ Y) [H : is_iso f] : is_iso f.unop :=
@@is_iso_of_op _ f.unop H

namespace ring_hom

include P

variable {P}

lemma respects_iso.basic_open_iff (hP : respects_iso @P) {X Y : Scheme}
  [is_affine X] [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (opposite.op ⊤)) :
  P (Scheme.Γ.map (f ∣_ Y.basic_open r).op) ↔
  P (@is_localization.away.map (Y.presheaf.obj (opposite.op ⊤)) _
      (Y.presheaf.obj (opposite.op $ Y.basic_open r)) _ _
      (X.presheaf.obj (opposite.op ⊤)) _ (X.presheaf.obj
      (opposite.op $ X.basic_open (Scheme.Γ.map f.op r))) _ _ (Scheme.Γ.map f.op) r _ _) :=
begin
  rw [Γ_map_morphism_restrict, hP.cancel_left_is_iso, hP.cancel_right_is_iso,
    ← (hP.cancel_right_is_iso (f.val.c.app (opposite.op (Y.basic_open r))) (X.presheaf.map
      (eq_to_hom (Scheme.preimage_basic_open f r).symm).op)), ← eq_iff_iff],
  congr,
  delta is_localization.away.map,
  refine is_localization.ring_hom_ext (submonoid.powers r) _,
  convert (is_localization.map_comp _).symm using 1,
  change Y.presheaf.map _ ≫ _ = _ ≫ X.presheaf.map _,
  rw f.val.c.naturality_assoc,
  erw ← X.presheaf.map_comp,
  congr,
end

lemma respects_iso.basic_open_iff_localization (hP : respects_iso @P)
  {X Y : Scheme} [is_affine X] [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (opposite.op ⊤)) :
  P (Scheme.Γ.map (f ∣_ Y.basic_open r).op) ↔
  P (localization.away_map (Scheme.Γ.map f.op) r) :=
(hP.basic_open_iff _ _).trans (hP.is_localization_away_iff _ _ _ _).symm

lemma respects_iso.of_restrict_morphism_restrict_iff (hP : ring_hom.respects_iso @P)
  {X Y : Scheme} [is_affine Y] (f : X ⟶ Y) (r : Y.presheaf.obj (opposite.op ⊤))
  (U : opens X.carrier) (hU : is_affine_open U) {V : opens _}
  (e : V = (opens.map (X.of_restrict ((opens.map f.1.base).obj _).open_embedding).1.base).obj U) :
  P (Scheme.Γ.map ((X.restrict ((opens.map f.1.base).obj _).open_embedding).of_restrict
    V.open_embedding ≫ f ∣_ Y.basic_open r).op) ↔
    P (localization.away_map (Scheme.Γ.map (X.of_restrict U.open_embedding ≫ f).op) r) :=
begin
  subst e,
  convert (hP.is_localization_away_iff _ _ _ _).symm,
  rotate,
  { apply_instance },
  { apply ring_hom.to_algebra,
    refine X.presheaf.map
      (@hom_of_le _ _ ((is_open_map.functor _).obj _) ((is_open_map.functor _).obj _) _).op,
    rw [opens.le_def],
    dsimp,
    change coe '' (coe '' set.univ) ⊆ coe '' set.univ,
    rw [subtype.coe_image_univ, subtype.coe_image_univ],
    exact set.image_preimage_subset _ _ },
  { exact algebraic_geometry.Γ_restrict_is_localization Y r },
  { rw ← U.open_embedding_obj_top at hU,
    dsimp [Scheme.Γ_obj_op, Scheme.Γ_map_op, Scheme.restrict],
    apply algebraic_geometry.is_localization_of_eq_basic_open _ hU,
    rw [opens.open_embedding_obj_top, opens.functor_obj_map_obj],
    convert (X.basic_open_res (Scheme.Γ.map f.op r) (hom_of_le le_top).op).symm using 1,
    rw [opens.open_embedding_obj_top, opens.open_embedding_obj_top, inf_comm,
      Scheme.Γ_map_op, ← Scheme.preimage_basic_open],
    refl },
  { apply is_localization.ring_hom_ext (submonoid.powers r) _,
    swap, { exact algebraic_geometry.Γ_restrict_is_localization Y r },
    rw [is_localization.away.map, is_localization.map_comp, ring_hom.algebra_map_to_algebra,
      ring_hom.algebra_map_to_algebra, op_comp, functor.map_comp, op_comp, functor.map_comp],
    refine (@category.assoc CommRing _ _ _ _ _ _ _ _).symm.trans _,
    refine eq.trans _ (@category.assoc CommRing _ _ _ _ _ _ _ _),
    dsimp only [Scheme.Γ_map, quiver.hom.unop_op],
    rw [morphism_restrict_c_app, category.assoc, category.assoc, category.assoc],
    erw [f.1.c.naturality_assoc, ← X.presheaf.map_comp, ← X.presheaf.map_comp,
      ← X.presheaf.map_comp],
    congr },
end

lemma stable_under_base_change.Γ_pullback_fst
  (hP : stable_under_base_change @P) (hP' : respects_iso @P) {X Y S : Scheme}
  [is_affine X] [is_affine Y] [is_affine S]
  (f : X ⟶ S) (g : Y ⟶ S) (H : P (Scheme.Γ.map g.op)) :
    P (Scheme.Γ.map (pullback.fst : pullback f g ⟶ _).op) :=
begin
  rw [← preserves_pullback.iso_inv_fst AffineScheme.forget_to_Scheme
    (AffineScheme.of_hom f) (AffineScheme.of_hom g), op_comp, functor.map_comp,
    hP'.cancel_right_is_iso, AffineScheme.forget_to_Scheme_map],
  have := _root_.congr_arg quiver.hom.unop (preserves_pullback.iso_hom_fst AffineScheme.Γ.right_op
    (AffineScheme.of_hom f) (AffineScheme.of_hom g)),
  simp only [quiver.hom.unop_op, functor.right_op_map, unop_comp] at this,
  delta AffineScheme.Γ at this,
  simp only [quiver.hom.unop_op, functor.comp_map, AffineScheme.forget_to_Scheme_map,
    functor.op_map] at this,
  rw [← this, hP'.cancel_right_is_iso,
    ← pushout_iso_unop_pullback_inl_hom (quiver.hom.unop _) (quiver.hom.unop _),
    hP'.cancel_right_is_iso],
  exact hP.pushout_inl _ hP' _ _ H
end

end ring_hom
