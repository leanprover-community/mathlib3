/-
Copyright (c) 2020 Markus Himmel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Markus Himmel, Scott Morrison
-/
import category_theory.subobject.factor_thru
import category_theory.subobject.well_powered
import category_theory.subobject.lattice
import category_theory.limits.comma
import category_theory.limits.constructions.epi_mono
import category_theory.limits.preserves.finite
import category_theory.limits.shapes.finite_limits

/-!
# Subobject in comma categories
-/

open_locale classical
noncomputable theory

open category_theory.limits

universes v u₁ u₂

namespace category_theory
variables {C : Type u₁} [category.{v} C] {D : Type u₂} [category.{v} D]

namespace structured_arrow
variables {S : D} {T : C ⥤ D}

instance proj_faithful : faithful (proj S T) :=
{ map_injective' := λ X Y f g h, comma_morphism.ext _ _ (subsingleton.elim _ _) h }

/-- If `A : S → T.obj B` is a structured arrow for `S : D` and `T : C ⥤ D`, then we can explicitly
    describe the subobjects of `A` as the subobjects of `P` of `B` in `C` so that `A.hom`
    factors through the image of `P` under `T`.

    We require `C` to have and `T` to preserve all limits. It is possible that this can be relaxed
    to require only certain limits. -/
def subobject_equiv [has_limits C] [preserves_limits T] (A : structured_arrow S T) :
  subobject A ≃o { P : subobject A.right // ∃ q, q ≫ T.map P.arrow = A.hom } :=
{ to_fun :=
  begin
    refine subobject.lift _ _,
    { introsI P f hf,
      refine ⟨subobject.mk ((proj S T).map f), ⟨P.hom ≫ T.map (subobject.underlying_iso _).inv, _⟩⟩,
      simp only [← functor.map_comp, category.assoc, subobject.underlying_iso_arrow, proj_map, w] },
    { introsI P Q f g hf hg i hi,
      refine subtype.ext (subobject.mk_eq_mk_of_comm _ _ ((proj S T).map_iso i) _),
      exact congr_arg comma_morphism.right hi }
  end,
  inv_fun := λ P,
  begin
    let t : mk P.prop.some ⟶ A := hom_mk P.val.arrow P.prop.some_spec,
    haveI : mono t,
    { apply (proj S T).mono_of_mono_map,
      dsimp, apply_instance },
    exact subobject.mk t
  end,
  left_inv :=
  begin
    refine subobject.ind _ _,
    introsI P f hf,
    dsimp,
    fapply subobject.mk_eq_mk_of_comm,
    { fapply iso_mk,
      { exact subobject.underlying_iso _ },
      { rw [← T.map_iso_hom],
        refine (cancel_mono (T.map ((proj S T).map f))).1 _,
        simp only [←T.map_comp, category.assoc, proj_map, w, mk_hom_eq_self, functor.map_iso_hom,
          subobject.underlying_iso_hom_comp_eq_mk],
        exact @Exists.some_spec _
          (λ q, q ≫ T.map (subobject.mk ((proj S T).map f)).arrow = A.hom) _ } },
    { refine comma_morphism.ext _ _ (subsingleton.elim _ _) _,
      simp only [subobject.underlying_iso_hom_comp_eq_mk, comma.comp_right, iso_mk_hom_right,
        hom_mk_right] }
  end,
  right_inv :=
  begin
    intro P,
    simp only [proj_map, hom_mk_right, subobject.mk_arrow, subtype.val_eq_coe, subobject.lift_mk,
      subtype.coe_eta],
  end,
  map_rel_iff' :=
  begin
    refine subobject.ind₂ _ _,
    introsI P Q f g hf hg,
    dsimp,
    refine ⟨λ h, _, λ h, _⟩,
    { refine subobject.mk_le_mk_of_comm _ _,
      { refine hom_mk (subobject.of_mk_le_mk _ _ h) ((cancel_mono (T.map ((proj S T).map g))).1 _),
        rw [category.assoc, ← T.map_comp, proj_map, w g, subobject.of_mk_le_mk_comp, w f] },
      { refine comma_morphism.ext _ _ (subsingleton.elim _ _) _,
        simp only [subobject.of_mk_le_mk_comp, comma.comp_right, hom_mk_right] } },
    { refine subobject.mk_le_mk_of_comm ((proj S T).map (subobject.of_mk_le_mk _ _ h)) _,
      exact congr_arg comma_morphism.right (subobject.of_mk_le_mk_comp h) }
  end }

/-- If `C` is well_powered and complete and `T` preserves_limits, then `structured_arrow S T` is
    well-powered. -/
instance well_powered_structured_arrow [well_powered C] [has_limits C] [preserves_limits T] :
  well_powered (structured_arrow S T) :=
{ subobject_small := λ X, small_of_injective (subobject_equiv X).injective }


end structured_arrow

end category_theory
