/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import algebraic_geometry.locally_ringed_space
import algebraic_geometry.structure_sheaf
import data.equiv.transfer_instance

/-!
# $Spec R$ as a `LocallyRingedSpace`

We bundle the `structure_sheaf R` construction for `R : CommRing` as a `LocallyRingedSpace`.

## Future work

Make it a functor.

-/


noncomputable theory

namespace algebraic_geometry
open opposite
open category_theory

/--
Spec of a commutative ring, as a `SheafedSpace`.
-/
def Spec.SheafedSpace (R : CommRing) : SheafedSpace CommRing :=
{ carrier := Top.of (prime_spectrum R),
  ..structure_sheaf R }

def Spec.Top_functor : CommRingᵒᵖ ⥤ Top :=
{ obj := λ R, Top.of (prime_spectrum (unop R : CommRing)),
  map := λ R S f, {
    to_fun := prime_spectrum.comap f.unop,
    continuous_to_fun := prime_spectrum.comap_continuous f.unop
  },
  map_id' := λ R, continuous_map.ext $ λ x,
  begin
    -- tidy can solve this, but it takes too long
    simp only [continuous_map.coe_mk, Top.id_app, category_theory.unop_id],
    erw [prime_spectrum.comap_id, id.def],
  end,
}

def Spec.functor_to_SheafedSpace : CommRingᵒᵖ ⥤ SheafedSpace CommRing :=
{ obj := λ R, {
    carrier := Spec.Top_functor.obj R,
    ..structure_sheaf (unop R : CommRing)
  },
  map := λ R S f, {
    base := Spec.Top_functor.map f,
    c := {
      app := λ U, structure_sheaf.comap f.unop (unop U)
        ((topological_space.opens.map (Spec.Top_functor.map f)).obj (unop U)) (λ p, iff.rfl),
      naturality' := λ U V i, ring_hom.ext $ λ s, subtype.eq $ funext $ λ p,
      begin
        dsimp only [PresheafedSpace.mk_coe],
        rw [category_theory.comp_apply, structure_sheaf.comap_apply],
        refl,
      end
      }
    },
  map_id' := λ R, PresheafedSpace.ext _ _ (Spec.Top_functor.map_id R) $
    category_theory.nat_trans.ext _ _ $ funext $ λ U,
  begin
    dsimp only [PresheafedSpace.mk_coe,
      Top.presheaf.pushforward_obj_obj, Top.presheaf.pushforward_obj_map,
      functor.op_obj, functor.op_map, functor.comp_obj,
      nat_trans.comp_app, nat_trans.op_app,
      SheafedSpace.id_base, SheafedSpace.id_c_app,
      whisker_right_app, topological_space.opens.map_iso_inv_app,
      unop_op, unop_id],
    erw [PresheafedSpace.id_c_app, structure_sheaf.comap_id], swap,
    { rw [Spec.Top_functor.map_id, topological_space.opens.map_id_obj_unop] },
    rw [eq_to_hom_op, eq_to_hom_map, eq_to_hom_trans],
    refl,
  end,
  map_comp' := λ R S T f g,
    PresheafedSpace.ext _ _ (Spec.Top_functor.map_comp f g) $
    category_theory.nat_trans.ext _ _ $ funext $ λ U,
  begin
    dsimp only [PresheafedSpace.mk_coe,
      Top.presheaf.pushforward_obj_obj, Top.presheaf.pushforward_obj_map,
      functor.op_obj, functor.op_map, functor.comp_obj,
      nat_trans.comp_app, nat_trans.op_app,
      SheafedSpace.comp_base, SheafedSpace.comp_c_app,
      whisker_right_app, topological_space.opens.map_iso_inv_app,
      unop_op, unop_comp, eq_to_hom_refl, category_theory.op_id],
    rw [Top.presheaf.pushforward.comp_inv_app, ← category.assoc],
    dsimp only [Top.presheaf.pushforward_obj_obj, functor.op_obj, unop_op],
    rw ← (structure_sheaf (unop R : CommRing)).presheaf.map_id,
    erw structure_sheaf.comap_comp g.unop f.unop _
      ((topological_space.opens.map (Spec.Top_functor.map g)).obj (unop U)) _ _ _,
    change (_ ≫ _) ≫ _ = (_ ≫ _) ≫ _,
    refl,
  end
}

/--
Spec of a commutative ring, as a `PresheafedSpace`.
-/
def Spec.PresheafedSpace (R : CommRing) : PresheafedSpace CommRing :=
(Spec.SheafedSpace R).to_PresheafedSpace

/--
Spec of a commutative ring, as a `LocallyRingedSpace`.
-/
def Spec.LocallyRingedSpace (R : CommRing) : LocallyRingedSpace :=
{ local_ring := λ x, @@ring_equiv.local_ring _
    (show local_ring (localization.at_prime _), by apply_instance) _
    (category_theory.iso.CommRing_iso_to_ring_equiv $ stalk_iso R x).symm,
  .. Spec.SheafedSpace R }

end algebraic_geometry
