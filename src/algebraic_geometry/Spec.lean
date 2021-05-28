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

universe u

noncomputable theory

namespace algebraic_geometry
open opposite
open category_theory

set_option profiler true

def Spec.Top_obj (R : CommRing) : Top := Top.of (prime_spectrum R)

@[simps] def Spec.Top_map {R S : CommRing} (f : R ⟶ S) :
  Spec.Top_obj S ⟶ Spec.Top_obj R :=
{ to_fun := prime_spectrum.comap f,
  continuous_to_fun := prime_spectrum.comap_continuous f }

@[simp] lemma Spec.Top_map_id (R : CommRing) :
  Spec.Top_map (𝟙 R) = 𝟙 (Spec.Top_obj R) :=
continuous_map.ext $ λ x,
by erw [Spec.Top_map_to_fun, prime_spectrum.comap_id, id.def, Top.id_app]

@[simp] lemma Spec.Top_map_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) :
  Spec.Top_map (f ≫ g) = Spec.Top_map g ≫ Spec.Top_map f :=
continuous_map.ext $ λ x,
begin
  dsimp only [Spec.Top_map_to_fun, Top.comp_app],
  erw prime_spectrum.comap_comp,
end

@[simps] def Spec.to_Top : CommRingᵒᵖ ⥤ Top :=
{ obj := λ R, Spec.Top_obj (unop R),
  map := λ R S f, Spec.Top_map f.unop,
  map_id' := λ R, by rw [unop_id, Spec.Top_map_id],
  map_comp' := λ R S T f g, by rw [unop_comp, Spec.Top_map_comp] }

/--
Spec of a commutative ring, as a `SheafedSpace`.
-/
@[simps] def Spec.SheafedSpace_obj (R : CommRing) : SheafedSpace CommRing :=
{ carrier := Spec.Top_obj R, ..structure_sheaf R }

@[simps] def Spec.comap {R S : CommRing} (f : R ⟶ S) :
  (structure_sheaf R).presheaf ⟶ Spec.Top_map f _* (structure_sheaf S).presheaf :=
{ app := λ U, structure_sheaf.comap f (unop U)
    ((topological_space.opens.map (Spec.Top_map f)).obj (unop U)) (λ p, iff.rfl),
  naturality' := λ U V i, ring_hom.ext $ λ s, subtype.eq $ funext $ λ p, rfl }

@[simps] def Spec.SheafedSpace_map {R S : CommRing} (f : R ⟶ S) :
  Spec.SheafedSpace_obj S ⟶ Spec.SheafedSpace_obj R :=
{ base := Spec.Top_map f,
  c := Spec.comap f }

@[simp] lemma Spec.SheafedSpace_map_id {R : CommRing} :
  Spec.SheafedSpace_map (𝟙 R) = 𝟙 (Spec.SheafedSpace_obj R) :=
PresheafedSpace.ext _ _ (Spec.Top_map_id R) $ category_theory.nat_trans.ext _ _ $ funext $ λ U,
begin
  dsimp,
  erw [PresheafedSpace.id_c_app, structure_sheaf.comap_id], swap,
    { rw [Spec.Top_map_id, topological_space.opens.map_id_obj_unop] },
  rw [eq_to_hom_op, eq_to_hom_map, eq_to_hom_trans],
  refl,
end

@[simp] lemma Spec.SheafedSpace_map_comp {R S T : CommRing} (f : R ⟶ S) (g : S ⟶ T) :
  Spec.SheafedSpace_map (f ≫ g) = Spec.SheafedSpace_map g ≫ Spec.SheafedSpace_map f :=
PresheafedSpace.ext _ _ (Spec.Top_map_comp f g) $ category_theory.nat_trans.ext _ _ $ funext $ λ U,
begin
  dsimp,
  erw [Top.presheaf.pushforward.comp_inv_app, ← category.assoc, category.comp_id,
    (structure_sheaf T).presheaf.map_id, category.comp_id, structure_sheaf.comap_comp],
  refl,
end

@[simps] def Spec.to_SheafedSpace : CommRingᵒᵖ ⥤ SheafedSpace CommRing :=
{ obj := λ R, Spec.SheafedSpace_obj (unop R),
  map := λ R S f, Spec.SheafedSpace_map f.unop,
  map_id' := λ R, by rw [unop_id, Spec.SheafedSpace_map_id],
  map_comp' := λ R S T f g, by rw [unop_comp, Spec.SheafedSpace_map_comp] }

/--
Spec of a commutative ring, as a `LocallyRingedSpace`.
-/
@[simps] def Spec.LocallyRingedSpace_obj (R : CommRing) : LocallyRingedSpace :=
{ local_ring := λ x, @@ring_equiv.local_ring _
    (show local_ring (localization.at_prime _), by apply_instance) _
    (category_theory.iso.CommRing_iso_to_ring_equiv $ stalk_iso R x).symm,
  .. Spec.SheafedSpace_obj R }

end algebraic_geometry
