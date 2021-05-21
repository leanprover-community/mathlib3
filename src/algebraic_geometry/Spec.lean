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

universe u

namespace algebraic_geometry

open opposite

set_option profiler true

#check continuous_map.ext

/--
Spec of a commutative ring, as a `SheafedSpace`.
-/
def Spec.SheafedSpace : CommRingᵒᵖ ⥤ SheafedSpace CommRing :=
{ obj := λ R, {
    carrier := Spec.Top (unop R : CommRing),
    .. structure_sheaf (unop R : CommRing) },
  map := λ R S f, {
    base := {
      to_fun := prime_spectrum.comap f.unop,
      continuous_to_fun := prime_spectrum.comap_continuous f.unop },
    c := {
      app := λ U, by {
        refine structure_sheaf.comap _ _ f.unop (unop U)
          ((topological_space.opens.map _).obj (unop U)) (λ p, _), refl,
      },
      naturality' := sorry
    }
  },
  map_id' := λ R,
  begin
    apply algebraic_geometry.PresheafedSpace.ext, swap,
    { ext1 x, dsimp, erw prime_spectrum.comap_id, refl, },
    ext U s p,
    dsimp at *,
    erw [PresheafedSpace.id_c_app],
    sorry
  end,
  map_comp' := λ R S T f g,
  begin
    apply algebraic_geometry.PresheafedSpace.ext, swap,
    { ext1 x, dsimp, erw prime_spectrum.comap_comp, },
    ext U s p,
    dsimp at *,
    erw PresheafedSpace.comp_c_app,

  end,
}

#print Spec.SheafedSpace

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
