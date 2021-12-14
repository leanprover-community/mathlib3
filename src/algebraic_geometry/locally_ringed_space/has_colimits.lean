/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.locally_ringed_space
import algebra.category.CommRing.constructions
import algebraic_geometry.open_immersion
import category_theory.limits.constructions.limits_of_products_and_equalizers

/-!
# Colimits of LocallyRingedSpace

We construct the explict coproducts of `LocallyRingedSpace`.

## TODO

Construct the explict coequalizers of `LocallyRingedSpace`.
It then follows that `LocallyRingedSpace` has all colimits, and
`forget_to_SheafedSpace` preserves them.

-/

namespace algebraic_geometry

universes v u

open category_theory category_theory.limits opposite

namespace SheafedSpace

variables {C : Type u} [category.{v} C] [has_limits C]
variables {J : Type v} [category.{v} J] (F : J ⥤ SheafedSpace C)

lemma is_colimit_exists_rep {c : cocone F} (hc : is_colimit c) (x : c.X) :
  ∃ (i : J) (y : F.obj i), (c.ι.app i).base y = x :=
concrete.is_colimit_exists_rep (F ⋙ SheafedSpace.forget _)
  (is_colimit_of_preserves (SheafedSpace.forget _) hc) x

lemma colimit_exists_rep (x : colimit F) :
  ∃ (i : J) (y : F.obj i), (colimit.ι F i).base y = x :=
concrete.is_colimit_exists_rep (F ⋙ SheafedSpace.forget _)
  (is_colimit_of_preserves (SheafedSpace.forget _) (colimit.is_colimit F)) x

instance {X Y : SheafedSpace C} (f g : X ⟶ Y) : epi (coequalizer.π f g).base :=
begin
  erw ← (show _ = (coequalizer.π f g).base, from
    ι_comp_coequalizer_comparison f g (SheafedSpace.forget C)),
  rw ← preserves_coequalizer.iso_hom,
  apply epi_comp
end

end SheafedSpace

namespace LocallyRingedSpace

section has_coproducts

variables {ι : Type u} (F : discrete ι ⥤ LocallyRingedSpace.{u})

/-- The explicit coproduct for `F : discrete ι ⥤ LocallyRingedSpace`. -/
noncomputable
def coproduct : LocallyRingedSpace :=
{ to_SheafedSpace := colimit (F ⋙ forget_to_SheafedSpace : _),
  local_ring := λ x, begin
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forget_to_SheafedSpace) x,
    haveI : _root_.local_ring (((F ⋙ forget_to_SheafedSpace).obj i).to_PresheafedSpace.stalk y) :=
      (F.obj i).local_ring _,
    exact (as_iso (PresheafedSpace.stalk_map (colimit.ι (F ⋙ forget_to_SheafedSpace) i : _) y)
      ).symm.CommRing_iso_to_ring_equiv.local_ring
  end }

/-- The explicit coproduct cofan for `F : discrete ι ⥤ LocallyRingedSpace`. -/
noncomputable
def coproduct_cofan : cocone F :=
{ X := coproduct F,
  ι := { app := λ j, ⟨colimit.ι (F ⋙ forget_to_SheafedSpace) j, infer_instance⟩ } }

/-- The explicit coproduct cofan constructed in `coproduct_cofan` is indeed a colimit. -/
noncomputable
def coproduct_cofan_is_colimit : is_colimit (coproduct_cofan F) :=
{ desc := λ s, ⟨colimit.desc (F ⋙ forget_to_SheafedSpace) (forget_to_SheafedSpace.map_cocone s),
  begin
    intro x,
    obtain ⟨i, y, ⟨⟩⟩ := SheafedSpace.colimit_exists_rep (F ⋙ forget_to_SheafedSpace) x,
    have := PresheafedSpace.stalk_map.comp (colimit.ι (F ⋙ forget_to_SheafedSpace) i : _)
      (colimit.desc (F ⋙ forget_to_SheafedSpace) (forget_to_SheafedSpace.map_cocone s)) y,
    rw ← is_iso.comp_inv_eq at this,
    erw [← this, PresheafedSpace.stalk_map.congr_hom _ _
      (colimit.ι_desc (forget_to_SheafedSpace.map_cocone s) i : _)],
    haveI : is_local_ring_hom (PresheafedSpace.stalk_map
      ((forget_to_SheafedSpace.map_cocone s).ι.app i) y) := (s.ι.app i).2 y,
    apply_instance
  end⟩,
  fac' := λ s j, subtype.eq (colimit.ι_desc _ _),
  uniq' := λ s f h, subtype.eq (is_colimit.uniq _ (forget_to_SheafedSpace.map_cocone s) f.1
    (λ j, congr_arg subtype.val (h j))) }

instance : has_coproducts LocallyRingedSpace.{u} :=
λ ι, ⟨λ F, ⟨⟨⟨_, coproduct_cofan_is_colimit F⟩⟩⟩⟩

noncomputable
instance (J : Type*) : preserves_colimits_of_shape (discrete J) forget_to_SheafedSpace :=
⟨λ G, preserves_colimit_of_preserves_colimit_cocone (coproduct_cofan_is_colimit G)
  ((colimit.is_colimit _).of_iso_colimit (cocones.ext (iso.refl _) (λ j, category.comp_id _)))⟩

end has_coproducts

end LocallyRingedSpace

end algebraic_geometry
