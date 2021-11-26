import algebraic_geometry.locally_ringed_space
import algebra.category.CommRing.constructions
import algebraic_geometry.open_immersion

namespace algebraic_geometry

universes v u

open category_theory category_theory.limits

namespace SheafedSpace

variables {C : Type u} [category.{v} C] [has_limits C]
variables {ι : Type v} (F : discrete ι ⥤ SheafedSpace C)

lemma sigma_ι_jointly_surjective (x : colimit F) :
  ∃ (i : ι) (y : F.obj i), (colimit.ι F i).base y = x :=
begin
  let e : (colimit F).carrier ≅ _ :=
    preserves_colimit_iso (SheafedSpace.forget _) _ ≪≫
      colim.map_iso discrete.nat_iso_functor ≪≫ Top.sigma_iso_sigma _,
  refine ⟨(e.hom x).1, (e.hom x).2, _⟩,
  apply (Top.mono_iff_injective e.hom).mp infer_instance,
  generalize : e.hom x = y,
  rw ← Top.comp_app,
  erw [ι_preserves_colimits_iso_hom_assoc (SheafedSpace.forget _), colimit.ι_map_assoc,
    Top.sigma_iso_sigma_hom_ι_apply],
  cases y,
  refl
end

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

noncomputable
def coproduct : LocallyRingedSpace :=
{ to_SheafedSpace := colimit (F ⋙ forget_to_SheafedSpace : _),
  local_ring := λ x, begin
    rcases SheafedSpace.sigma_ι_jointly_surjective (F ⋙ forget_to_SheafedSpace) x with ⟨i, y, ⟨⟩⟩,
    haveI : _root_.local_ring (((F ⋙ forget_to_SheafedSpace).obj i).to_PresheafedSpace.stalk y) :=
      (F.obj i).local_ring _,
    exact (as_iso (PresheafedSpace.stalk_map (colimit.ι (F ⋙ forget_to_SheafedSpace) i : _) y)
      ).symm.CommRing_iso_to_ring_equiv.local_ring
  end }

noncomputable
def coproduct_cofan : cocone F :=
{ X := coproduct F,
  ι := { app := λ j, ⟨colimit.ι (F ⋙ forget_to_SheafedSpace) j, infer_instance⟩ } }

section end

noncomputable
lemma coproduct_cofan_is_colimit : is_colimit (coproduct_cofan F) :=
{ desc := λ s, ⟨colimit.desc (F ⋙ forget_to_SheafedSpace) (forget_to_SheafedSpace.map_cocone s),
  begin
    intro x,
    rcases SheafedSpace.sigma_ι_jointly_surjective (F ⋙ forget_to_SheafedSpace) x with ⟨i, y, ⟨⟩⟩,
    have := PresheafedSpace.stalk_map.comp (colimit.ι (F ⋙ forget_to_SheafedSpace) i : _)
      (colimit.desc (F ⋙ forget_to_SheafedSpace) (forget_to_SheafedSpace.map_cocone s)) y,
    rw ← is_iso.comp_inv_eq at this,
    erw ← this,
    erw PresheafedSpace.stalk_map.congr_hom _ _
      (colimit.ι_desc (forget_to_SheafedSpace.map_cocone s) i : _),
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

section has_coequalizer

variables {X Y : LocallyRingedSpace.{u}} (f g : X ⟶ Y)

lemma coequalizer_π_app_is_local_ring_hom
  (U : topological_space.opens ((coequalizer f.val g.val).carrier)) :
  is_local_ring_hom ((coequalizer.π f.val g.val : _).c.app (opposite.op U)) :=
begin
  have := ι_comp_coequalizer_comparison f.1 g.1 SheafedSpace.forget_to_PresheafedSpace,
  rw ← preserves_coequalizer.iso_hom at this,
  erw PresheafedSpace.congr_app this.symm (opposite.op U),
  rw PresheafedSpace.comp_c_app,
  apply_with is_local_ring_hom_comp { instances := ff },
  { apply_instance },
  apply_with is_local_ring_hom_comp { instances := ff }, swap,
  { apply_instance },
  rw ← PresheafedSpace.colimit_presheaf_obj_iso_pointwise_limit_hom_π,
  apply_with is_local_ring_hom_comp { instances := ff }, swap,
  { apply_instance },
  dsimp,
  -- constructor,
  -- rintros a ha,
  -- rcases Top.presheaf.germ_exist _ _ a with ⟨U, hU, s, rfl⟩,
  -- erw PresheafedSpace.stalk_map_germ_apply (coequalizer.π f.val g.val : _) U ⟨_, hU⟩ at ha,
  -- have := RingedSpace.is_unit_res_of_is_unit_germ _ _ _ _ ha,
end


lemma coequalizer_π_stalk_is_local_ring_hom (x : Y) :
  is_local_ring_hom (PresheafedSpace.stalk_map (coequalizer.π f.val g.val : _) x) :=
begin
  constructor,
  rintros a ha,
  rcases Top.presheaf.germ_exist _ _ a with ⟨U, hU, s, rfl⟩,
  erw PresheafedSpace.stalk_map_germ_apply (coequalizer.π f.val g.val : _) U ⟨_, hU⟩ at ha,
  have := RingedSpace.is_unit_res_of_is_unit_germ _ _ _ _ ha,
end

noncomputable
def coequalizer : LocallyRingedSpace :=
{ to_SheafedSpace := coequalizer f.1 g.1,
  local_ring := λ x,
  begin
    haveI : nontrivial ((coequalizer f.val g.val).to_PresheafedSpace.stalk x),
    { rcases (Top.epi_iff_surjective (coequalizer.π f.val g.val).base).mp
        infer_instance x with ⟨y, rfl⟩,
      exact pullback_nonzero (PresheafedSpace.stalk_map (coequalizer.π f.val g.val : _) y)
        (ring_hom.map_zero _) (ring_hom.map_one _) },
    constructor,
    intro a,
    clear _inst,
    rcases (Top.epi_iff_surjective (coequalizer.π f.val g.val).base).mp
      infer_instance x with ⟨y, rfl⟩,
    have := (PresheafedSpace.stalk_map (coequalizer.π f.val g.val : _) y a),
  end }


end has_coequalizer

end LocallyRingedSpace

end algebraic_geometry
