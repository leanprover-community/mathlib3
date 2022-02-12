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

We construct the explict coproducts and coequalizers of `LocallyRingedSpace`.
It then follows that `LocallyRingedSpace` has all colimits, and
`forget_to_SheafedSpace` preserves them.

-/

namespace algebraic_geometry

universes v u

open category_theory category_theory.limits opposite topological_space

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

section has_coequalizer

variables {X Y : LocallyRingedSpace.{u}} (f g : X ⟶ Y)

namespace has_coequalizer

instance coequalizer_π_app_is_local_ring_hom
  (U : topological_space.opens ((coequalizer f.val g.val).carrier)) :
  is_local_ring_hom ((coequalizer.π f.val g.val : _).c.app (op U)) :=
begin
  have := ι_comp_coequalizer_comparison f.1 g.1 SheafedSpace.forget_to_PresheafedSpace,
  rw ← preserves_coequalizer.iso_hom at this,
  erw SheafedSpace.congr_app this.symm (op U),
  rw [PresheafedSpace.comp_c_app,
    ← PresheafedSpace.colimit_presheaf_obj_iso_componentwise_limit_hom_π],
  apply_instance
end

/-!
We roughly follow the construction given in [MR0302656]. Given a pair `f, g : X ⟶ Y` of morphisms
of locally ringed spaces, we want to show that the stalk map of
`π = coequalizer.π f g` (as sheafed space homs) is a local ring hom. It then follows that
`coequalizer f g` is indeed a locally ringed space, and `coequalizer.π f g` is a morphism of
locally ringed space.

Given a germ `⟨U, s⟩` of `x : coequalizer f g` such that `π꙳ x : Y` is invertible, we ought to show
that `⟨U, s⟩` is invertible. That is, there exists an open set `U' ⊆ U` containing `x` such that the
restriction of `s` onto `U'` is invertible. This `U'` is given by `π '' V`, where `V` is the
basic open set of `π⋆x`.

Since `f ⁻¹' V = Y.basic_open (f ≫ π)꙳ x = Y.basic_open (g ≫ π)꙳ x = g ⁻¹' V`, we have
`π ⁻¹' (π '' V) = V` (as the underlying set map is merely the set-theoretic coequalizer).
This shows that `π '' V` is indeed open, and `s` is invertible on `π '' V` as the components of `π꙳`
are local ring homs.
-/
variable (U : opens ((coequalizer f.1 g.1).carrier))
variable (s : (coequalizer f.1 g.1).presheaf.obj (op U))

/-- (Implementation). The basic open set of the section `π꙳ s`. -/
noncomputable
def image_basic_open : opens Y := (Y.to_RingedSpace.basic_open
  (show Y.presheaf.obj (op (unop _)), from ((coequalizer.π f.1 g.1).c.app (op U)) s))

lemma image_basic_open_image_preimage :
  (coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base ''
    (image_basic_open f g U s).1) = (image_basic_open f g U s).1 :=
begin
  fapply types.coequalizer_preimage_image_eq_of_preimage_eq f.1.base g.1.base,
  { ext,
    simp_rw [types_comp_apply, ← Top.comp_app, ← PresheafedSpace.comp_base],
    congr' 2,
    exact coequalizer.condition f.1 g.1 },
  { apply is_colimit_cofork_map_of_is_colimit (forget Top),
    apply is_colimit_cofork_map_of_is_colimit (SheafedSpace.forget _),
    exact coequalizer_is_coequalizer f.1 g.1 },
  { suffices : (topological_space.opens.map f.1.base).obj (image_basic_open f g U s) =
      (topological_space.opens.map g.1.base).obj (image_basic_open f g U s),
    { injection this },
    delta image_basic_open,
    rw [preimage_basic_open f, preimage_basic_open g],
    dsimp only [functor.op, unop_op],
    rw [← comp_apply, ← SheafedSpace.comp_c_app', ← comp_apply, ← SheafedSpace.comp_c_app',
      SheafedSpace.congr_app (coequalizer.condition f.1 g.1), comp_apply],
    erw X.to_RingedSpace.basic_open_res,
    apply inf_eq_right.mpr,
    refine (RingedSpace.basic_open_subset _ _).trans _,
    rw coequalizer.condition f.1 g.1,
    exact λ _ h, h }
end

lemma image_basic_open_image_open :
  is_open ((coequalizer.π f.1 g.1).base '' (image_basic_open f g U s).1) :=
begin
  rw [← (Top.homeo_of_iso (preserves_coequalizer.iso (SheafedSpace.forget _) f.1 g.1))
      .is_open_preimage, Top.coequalizer_is_open_iff, ← set.preimage_comp],
  erw ← coe_comp,
  rw [preserves_coequalizer.iso_hom, ι_comp_coequalizer_comparison],
  dsimp only [SheafedSpace.forget],
  rw image_basic_open_image_preimage,
  exact (image_basic_open f g U s).2
end

instance coequalizer_π_stalk_is_local_ring_hom (x : Y) :
  is_local_ring_hom (PresheafedSpace.stalk_map (coequalizer.π f.val g.val : _) x) :=
begin
  constructor,
  rintros a ha,
  rcases Top.presheaf.germ_exist _ _ a with ⟨U, hU, s, rfl⟩,
  erw PresheafedSpace.stalk_map_germ_apply (coequalizer.π f.1 g.1 : _) U ⟨_, hU⟩ at ha,

  let V := image_basic_open f g U s,
  have hV : (coequalizer.π f.1 g.1).base ⁻¹' ((coequalizer.π f.1 g.1).base '' V.1) = V.1 :=
    image_basic_open_image_preimage f g U s,
  have hV' : V = ⟨(coequalizer.π f.1 g.1).base ⁻¹'
    ((coequalizer.π f.1 g.1).base '' V.1), hV.symm ▸ V.2⟩ := subtype.eq hV.symm,
  have V_open : is_open (((coequalizer.π f.val g.val).base) '' V.val) :=
    image_basic_open_image_open f g U s,
  have VleU :
    (⟨((coequalizer.π f.val g.val).base) '' V.val, V_open⟩ : topological_space.opens _) ≤ U,
  { exact set.image_subset_iff.mpr (Y.to_RingedSpace.basic_open_subset _) },
  have hxV : x ∈ V := ⟨⟨_, hU⟩, ha, rfl⟩,

  erw ← (coequalizer f.val g.val).presheaf.germ_res_apply (hom_of_le VleU)
    ⟨_, @set.mem_image_of_mem _ _ (coequalizer.π f.val g.val).base x V.1 hxV⟩ s,
  apply ring_hom.is_unit_map,
  rw [← is_unit_map_iff ((coequalizer.π f.val g.val : _).c.app _), ← comp_apply,
    nat_trans.naturality, comp_apply, Top.presheaf.pushforward_obj_map,
    ← is_unit_map_iff (Y.presheaf.map (eq_to_hom hV').op), ← comp_apply, ← functor.map_comp],
  convert @RingedSpace.is_unit_res_basic_open Y.to_RingedSpace (unop _)
    (((coequalizer.π f.val g.val).c.app (op U)) s),
  apply_instance
end

end has_coequalizer

/-- The coequalizer of two locally ringed space in the category of sheafed spaces is a locally
ringed space. -/
noncomputable
def coequalizer : LocallyRingedSpace :=
{ to_SheafedSpace := coequalizer f.1 g.1,
  local_ring := λ x,
  begin
    obtain ⟨y, rfl⟩ :=
      (Top.epi_iff_surjective (coequalizer.π f.val g.val).base).mp infer_instance x,
    exact (PresheafedSpace.stalk_map (coequalizer.π f.val g.val : _) y).domain_local_ring
  end }

/-- The explicit coequalizer cofork of locally ringed spaces. -/
noncomputable
def coequalizer_cofork : cofork f g :=
@cofork.of_π _ _ _ _ f g (coequalizer f g) ⟨coequalizer.π f.1 g.1, infer_instance⟩
  (subtype.eq (coequalizer.condition f.1 g.1))

lemma is_local_ring_hom_stalk_map_congr {X Y : RingedSpace} (f g : X ⟶ Y) (H : f = g)
  (x) (h : is_local_ring_hom (PresheafedSpace.stalk_map f x)) :
    is_local_ring_hom (PresheafedSpace.stalk_map g x) :=
by { rw PresheafedSpace.stalk_map.congr_hom _ _ H.symm x, apply_instance }

/-- The cofork constructed in `coequalizer_cofork` is indeed a colimit cocone. -/
noncomputable
def coequalizer_cofork_is_colimit : is_colimit (coequalizer_cofork f g) :=
begin
  apply cofork.is_colimit.mk',
  intro s,
  have e : f.val ≫ s.π.val = g.val ≫ s.π.val := by injection s.condition,
  use coequalizer.desc s.π.1 e,
  { intro x,
    rcases (Top.epi_iff_surjective (coequalizer.π f.val g.val).base).mp
      infer_instance x with ⟨y, rfl⟩,
    apply is_local_ring_hom_of_comp _ (PresheafedSpace.stalk_map (coequalizer_cofork f g).π.1 _),
    change is_local_ring_hom (_ ≫ PresheafedSpace.stalk_map (coequalizer_cofork f g).π.val y),
    erw ← PresheafedSpace.stalk_map.comp,
    apply is_local_ring_hom_stalk_map_congr _ _ (coequalizer.π_desc s.π.1 e).symm y,
    apply_instance },
  split,
  exact subtype.eq (coequalizer.π_desc _ _),
  intros m h,
  replace h : (coequalizer_cofork f g).π.1 ≫ m.1 = s.π.1 := by { rw ← h, refl },
  apply subtype.eq,
  apply (colimit.is_colimit (parallel_pair f.1 g.1)).uniq (cofork.of_π s.π.1 e) m.1,
  rintro ⟨⟩,
  { rw [← (colimit.cocone (parallel_pair f.val g.val)).w walking_parallel_pair_hom.left,
      category.assoc],
    change _ ≫ _ ≫ _ = _ ≫ _,
    congr,
    exact h },
  { exact h }
end


instance : has_coequalizer f g := ⟨⟨⟨_, coequalizer_cofork_is_colimit f g⟩⟩⟩

instance : has_coequalizers LocallyRingedSpace := has_coequalizers_of_has_colimit_parallel_pair _

noncomputable
instance preserves_coequalizer :
  preserves_colimits_of_shape walking_parallel_pair.{v} forget_to_SheafedSpace.{v} :=
⟨λ F, begin
  apply preserves_colimit_of_iso_diagram _ (diagram_iso_parallel_pair F).symm,
  apply preserves_colimit_of_preserves_colimit_cocone (coequalizer_cofork_is_colimit _ _),
  apply (is_colimit_map_cocone_cofork_equiv _ _).symm _,
  dsimp only [forget_to_SheafedSpace],
  exact coequalizer_is_coequalizer _ _
end⟩

end has_coequalizer

instance : has_colimits LocallyRingedSpace := colimits_from_coequalizers_and_coproducts

noncomputable
instance : preserves_colimits LocallyRingedSpace.forget_to_SheafedSpace :=
preserves_colimits_of_preserves_coequalizers_and_coproducts _

end LocallyRingedSpace

end algebraic_geometry
