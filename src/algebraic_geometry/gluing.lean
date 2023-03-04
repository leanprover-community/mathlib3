/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.presheafed_space.gluing

/-!
# Gluing Schemes

Given a family of gluing data of schemes, we may glue them together.

## Main definitions

* `algebraic_geometry.Scheme.glue_data`: A structure containing the family of gluing data.
* `algebraic_geometry.Scheme.glue_data.glued`: The glued scheme.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `algebraic_geometry.Scheme.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.
* `algebraic_geometry.Scheme.glue_data.iso_carrier`: The isomorphism between the underlying space
  of the glued scheme and the gluing of the underlying topological spaces.
* `algebraic_geometry.Scheme.open_cover.glue_data`: The glue data associated with an open cover.
* `algebraic_geometry.Scheme.open_cover.from_glue_data`: The canonical morphism
  `𝒰.glue_data.glued ⟶ X`. This has an `is_iso` instance.
* `algebraic_geometry.Scheme.open_cover.glue_morphisms`: We may glue a family of compatible
  morphisms defined on an open cover of a scheme.

## Main results

* `algebraic_geometry.Scheme.glue_data.ι_is_open_immersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.
* `algebraic_geometry.Scheme.glue_data.ι_jointly_surjective` : The underlying maps of
  `ι i : U i ⟶ glued` are jointly surjective.
* `algebraic_geometry.Scheme.glue_data.V_pullback_cone_is_limit` : `V i j` is the pullback
  (intersection) of `U i` and `U j` over the glued space.
* `algebraic_geometry.Scheme.glue_data.ι_eq_iff_rel` : `ι i x = ι j y` if and only if they coincide
  when restricted to `V i i`.
* `algebraic_geometry.Scheme.glue_data.is_open_iff` : An subset of the glued scheme is open iff
  all its preimages in `U i` are open.

## Implementation details

All the hard work is done in `algebraic_geometry/presheafed_space/gluing.lean` where we glue
presheafed spaces, sheafed spaces, and locally ringed spaces.

-/

noncomputable theory

universe u

open topological_space category_theory opposite
open category_theory.limits algebraic_geometry.PresheafedSpace
open category_theory.glue_data

namespace algebraic_geometry

namespace Scheme

/--
A family of gluing data consists of
1. An index type `J`
2. An scheme `U i` for each `i : J`.
3. An scheme `V i j` for each `i j : J`.
  (Note that this is `J × J → Scheme` rather than `J → J → Scheme` to connect to the
  limits library easier.)
4. An open immersion `f i j : V i j ⟶ U i` for each `i j : ι`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : ι`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
9. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.

We can then glue the schemes `U i` together by identifying `V i j` with `V j i`, such
that the `U i`'s are open subschemes of the glued space.
-/
@[nolint has_nonempty_instance]
structure glue_data extends category_theory.glue_data Scheme :=
(f_open : ∀ i j, is_open_immersion (f i j))

attribute [instance] glue_data.f_open

namespace glue_data

variables (D : glue_data)

include D

local notation `𝖣` := D.to_glue_data

/-- The glue data of locally ringed spaces spaces associated to a family of glue data of schemes. -/
abbreviation to_LocallyRingedSpace_glue_data : LocallyRingedSpace.glue_data :=
{ f_open := D.f_open,
  to_glue_data := 𝖣 .map_glue_data forget_to_LocallyRingedSpace }

/-- (Implementation). The glued scheme of a glue data.
This should not be used outside this file. Use `Scheme.glue_data.glued` instead. -/
def glued_Scheme : Scheme :=
begin
  apply LocallyRingedSpace.is_open_immersion.Scheme
    D.to_LocallyRingedSpace_glue_data.to_glue_data.glued,
  intro x,
  obtain ⟨i, y, rfl⟩ := D.to_LocallyRingedSpace_glue_data.ι_jointly_surjective x,
  refine ⟨_, _ ≫ D.to_LocallyRingedSpace_glue_data.to_glue_data.ι i, _⟩,
  swap, exact (D.U i).affine_cover.map y,
  split,
  { dsimp [-set.mem_range],
    rw [coe_comp, set.range_comp],
    refine set.mem_image_of_mem _ _,
    exact (D.U i).affine_cover.covers y },
  { apply_instance },
end

instance : creates_colimit 𝖣 .diagram.multispan forget_to_LocallyRingedSpace :=
creates_colimit_of_fully_faithful_of_iso D.glued_Scheme
  (has_colimit.iso_of_nat_iso (𝖣 .diagram_iso forget_to_LocallyRingedSpace).symm)

instance : preserves_colimit 𝖣 .diagram.multispan forget_to_Top :=
begin
  delta forget_to_Top LocallyRingedSpace.forget_to_Top,
  apply_instance,
end

instance : has_multicoequalizer 𝖣 .diagram :=
has_colimit_of_created _ forget_to_LocallyRingedSpace

/-- The glued scheme of a glued space. -/
abbreviation glued : Scheme := 𝖣 .glued

/-- The immersion from `D.U i` into the glued space. -/
abbreviation ι (i : D.J) : D.U i ⟶ D.glued := 𝖣 .ι i

/-- The gluing as sheafed spaces is isomorphic to the gluing as presheafed spaces. -/
abbreviation iso_LocallyRingedSpace :
  D.glued.to_LocallyRingedSpace ≅ D.to_LocallyRingedSpace_glue_data.to_glue_data.glued :=
𝖣 .glued_iso forget_to_LocallyRingedSpace

lemma ι_iso_LocallyRingedSpace_inv (i : D.J) :
  D.to_LocallyRingedSpace_glue_data.to_glue_data.ι i ≫ D.iso_LocallyRingedSpace.inv = 𝖣 .ι i :=
𝖣 .ι_glued_iso_inv forget_to_LocallyRingedSpace i

instance ι_is_open_immersion (i : D.J) :
  is_open_immersion (𝖣 .ι i) :=
by { rw ← D.ι_iso_LocallyRingedSpace_inv, apply_instance }

lemma ι_jointly_surjective (x : 𝖣 .glued.carrier) :
  ∃ (i : D.J) (y : (D.U i).carrier), (D.ι i).1.base y = x :=
𝖣 .ι_jointly_surjective (forget_to_Top ⋙ forget Top) x

@[simp, reassoc]
lemma glue_condition (i j : D.J) :
  D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
𝖣 .glue_condition i j

/-- The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This is a pullback diagram (`V_pullback_cone_is_limit`). -/
def V_pullback_cone (i j : D.J) : pullback_cone (D.ι i) (D.ι j) :=
pullback_cone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

/-- The following diagram is a pullback, i.e. `Vᵢⱼ` is the intersection of `Uᵢ` and `Uⱼ` in `X`.

Vᵢⱼ ⟶ Uᵢ
 |      |
 ↓      ↓
 Uⱼ ⟶ X
-/
def V_pullback_cone_is_limit (i j : D.J) :
  is_limit (D.V_pullback_cone i j) :=
𝖣 .V_pullback_cone_is_limit_of_map forget_to_LocallyRingedSpace i j
  (D.to_LocallyRingedSpace_glue_data.V_pullback_cone_is_limit _ _)

/-- The underlying topological space of the glued scheme is isomorphic to the gluing of the
underlying spacess -/
def iso_carrier :
  D.glued.carrier ≅ D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
    .to_PresheafedSpace_glue_data.to_Top_glue_data.to_glue_data.glued :=
begin
  refine (PresheafedSpace.forget _).map_iso _ ≪≫
    glue_data.glued_iso _ (PresheafedSpace.forget _),
  refine SheafedSpace.forget_to_PresheafedSpace.map_iso _ ≪≫
    SheafedSpace.glue_data.iso_PresheafedSpace _,
  refine LocallyRingedSpace.forget_to_SheafedSpace.map_iso _ ≪≫
    LocallyRingedSpace.glue_data.iso_SheafedSpace _,
  exact Scheme.glue_data.iso_LocallyRingedSpace _
end

@[simp]
lemma ι_iso_carrier_inv (i : D.J) :
  D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
    .to_PresheafedSpace_glue_data.to_Top_glue_data.to_glue_data.ι i ≫ D.iso_carrier.inv =
    (D.ι i).1.base :=
begin
  delta iso_carrier,
  simp only [functor.map_iso_inv, iso.trans_inv, iso.trans_assoc,
    glue_data.ι_glued_iso_inv_assoc, functor.map_iso_trans, category.assoc],
  iterate 3 { erw ← comp_base },
  simp_rw ← category.assoc,
  rw D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data.ι_iso_PresheafedSpace_inv i,
  erw D.to_LocallyRingedSpace_glue_data.ι_iso_SheafedSpace_inv i,
  change (_ ≫ D.iso_LocallyRingedSpace.inv).1.base = _,
  rw D.ι_iso_LocallyRingedSpace_inv i
end

/-- An equivalence relation on `Σ i, D.U i` that holds iff `𝖣 .ι i x = 𝖣 .ι j y`.
See `Scheme.gluing_data.ι_eq_iff`. -/
def rel (a b : Σ i, ((D.U i).carrier : Type*)) : Prop :=
  a = b ∨ ∃ (x : (D.V (a.1, b.1)).carrier),
    (D.f _ _).1.base x = a.2 ∧ (D.t _ _ ≫ D.f _ _).1.base x = b.2

lemma ι_eq_iff (i j : D.J) (x : (D.U i).carrier) (y : (D.U j).carrier) :
  (𝖣 .ι i).1.base x = (𝖣 .ι j).1.base y ↔ D.rel ⟨i, x⟩ ⟨j, y⟩ :=
begin
  refine iff.trans _ (D.to_LocallyRingedSpace_glue_data.to_SheafedSpace_glue_data
      .to_PresheafedSpace_glue_data.to_Top_glue_data.ι_eq_iff_rel i j x y),
  rw ← ((Top.mono_iff_injective D.iso_carrier.inv).mp infer_instance).eq_iff,
    simp_rw [← comp_apply, D.ι_iso_carrier_inv]
end

lemma is_open_iff (U : set D.glued.carrier) : is_open U ↔ ∀ i, is_open ((D.ι i).1.base ⁻¹' U) :=
begin
  rw ← (Top.homeo_of_iso D.iso_carrier.symm).is_open_preimage,
  rw Top.glue_data.is_open_iff,
  apply forall_congr,
  intro i,
  erw [← set.preimage_comp, ← coe_comp, ι_iso_carrier_inv]
end

/-- The open cover of the glued space given by the glue data. -/
def open_cover (D : Scheme.glue_data) : open_cover D.glued :=
{ J := D.J,
  obj := D.U,
  map := D.ι,
  f := λ x, (D.ι_jointly_surjective x).some,
  covers := λ x, ⟨_, (D.ι_jointly_surjective x).some_spec.some_spec⟩ }

end glue_data

namespace open_cover

variables {X : Scheme.{u}} (𝒰 : open_cover.{u} X)

/-- (Implementation) the transition maps in the glue data associated with an open cover. -/
def glued_cover_t' (x y z : 𝒰.J) :
  pullback (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _)
    (pullback.fst : pullback (𝒰.map x) (𝒰.map z) ⟶ _) ⟶
  pullback (pullback.fst : pullback (𝒰.map y) (𝒰.map z) ⟶ _)
    (pullback.fst : pullback (𝒰.map y) (𝒰.map x) ⟶ _) :=
begin
  refine (pullback_right_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_right_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _,
  { simp [pullback.condition] },
  { simp }
end

@[simp, reassoc]
lemma glued_cover_t'_fst_fst (x y z : 𝒰.J) :
   𝒰.glued_cover_t' x y z ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_fst_snd (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_snd_fst (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ pullback.snd ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta glued_cover_t', simp }

@[simp, reassoc]
lemma glued_cover_t'_snd_snd (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta glued_cover_t', simp }

lemma glued_cover_cocycle_fst (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y ≫ pullback.fst =
    pullback.fst :=
by apply pullback.hom_ext; simp

lemma glued_cover_cocycle_snd (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y ≫ pullback.snd =
    pullback.snd :=
by apply pullback.hom_ext; simp [pullback.condition]

lemma glued_cover_cocycle (x y z : 𝒰.J) :
  glued_cover_t' 𝒰 x y z ≫ glued_cover_t' 𝒰 y z x ≫ glued_cover_t' 𝒰 z x y = 𝟙 _ :=
begin
  apply pullback.hom_ext; simp_rw [category.id_comp, category.assoc],
  apply glued_cover_cocycle_fst,
  apply glued_cover_cocycle_snd,
end

/-- The glue data associated with an open cover.
The canonical isomorphism `𝒰.glued_cover.glued ⟶ X` is provided by `𝒰.from_glued`. -/
@[simps]
def glued_cover : Scheme.glue_data.{u} :=
{ J := 𝒰.J,
  U := 𝒰.obj,
  V := λ ⟨x, y⟩, pullback (𝒰.map x) (𝒰.map y),
  f := λ x y, pullback.fst,
  f_id := λ x, infer_instance,
  t := λ x y, (pullback_symmetry _ _).hom,
  t_id := λ x, by simpa,
  t' := λ x y z, glued_cover_t' 𝒰 x y z,
  t_fac := λ x y z, by apply pullback.hom_ext; simp,
  -- The `cocycle` field could have been `by tidy` but lean timeouts.
  cocycle := λ x y z, glued_cover_cocycle 𝒰 x y z,
  f_open := λ x, infer_instance }

/-- The canonical morphism from the gluing of an open cover of `X` into `X`.
This is an isomorphism, as witnessed by an `is_iso` instance. -/
def from_glued : 𝒰.glued_cover.glued ⟶ X :=
begin
  fapply multicoequalizer.desc,
  exact λ x, (𝒰.map x),
  rintro ⟨x, y⟩,
  change pullback.fst ≫ _ = ((pullback_symmetry _ _).hom ≫ pullback.fst) ≫ _,
  simpa using pullback.condition
end

@[simp, reassoc]
lemma ι_from_glued (x : 𝒰.J) :
  𝒰.glued_cover.ι x ≫ 𝒰.from_glued = 𝒰.map x :=
multicoequalizer.π_desc _ _ _ _ _

lemma from_glued_injective : function.injective 𝒰.from_glued.1.base :=
begin
  intros x y h,
  obtain ⟨i, x, rfl⟩ := 𝒰.glued_cover.ι_jointly_surjective x,
  obtain ⟨j, y, rfl⟩ :=  𝒰.glued_cover.ι_jointly_surjective y,
  simp_rw [← comp_apply, ← SheafedSpace.comp_base, ← LocallyRingedSpace.comp_val] at h,
  erw [ι_from_glued, ι_from_glued] at h,
  let e := (Top.pullback_cone_is_limit _ _).cone_point_unique_up_to_iso
    (is_limit_of_has_pullback_of_preserves_limit Scheme.forget_to_Top
      (𝒰.map i) (𝒰.map j)),
  rw 𝒰.glued_cover.ι_eq_iff,
  right,
  use e.hom ⟨⟨x, y⟩, h⟩,
  simp_rw ← comp_apply,
  split,
  { erw is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.left, refl },
  { erw [pullback_symmetry_hom_comp_fst,
      is_limit.cone_point_unique_up_to_iso_hom_comp _ _ walking_cospan.right], refl }
end

instance from_glued_stalk_iso (x : 𝒰.glued_cover.glued.carrier) :
  is_iso (PresheafedSpace.stalk_map 𝒰.from_glued.val x) :=
begin
  obtain ⟨i, x, rfl⟩ := 𝒰.glued_cover.ι_jointly_surjective x,
  have := PresheafedSpace.stalk_map.congr_hom _ _
    (congr_arg LocallyRingedSpace.hom.val $ 𝒰.ι_from_glued i) x,
  erw PresheafedSpace.stalk_map.comp at this,
  rw ← is_iso.eq_comp_inv at this,
  rw this,
  apply_instance,
end

lemma from_glued_open_map : is_open_map 𝒰.from_glued.1.base :=
begin
  intros U hU,
  rw is_open_iff_forall_mem_open,
  intros x hx,
  rw 𝒰.glued_cover.is_open_iff at hU,
  use 𝒰.from_glued.val.base '' U ∩ set.range (𝒰.map (𝒰.f x)).1.base,
  use set.inter_subset_left _ _,
  split,
  { rw ← set.image_preimage_eq_inter_range,
    apply (show is_open_immersion (𝒰.map (𝒰.f x)), by apply_instance).base_open.is_open_map,
    convert hU (𝒰.f x) using 1,
    rw ← ι_from_glued, erw coe_comp, rw set.preimage_comp,
    congr' 1,
    refine set.preimage_image_eq _ 𝒰.from_glued_injective },
  { exact ⟨hx, 𝒰.covers x⟩ }
end

lemma from_glued_open_embedding : open_embedding 𝒰.from_glued.1.base :=
open_embedding_of_continuous_injective_open (by continuity) 𝒰.from_glued_injective
  𝒰.from_glued_open_map

instance : epi 𝒰.from_glued.val.base :=
begin
  rw Top.epi_iff_surjective,
  intro x,
  obtain ⟨y, h⟩ := 𝒰.covers x,
  use (𝒰.glued_cover.ι (𝒰.f x)).1.base y,
  rw ← comp_apply,
  rw ← 𝒰.ι_from_glued (𝒰.f x) at h,
  exact h
end

instance from_glued_open_immersion : is_open_immersion 𝒰.from_glued :=
SheafedSpace.is_open_immersion.of_stalk_iso _ 𝒰.from_glued_open_embedding

instance : is_iso 𝒰.from_glued :=
begin
  apply is_iso_of_reflects_iso _ (Scheme.forget_to_LocallyRingedSpace ⋙
    LocallyRingedSpace.forget_to_SheafedSpace ⋙ SheafedSpace.forget_to_PresheafedSpace),
  change @is_iso (PresheafedSpace _) _ _ _ 𝒰.from_glued.val,
  apply PresheafedSpace.is_open_immersion.to_iso,
end

/-- Given an open cover of `X`, and a morphism `𝒰.obj x ⟶ Y` for each open subscheme in the cover,
such that these morphisms are compatible in the intersection (pullback), we may glue the morphisms
together into a morphism `X ⟶ Y`.

Note:
If `X` is exactly (defeq to) the gluing of `U i`, then using `multicoequalizer.desc` suffices.
-/
def glue_morphisms {Y : Scheme} (f : ∀ x, 𝒰.obj x ⟶ Y)
  (hf : ∀ x y, (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _) ≫ f x = pullback.snd ≫ f y) :
  X ⟶ Y :=
begin
  refine inv 𝒰.from_glued ≫ _,
  fapply multicoequalizer.desc,
  exact f,
  rintro ⟨i, j⟩,
  change pullback.fst ≫ f i = (_ ≫ _) ≫ f j,
  erw pullback_symmetry_hom_comp_fst,
  exact hf i j
end

@[simp, reassoc]
lemma ι_glue_morphisms {Y : Scheme} (f : ∀ x, 𝒰.obj x ⟶ Y)
  (hf : ∀ x y, (pullback.fst : pullback (𝒰.map x) (𝒰.map y) ⟶ _) ≫ f x = pullback.snd ≫ f y)
  (x : 𝒰.J) : (𝒰.map x) ≫ 𝒰.glue_morphisms f hf = f x :=
begin
  rw [← ι_from_glued, category.assoc],
  erw [is_iso.hom_inv_id_assoc, multicoequalizer.π_desc],
end

lemma hom_ext {Y : Scheme} (f₁ f₂ : X ⟶ Y) (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂ :=
begin
  rw ← cancel_epi 𝒰.from_glued,
  apply multicoequalizer.hom_ext,
  intro x,
  erw multicoequalizer.π_desc_assoc,
  erw multicoequalizer.π_desc_assoc,
  exact h x,
end

end open_cover

end Scheme

end algebraic_geometry
