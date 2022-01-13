/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.presheafed_space.gluing

/-!
# Gluing Schemes

Given a family of gluing data of schemes, we may glue them together.

The construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `algebraic_geometry.PresheafedSpace.glue_data`: A structure containing the family of gluing data.
* `category_theory.glue_data.glued`: The glued presheafed space.
    This is defined as the multicoequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API
    can be used.
* `category_theory.glue_data.ι`: The immersion `ι i : U i ⟶ glued` for each `i : J`.

## Main results

* `algebraic_geometry.PresheafedSpace.glue_data.ι_is_open_immersion`: The map `ι i : U i ⟶ glued`
  is an open immersion for each `i : J`.

## Implementation details

All the hard work is done in `algebraic_geometry/presheafed_space/gluing.lean` where we glue
presheafed spaces, sheafed spaces, and locally ringed spaces.

-/

noncomputable theory

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
@[nolint has_inhabited_instance]
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
  { dsimp,
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

end glue_data

end Scheme

end algebraic_geometry
