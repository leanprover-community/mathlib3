/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import topology.gluing
import algebraic_geometry.presheafed_space.open_immersion
import algebraic_geometry.presheafed_space.has_colimits

/-!
# Gluing Topological spaces

Given a family of gluing data, consisting of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.

THe construction should be "sealed" and considered as a black box, while only using the API
provided.

## Main definitions

* `Top.gluing_data`: A structure containing the family of gluing data.
* `Top.gluing_data.glued`: The glued topological space.
    This is defined as the coequalizer of `∐ V i j ⇉ ∐ U i`, so that the general colimit API can
    be used.
* `Top.gluing_data.imm`: The immersion `imm i : U i ⟶ glued` for each `i : ι`.
* `Top.gluing_data.rel`: A relation on `Σ i, D.U i` defined by `⟨i, x⟩ ~ ⟨j, y⟩` iff
    `⟨i, x⟩ = ⟨j, y⟩` or `f i j x = y`. See `Top.gluing_data.imm_eq_iff_rel`.

## Main results

* `Top.gluing_data.is_open_iff`: A set in `glued` is open iff its preimage along each `imm i` is
    open.
* `Top.gluing_data.imm_jointly_surjective`: The `imm i`s are jointly surjective.
* `Top.gluing_data.glue_condition` : `f i j ≫ imm j = imm i`.
* `Top.gluing_data.rel_equiv`: `rel` is an equivalence relation.
* `Top.gluing_data.imm_eq_iff_rel`: `imm i x = imm j y ↔ ⟨i, x⟩ ~ ⟨j, y⟩`.
* `Top.gluing_data.image_inter`: The intersection of the images of `U i` and `U j` in `glued` is
    `V i j`.
* `Top.gluing_data.preimage_range`: The preimage of the image of `U i` in `U j` is `V i j`.
* `Top.gluing_data.preimage_image_eq_preimage_f`: The preimage of the image of some `U ⊆ U i` is
    given by the preimage along `f j i`.
* `Top.gluing_data.imm_open_embedding`: Each of the `imm i`s are open embeddings.

-/

noncomputable theory

open topological_space category_theory
open category_theory.limits algebraic_geometry.PresheafedSpace
namespace algebraic_geometry

universes v u

variables (C : Type u) [category.{v} C]

/--
A family of gluing data consists of
1. An index type `ι`
2. A topological space `U i` for each `i : ι`.
3. An open subset `V i j ⊆ U i` for each `i j : ι`.
4. A transition map `f i j : V i j ⟶ V j i` for each `i j : ι`.
such that
5. `V i i = U i`.
6. `f i i` is the identity.
7. `f i j x ∈ V j k` for all `x ∈ V i j ∩ V i k`.
8. `f i j ≫ f j k = f i k`.

We can then glue the topological spaces `U i` along `V i j`.
-/
@[nolint has_inhabited_instance]
structure glue_data : Type (max u v + 1) :=
  (ι : Type v)
  (U : ι → PresheafedSpace C)
  (V : ι × ι → PresheafedSpace C)
  (f : Π i j, V (i, j) ⟶ U i)
  (f_open : ∀ i j, open_immersion (f i j))
  (f_id : ∀ i, is_iso (f i i))
  (t : Π i j, V (i, j) ⟶ V (j, i))
  (t_id : ∀ i, t i i = 𝟙 _)
  (t' : Π i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i))
  (t_fac : ∀ i j k, t' i j k ≫ pullback.snd = pullback.fst ≫ t i j)
  (cocycle : ∀ i j k , t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _)


attribute [simp] glue_data.t_id
attribute [instance] glue_data.f_id glue_data.f_open
attribute [reassoc] glue_data.t_fac glue_data.cocycle

namespace glue_data

variables {C} (D : glue_data C) [has_limits C]

@[simp] lemma t'_iij (i j : D.ι) : D.t' i i j = (pullback_symmetry _ _).hom :=
begin
  have eq₁ := D.t_fac i i j,
  have eq₂ := (is_iso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _),
  rw [D.t_id, category.comp_id, eq₂] at eq₁,
  have eq₃ := (is_iso.eq_comp_inv (D.f i i)).mp eq₁,
  rw [category.assoc, ←pullback.condition, ←category.assoc] at eq₃,
  exact mono.right_cancellation _ _
    ((mono.right_cancellation _ _ eq₃).trans (pullback_symmetry_hom_comp_fst _ _).symm)
end

lemma t'_jii (i j : D.ι) : D.t' j i i = pullback.fst ≫ D.t j i ≫ inv pullback.snd :=
by { rw [←category.assoc, ←D.t_fac], simp }

lemma t'_iji (i j : D.ι) : D.t' i j i = pullback.fst ≫ D.t i j ≫ inv pullback.snd :=
by { rw [←category.assoc, ←D.t_fac], simp }

@[simp, reassoc, elementwise] lemma t_inv (i j : D.ι) :
  D.t i j ≫ D.t j i = 𝟙 _ :=
begin
  have eq : (pullback_symmetry (D.f i i) (D.f i j)).hom = pullback.snd ≫ inv pullback.fst,
  simp,
  have := D.cocycle i j i,
  rw [D.t'_iij, D.t'_jii, D.t'_iji, fst_eq_snd_of_mono_eq, eq] at this,
  simp only [category.assoc, is_iso.inv_hom_id_assoc] at this,
  rw [←is_iso.eq_inv_comp, ←category.assoc, is_iso.comp_inv_eq] at this,
  simpa using this,
end

instance t_is_iso (i j : D.ι) : is_iso (D.t i j) :=
⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩

instance t'_is_iso (i j k : D.ι) : is_iso (D.t' i j k) :=
⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, (by simpa using D.cocycle _ _ _)⟩⟩

/-- (Implementation) The disjoint union of `U i`. -/
def sigma_opens : PresheafedSpace C := ∐ D.U

/-- (Implementation) The disjoint union of `V i j`. -/
def sigma_inters : PresheafedSpace C := ∐ D.V

/-- (Implementation) The projection `∐ D.inters ⟶ ∐ D.U` via left projection. -/
def left_imm : D.sigma_inters ⟶ D.sigma_opens :=
sigma.desc (λ ⟨i, j⟩, D.f i j ≫ sigma.ι D.U i)

/-- (Implementation) The projection `∐ D.inters ⟶ ∐ D.U` via right projection. -/
def right_imm : D.sigma_inters ⟶ D.sigma_opens :=
sigma.desc (λ ⟨i, j⟩, D.t i j ≫ D.f j i ≫ sigma.ι D.U j)

/-- (Implementation) The diagram to take colimit of. -/
def diagram := parallel_pair D.left_imm D.right_imm

/-- The glued topological space given a family of gluing data. -/
def glued : PresheafedSpace C :=
coequalizer D.left_imm D.right_imm

/-- (Implementation) The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
def π : D.sigma_opens ⟶ D.glued :=
coequalizer.π _ _

instance π_epi : epi D.π :=
coequalizer.π_epi

/-- The open immersion `D.U i ⟶ D.glued` for each `i`. -/
def imm (i : D.ι) : D.U i ⟶ D.glued :=
sigma.ι _ _ ≫ D.π

def to_top_glue_data : Top.glue_data :=
{ ι := D.ι,
  U := λ i, (D.U i).carrier,
  V := λ i, (D.V i).carrier,
  f := λ i j, (D.f i j).base,
  f_open := λ i j, (D.f_open i j).base_open,
  f_id := λ i, infer_instance,
  t := λ i j, (D.t i j).base,
  t_id := λ i, by { rw D.t_id i, refl },
  t' := λ i j k, (pullback_carrier_iso_pullback _ _).inv ≫
    (forget C).map (D.t' i j k) ≫ (pullback_carrier_iso_pullback _ _).hom,
  t_fac := λ i j k, by simpa [iso.inv_comp_eq] using congr_arg hom.base (D.t_fac i j k),
  cocycle := λ i j k, by simpa [iso.inv_comp_eq] using
    congr_arg (λ f, hom.base f ≫ (pullback_carrier_iso_pullback (D.f i j) (D.f i k)).hom)
      (D.cocycle i j k) }

section end

@[simps]
def sigma_inters_carrier_iso : D.sigma_inters.carrier ≅ D.to_top_glue_data.sigma_inters :=
preserves_colimit_iso (PresheafedSpace.forget C) (discrete.functor D.V) ≪≫
  colim.map_iso (nat_iso.of_components (λ i, iso.refl _) (by { rintros _ _ ⟨⟨⟨⟩⟩⟩, simp }))

@[simps]
def sigma_opens_carrier_iso : D.sigma_opens.carrier ≅ D.to_top_glue_data.sigma_opens :=
preserves_colimit_iso (PresheafedSpace.forget C) (discrete.functor D.U) ≪≫
  colim.map_iso (nat_iso.of_components (λ i, iso.refl _) (by { rintros _ _ ⟨⟨⟨⟩⟩⟩, simp }))

lemma left_imm_naturality :
  D.sigma_inters_carrier_iso.inv ≫ D.left_imm.base =
    D.to_top_glue_data.left_imm ≫ D.sigma_opens_carrier_iso.inv :=
begin
  ext1,
  simp only [ι_preserves_colimits_iso_inv_assoc, functor.map_iso_inv,
    nat_iso.of_components.inv_app, sigma_opens_carrier_iso, colimit.ι_desc_assoc, iso.trans_inv,
    iso.refl_inv, colimit.ι_map_assoc, sigma_inters_carrier_iso, Top.glue_data.left_imm,
    category.assoc, left_imm, forget_map, cofan.mk_ι_app],
  rw ← comp_base,
  erw colimit.ι_desc,
  erw category.id_comp,
  simp only [cofan.mk_ι_app],
  delta left_imm,
  simp? [left_imm],
end

def glued_carrier_iso : D.glued.carrier ≅ D.to_top_glue_data.glued :=
begin
  refine preserves_colimit_iso (PresheafedSpace.forget C) (parallel_pair D.left_imm D.right_imm) ≪≫ colim.map_iso _,
  fapply nat_iso.of_components,
  { rintro ⟨⟩, exacts [D.sigma_inters_carrier_iso, D.sigma_opens_carrier_iso] },
  rintros X Y ⟨_|_|_⟩,
  dsimp,
  ext,
  simp[sigma_inters_carrier_iso, sigma_opens_carrier_iso],
end

lemma imm_open_embedding (i : D.ι) : open_embedding (D.imm i).base :=
begin
  have := preserves_colimit_iso (PresheafedSpace.forget C) (parallel_pair D.left_imm D.right_imm),
end

lemma lem (i : D.ι) (U : opens (D.U i)) :

end glue_data

end algebraic_geometry
