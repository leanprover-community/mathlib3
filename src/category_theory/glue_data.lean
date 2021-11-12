/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import tactic.elementwise
import category_theory.limits.shapes.multiequalizer
import category_theory.limits.constructions.epi_mono

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

open category_theory.limits
namespace category_theory

universes v u₁ u₂

variables (C : Type u₁) [category.{v} C] {C' : Type u₂} [category.{v} C']

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
structure glue_data :=
  (ι : Type v)
  (U : ι → C)
  (V : ι × ι → C)
  (f : Π i j, V (i, j) ⟶ U i)
  (f_mono : ∀ i j, mono (f i j) . tactic.apply_instance)
  (f_has_pullback : ∀ i j k, has_pullback (f i j) (f i k) . tactic.apply_instance)
  (f_id : ∀ i, is_iso (f i i))
  (t : Π i j, V (i, j) ⟶ V (j, i))
  (t_id : ∀ i, t i i = 𝟙 _)
  (t' : Π i j k, pullback (f i j) (f i k) ⟶ pullback (f j k) (f j i))
  (t_fac : ∀ i j k, t' i j k ≫ pullback.snd = pullback.fst ≫ t i j)
  (cocycle : ∀ i j k , t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _)

attribute [simp] glue_data.t_id
attribute [instance] glue_data.f_id glue_data.f_mono glue_data.f_has_pullback
attribute [reassoc] glue_data.t_fac glue_data.cocycle

namespace glue_data

variables {C} (D : glue_data C)

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
def sigma_opens [has_coproduct D.U] : C := ∐ D.U

/-- (Implementation) The diagram to take colimit of. -/
def diagram : multispan_index C :=
{ L := D.ι × D.ι, R := D.ι,
  fst_from := _root_.prod.fst, snd_from := _root_.prod.snd,
  left := D.V, right := D.U,
  fst := λ ⟨i, j⟩, D.f i j,
  snd := λ ⟨i, j⟩, D.t i j ≫ D.f j i }

variable [has_multicoequalizer D.diagram]

/-- The glued topological space given a family of gluing data. -/
def glued : C := multicoequalizer D.diagram

/-- The open immersion `D.U i ⟶ D.glued` for each `i`. -/
def imm (i : D.ι) : D.U i ⟶ D.glued :=
multicoequalizer.π D.diagram i

variables [has_colimits C]

/-- (Implementation) The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
def π : D.sigma_opens ⟶ D.glued := multicoequalizer.sigma_π D.diagram

instance π_epi : epi D.π := by { unfold π, apply_instance }

variables (F : C ⥤ C') [H : ∀ i j k, preserves_limit (cospan (D.f i j) (D.f i k)) F]

include H

instance (i j k : D.ι) : has_pullback (F.map (D.f i j)) (F.map (D.f i k)) :=
⟨⟨⟨_, is_limit_of_has_pullback_of_preserves_limit F (D.f i j) (D.f i k)⟩⟩⟩

def map_glue_data :
  glue_data C' :=
{ ι := D.ι,
  U := λ i, F.obj (D.U i),
  V := λ i, F.obj (D.V i),
  f := λ i j, F.map (D.f i j),
  f_mono := λ i j, category_theory.preserves_mono F (D.f i j),
  f_id := λ i, infer_instance,
  t := λ i j, F.map (D.t i j),
  t_id := λ i, by { rw D.t_id i, simp },
  t' := λ i j k, (preserves_pullback.iso F (D.f i j) (D.f i k)).inv ≫
    F.map (D.t' i j k) ≫ (preserves_pullback.iso F (D.f j k) (D.f j i)).hom,
  t_fac := λ i j k, by simpa [iso.inv_comp_eq] using congr_arg (λ f, F.map f) (D.t_fac i j k),
  cocycle := λ i j k, by simp only [category.assoc, iso.hom_inv_id_assoc, ← functor.map_comp_assoc,
    D.cocycle, iso.inv_hom_id, category_theory.functor.map_id, category.id_comp] }

def diagram_iso : D.diagram.multispan ⋙ F ≅ (D.map_glue_data F).diagram.multispan :=
nat_iso.of_components
  (λ x, match x with
    | walking_multispan.left a := iso.refl _
    | walking_multispan.right b := iso.refl _
    end)
  (begin
    rintros (⟨_,_⟩|b) _ (_|_|_),
    all_goals
    { try { erw category.comp_id },
      try { erw category.id_comp },
      try { erw functor.map_id },
      try { erw functor.map_comp },
      refl },
  end)

end glue_data

end category_theory
