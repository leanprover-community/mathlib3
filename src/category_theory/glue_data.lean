/-
Copyright (c) 2021 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import tactic.elementwise
import category_theory.limits.shapes.multiequalizer
import category_theory.limits.constructions.epi_mono
import category_theory.limits.preserves.limits
import category_theory.limits.shapes.types

/-!
# Gluing data

We define `glue_data` as a family of data needed to glue topological spaces, schemes, etc. We
provide the API to realize it as a multispan diagram, and also states lemmas about its
interaction with a functor that preserves certain pullbacks.

-/

noncomputable theory

open category_theory.limits
namespace category_theory

universes v u₁ u₂

variables (C : Type u₁) [category.{v} C] {C' : Type u₂} [category.{v} C']

/--
A gluing datum consists of
1. An index type `J`
2. An object `U i` for each `i : J`.
3. An object `V i j` for each `i j : J`.
4. A monomorphism `f i j : V i j ⟶ U i` for each `i j : J`.
5. A transition map `t i j : V i j ⟶ V j i` for each `i j : J`.
such that
6. `f i i` is an isomorphism.
7. `t i i` is the identity.
8. The pullback for `f i j` and `f i k` exists.
9. `V i j ×[U i] V i k ⟶ V i j ⟶ V j i` factors through `V j k ×[U j] V j i ⟶ V j i` via some
    `t' : V i j ×[U i] V i k ⟶ V j k ×[U j] V j i`.
10. `t' i j k ≫ t' j k i ≫ t' k i j = 𝟙 _`.
-/
@[nolint has_inhabited_instance]
structure glue_data :=
(J : Type v)
(U : J → C)
(V : J × J → C)
(f : Π i j, V (i, j) ⟶ U i)
(f_mono : ∀ i j, mono (f i j) . tactic.apply_instance)
(f_has_pullback : ∀ i j k, has_pullback (f i j) (f i k) . tactic.apply_instance)
(f_id : ∀ i, is_iso (f i i) . tactic.apply_instance)
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

@[simp] lemma t'_iij (i j : D.J) : D.t' i i j = (pullback_symmetry _ _).hom :=
begin
  have eq₁ := D.t_fac i i j,
  have eq₂ := (is_iso.eq_comp_inv (D.f i i)).mpr (@pullback.condition _ _ _ _ _ _ (D.f i j) _),
  rw [D.t_id, category.comp_id, eq₂] at eq₁,
  have eq₃ := (is_iso.eq_comp_inv (D.f i i)).mp eq₁,
  rw [category.assoc, ←pullback.condition, ←category.assoc] at eq₃,
  exact mono.right_cancellation _ _
    ((mono.right_cancellation _ _ eq₃).trans (pullback_symmetry_hom_comp_fst _ _).symm)
end

lemma t'_jii (i j : D.J) : D.t' j i i = pullback.fst ≫ D.t j i ≫ inv pullback.snd :=
by { rw [←category.assoc, ←D.t_fac], simp }

lemma t'_iji (i j : D.J) : D.t' i j i = pullback.fst ≫ D.t i j ≫ inv pullback.snd :=
by { rw [←category.assoc, ←D.t_fac], simp }

@[simp, reassoc, elementwise] lemma t_inv (i j : D.J) :
  D.t i j ≫ D.t j i = 𝟙 _ :=
begin
  have eq : (pullback_symmetry (D.f i i) (D.f i j)).hom = pullback.snd ≫ inv pullback.fst,
  { simp },
  have := D.cocycle i j i,
  rw [D.t'_iij, D.t'_jii, D.t'_iji, fst_eq_snd_of_mono_eq, eq] at this,
  simp only [category.assoc, is_iso.inv_hom_id_assoc] at this,
  rw [←is_iso.eq_inv_comp, ←category.assoc, is_iso.comp_inv_eq] at this,
  simpa using this,
end

lemma t'_inv (i j k : D.J) : D.t' i j k ≫ (pullback_symmetry _ _).hom ≫
  D.t' j i k ≫ (pullback_symmetry _ _).hom = 𝟙 _ :=
begin
  rw ← cancel_mono (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _),
  simp [t_fac, t_fac_assoc]
end

instance t_is_iso (i j : D.J) : is_iso (D.t i j) :=
⟨⟨D.t j i, D.t_inv _ _, D.t_inv _ _⟩⟩

instance t'_is_iso (i j k : D.J) : is_iso (D.t' i j k) :=
⟨⟨D.t' j k i ≫ D.t' k i j, D.cocycle _ _ _, (by simpa using D.cocycle _ _ _)⟩⟩

@[reassoc]
lemma t'_comp_eq_pullback_symmetry (i j k : D.J) :
  D.t' j k i ≫ D.t' k i j = (pullback_symmetry _ _).hom ≫
  D.t' j i k ≫ (pullback_symmetry _ _).hom :=
begin
  transitivity inv (D.t' i j k),
  { exact is_iso.eq_inv_of_hom_inv_id (D.cocycle _ _ _) },
  { rw ← cancel_mono (pullback.fst : pullback (D.f i j) (D.f i k) ⟶ _),
    simp [t_fac, t_fac_assoc] }
end

/-- (Implementation) The disjoint union of `U i`. -/
def sigma_opens [has_coproduct D.U] : C := ∐ D.U

/-- (Implementation) The diagram to take colimit of. -/
def diagram : multispan_index C :=
{ L := D.J × D.J, R := D.J,
  fst_from := _root_.prod.fst, snd_from := _root_.prod.snd,
  left := D.V, right := D.U,
  fst := λ ⟨i, j⟩, D.f i j,
  snd := λ ⟨i, j⟩, D.t i j ≫ D.f j i }

@[simp] lemma diagram_L : D.diagram.L = (D.J × D.J) := rfl
@[simp] lemma diagram_R : D.diagram.R = D.J := rfl
@[simp] lemma diagram_fst_from (i j : D.J) : D.diagram.fst_from ⟨i, j⟩ = i := rfl
@[simp] lemma diagram_snd_from (i j : D.J) : D.diagram.snd_from ⟨i, j⟩ = j := rfl
@[simp] lemma diagram_fst (i j : D.J) : D.diagram.fst ⟨i, j⟩ = D.f i j := rfl
@[simp] lemma diagram_snd (i j : D.J) : D.diagram.snd ⟨i, j⟩ = D.t i j ≫ D.f j i := rfl
@[simp] lemma diagram_left : D.diagram.left = D.V := rfl
@[simp] lemma diagram_right : D.diagram.right = D.U := rfl

section

variable [has_multicoequalizer D.diagram]

/-- The glued object given a family of gluing data. -/
def glued : C := multicoequalizer D.diagram

/-- The map `D.U i ⟶ D.glued` for each `i`. -/
def ι (i : D.J) : D.U i ⟶ D.glued :=
multicoequalizer.π D.diagram i

@[simp, elementwise]
lemma glue_condition (i j : D.J) :
  D.t i j ≫ D.f j i ≫ D.ι j = D.f i j ≫ D.ι i :=
(category.assoc _ _ _).symm.trans (multicoequalizer.condition D.diagram ⟨i, j⟩).symm

/-- The pullback cone spanned by `V i j ⟶ U i` and `V i j ⟶ U j`.
This will often be a pullback diagram. -/
 def V_pullback_cone (i j : D.J) : pullback_cone (D.ι i) (D.ι j) :=
 pullback_cone.mk (D.f i j) (D.t i j ≫ D.f j i) (by simp)

variables [has_colimits C]

/-- The projection `∐ D.U ⟶ D.glued` given by the colimit. -/
def π : D.sigma_opens ⟶ D.glued := multicoequalizer.sigma_π D.diagram

instance π_epi : epi D.π := by { unfold π, apply_instance }

end

lemma types_π_surjective (D : glue_data Type*) :
  function.surjective D.π := (epi_iff_surjective _).mp infer_instance

lemma types_ι_jointly_surjective (D : glue_data Type*) (x : D.glued) :
  ∃ i (y : D.U i), D.ι i y = x :=
begin
  delta category_theory.glue_data.ι,
  simp_rw ← multicoequalizer.ι_sigma_π D.diagram,
  rcases D.types_π_surjective x with ⟨x', rfl⟩,
  have := colimit.iso_colimit_cocone (types.coproduct_colimit_cocone _),
  rw ← (show (colimit.iso_colimit_cocone (types.coproduct_colimit_cocone _)).inv _ = x',
    from concrete_category.congr_hom
      ((colimit.iso_colimit_cocone (types.coproduct_colimit_cocone _)).hom_inv_id) x'),
  rcases (colimit.iso_colimit_cocone (types.coproduct_colimit_cocone _)).hom x' with ⟨i, y⟩,
  exact ⟨i, y, by { simpa [← multicoequalizer.ι_sigma_π, -multicoequalizer.ι_sigma_π] }⟩
end

variables (F : C ⥤ C') [H : ∀ i j k, preserves_limit (cospan (D.f i j) (D.f i k)) F]

include H

instance (i j k : D.J) : has_pullback (F.map (D.f i j)) (F.map (D.f i k)) :=
⟨⟨⟨_, is_limit_of_has_pullback_of_preserves_limit F (D.f i j) (D.f i k)⟩⟩⟩

/-- A functor that preserves the pullbacks of `f i j` and `f i k` can map a family of glue data. -/
@[simps] def map_glue_data :
  glue_data C' :=
{ J := D.J,
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

/--
The diagram of the image of a `glue_data` under a functor `F` is naturally isomorphic to the
original diagram of the `glue_data` via `F`.
-/
def diagram_iso : D.diagram.multispan ⋙ F ≅ (D.map_glue_data F).diagram.multispan :=
nat_iso.of_components
  (λ x, match x with
    | walking_multispan.left a := iso.refl _
    | walking_multispan.right b := iso.refl _
    end)
  (begin
    rintros (⟨_,_⟩|_) _ (_|_|_),
    { erw [category.comp_id, category.id_comp, functor.map_id], refl },
    { erw [category.comp_id, category.id_comp], refl },
    { erw [category.comp_id, category.id_comp, functor.map_comp], refl },
    { erw [category.comp_id, category.id_comp, functor.map_id], refl },
  end)

@[simp] lemma diagram_iso_app_left (i : D.J × D.J) :
  (D.diagram_iso F).app (walking_multispan.left i) = iso.refl _ := rfl

@[simp] lemma diagram_iso_app_right (i : D.J) :
  (D.diagram_iso F).app (walking_multispan.right i) = iso.refl _ := rfl

@[simp] lemma diagram_iso_hom_app_left (i : D.J × D.J) :
  (D.diagram_iso F).hom.app (walking_multispan.left i) = 𝟙 _ := rfl

@[simp] lemma diagram_iso_hom_app_right (i : D.J) :
  (D.diagram_iso F).hom.app (walking_multispan.right i) = 𝟙 _ := rfl

@[simp] lemma diagram_iso_inv_app_left (i : D.J × D.J) :
  (D.diagram_iso F).inv.app (walking_multispan.left i) = 𝟙 _ := rfl

@[simp] lemma diagram_iso_inv_app_right (i : D.J) :
  (D.diagram_iso F).inv.app (walking_multispan.right i) = 𝟙 _ := rfl

variables [has_multicoequalizer D.diagram] [preserves_colimit D.diagram.multispan F]

omit H

lemma has_colimit_multispan_comp : has_colimit (D.diagram.multispan ⋙ F) :=
⟨⟨⟨_,preserves_colimit.preserves (colimit.is_colimit _)⟩⟩⟩

include H

local attribute [instance] has_colimit_multispan_comp

lemma has_colimit_map_glue_data_diagram : has_multicoequalizer (D.map_glue_data F).diagram :=
has_colimit_of_iso (D.diagram_iso F).symm

local attribute [instance] has_colimit_map_glue_data_diagram

/-- If `F` preserves the gluing, we obtain an iso between the glued objects. -/
def glued_iso : F.obj D.glued ≅ (D.map_glue_data F).glued :=
preserves_colimit_iso F D.diagram.multispan ≪≫
  (limits.has_colimit.iso_of_nat_iso (D.diagram_iso F))

@[simp, reassoc]
lemma ι_glued_iso_hom (i : D.J) :
  F.map (D.ι i) ≫ (D.glued_iso F).hom = (D.map_glue_data F).ι i :=
by { erw ι_preserves_colimits_iso_hom_assoc, rw has_colimit.iso_of_nat_iso_ι_hom,
  erw category.id_comp, refl }

@[simp, reassoc]
lemma ι_glued_iso_inv (i : D.J) :
  (D.map_glue_data F).ι i ≫ (D.glued_iso F).inv = F.map (D.ι i) :=
by rw [iso.comp_inv_eq, ι_glued_iso_hom]

/-- If `F` preserves the gluing, and reflects the pullback of `U i ⟶ glued` and `U j ⟶ glued`,
then `F` reflects the fact that `V_pullback_cone` is a pullback. -/
def V_pullback_cone_is_limit_of_map (i j : D.J) [reflects_limit (cospan (D.ι i) (D.ι j)) F]
  (hc : is_limit ((D.map_glue_data F).V_pullback_cone i j)) :
  is_limit (D.V_pullback_cone i j) :=
begin
  apply is_limit_of_reflects F,
  apply (is_limit_map_cone_pullback_cone_equiv _ _).symm _,
  let e : cospan (F.map (D.ι i)) (F.map (D.ι j)) ≅
    cospan ((D.map_glue_data F).ι i) ((D.map_glue_data F).ι j),
  exact nat_iso.of_components
    (λ x, by { cases x, exacts [D.glued_iso F, iso.refl _] })
    (by rintros (_|_) (_|_) (_|_|_); simp),
  apply is_limit.postcompose_hom_equiv e _ _,
  apply hc.of_iso_limit,
  refine cones.ext (iso.refl _) _,
  { rintro (_|_|_),
    change _ = _ ≫ (_ ≫ _) ≫ _,
    all_goals { change _ = 𝟙 _ ≫ _ ≫ _, simpa } }
end

omit H

/-- If there is a forgetful functor into `Type` that preserves enough (co)limits, then `D.ι` will
be jointly surjective. -/
lemma ι_jointly_surjective (F : C ⥤ Type v) [preserves_colimit D.diagram.multispan F]
  [Π (i j k : D.J), preserves_limit (cospan (D.f i j) (D.f i k)) F] (x : F.obj (D.glued)) :
  ∃ i (y : F.obj (D.U i)), F.map (D.ι i) y = x :=
begin
  let e := D.glued_iso F,
  obtain ⟨i, y, eq⟩ := (D.map_glue_data F).types_ι_jointly_surjective (e.hom x),
  replace eq := congr_arg e.inv eq,
  change ((D.map_glue_data F).ι i ≫ e.inv) y = (e.hom ≫ e.inv) x at eq,
  rw [e.hom_inv_id, D.ι_glued_iso_inv] at eq,
  exact ⟨i, y, eq⟩
end

end glue_data

end category_theory
