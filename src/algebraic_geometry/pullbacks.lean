/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.gluing
import category_theory.limits.opposites
import algebraic_geometry.Gamma_Spec_adjunction

/-!
# Fibred products of schemes

In this file we construct the fibred product of schemes via gluing.
We roughly follow [har77] Theorem 3.3.

In particular, the main construction is to show that for an open cover `{ Uᵢ }` of `X`, if there
exist fibred products `Uᵢ ×[Z] Y` for each `i`, then there exists a fibred product `X ×[Z] Y`.

Then, for constructing the fibred product for arbitrary schemes `X, Y, Z`, we can use the
construction to reduce to the case where `X, Y, Z` are all affine, where fibred products are
constructed via tensor products.

-/
universes v u
noncomputable theory

open category_theory category_theory.limits algebraic_geometry
namespace algebraic_geometry.Scheme

namespace pullback

variables {C : Type u} [category.{v} C]

variables {X Y Z : Scheme.{u}} (𝒰 : open_cover.{u} X) (f : X ⟶ Z) (g : Y ⟶ Z)
variables [∀ i, has_pullback (𝒰.map i ≫ f) g]

/-- The intersection of `Uᵢ ×[Z] Y` and `Uⱼ ×[Z] Y` is given by (Uᵢ ×[Z] Y) ×[X] Uⱼ -/
def V (i j : 𝒰.J) : Scheme :=
pullback ((pullback.fst : pullback ((𝒰.map i) ≫ f) g ⟶ _) ≫ (𝒰.map i)) (𝒰.map j)

/-- The canonical transition map `(Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ` given by the fact
that pullbacks are associative and symmetric. -/
def t (i j : 𝒰.J) : V 𝒰 f g i j ⟶ V 𝒰 f g j i :=
begin
  haveI : has_pullback (pullback.snd ≫ 𝒰.map i ≫ f) g :=
    has_pullback_assoc_symm (𝒰.map j) (𝒰.map i) (𝒰.map i ≫ f) g,
  haveI : has_pullback (pullback.snd ≫ 𝒰.map j ≫ f) g :=
    has_pullback_assoc_symm (𝒰.map i) (𝒰.map j) (𝒰.map j ≫ f) g,
  refine (pullback_symmetry _ _).hom ≫ _,
  refine (pullback_assoc _ _ _ _).inv ≫ _,
  change pullback _ _ ⟶ pullback _ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_assoc _ _ _ _).hom,
  refine pullback.map _ _ _ _ (pullback_symmetry _ _).hom (𝟙 _) (𝟙 _) _ _,
  rw [pullback_symmetry_hom_comp_snd_assoc, pullback.condition_assoc, category.comp_id],
  rw [category.comp_id, category.id_comp]
end

@[simp, reassoc]
lemma t_fst_fst (i j : 𝒰.J) : t 𝒰 f g i j ≫ pullback.fst ≫ pullback.fst = pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_fst_snd (i j : 𝒰.J) :
  t 𝒰 f g i j ≫ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_snd (i j : 𝒰.J) :
  t 𝒰 f g i j ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta t, simp }

lemma t_id (i : 𝒰.J) : t 𝒰 f g i i = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  { rw ← cancel_mono (𝒰.map i), simp [pullback.condition] },
  { simp },
  { rw ← cancel_mono (𝒰.map i), simp [pullback.condition] }
end

/-- The inclusion map of `V i j = (Uᵢ ×[Z] Y) ×[X] Uⱼ ⟶ Uᵢ ×[Z] Y`-/
abbreviation fV (i j : 𝒰.J) : V 𝒰 f g i j ⟶ pullback ((𝒰.map i) ≫ f) g := pullback.fst

/-- The map `((Xᵢ ×[Z] Y) ×[X] Xⱼ) ×[Xᵢ ×[Z] Y] ((Xᵢ ×[Z] Y) ×[X] Xₖ)` ⟶
  `((Xⱼ ×[Z] Y) ×[X] Xₖ) ×[Xⱼ ×[Z] Y] ((Xⱼ ×[Z] Y) ×[X] Xᵢ)` needed for gluing   -/
def t' (i j k : 𝒰.J) :
  pullback (fV 𝒰 f g i j) (fV 𝒰 f g i k) ⟶ pullback (fV 𝒰 f g j k) (fV 𝒰 f g j i) :=
begin
  refine (pullback_right_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_right_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (t 𝒰 f g i j) (𝟙 _) (𝟙 _) _ _,
  { simp [← pullback.condition] },
  { simp }
end

section end

@[simp, reassoc]
lemma t'_fst_fst_fst (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_fst (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by { delta t', simp, }

lemma cocycle_fst_fst_fst (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.fst ≫
  pullback.fst = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by simp

lemma cocycle_fst_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.fst ≫
  pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_snd_fst_fst (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.fst ≫
  pullback.fst = pullback.snd ≫ pullback.fst ≫ pullback.fst :=
by { rw ← cancel_mono (𝒰.map i), simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.fst ≫
  pullback.snd = pullback.snd ≫ pullback.fst ≫ pullback.snd :=
by { simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.snd =
    pullback.snd ≫ pullback.snd :=
by simp

-- `by tidy` should solve it, but it times out.
lemma cocycle (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  { apply pullback.hom_ext,
    { apply pullback.hom_ext,
      { simp_rw category.assoc,
        exact cocycle_fst_fst_fst 𝒰 f g i j k },
      { simp_rw category.assoc,
        exact cocycle_fst_fst_snd 𝒰 f g i j k } },
    { simp_rw category.assoc,
      exact cocycle_fst_snd 𝒰 f g i j k } },
  { apply pullback.hom_ext,
    { apply pullback.hom_ext,
      { simp_rw category.assoc,
        exact cocycle_snd_fst_fst 𝒰 f g i j k },
      { simp_rw category.assoc,
        exact cocycle_snd_fst_snd 𝒰 f g i j k } },
    { simp_rw category.assoc,
      exact cocycle_snd_snd 𝒰 f g i j k } }
end

/-- Given `Uᵢ ×[Z] Y`, this is the glued fibered product `X ×[Z] Y`. -/
@[simps]
def gluing : Scheme.glue_data.{u} :=
{ J := 𝒰.J,
  U := λ i, pullback ((𝒰.map i) ≫ f) g,
  V := λ ⟨i, j⟩, V 𝒰 f g i j, -- `p⁻¹(Uᵢ ∩ Uⱼ)` where `p : Uᵢ ×[Z] Y ⟶ Uᵢ ⟶ X`.
  f := λ i j, pullback.fst,
  f_id := λ i, infer_instance,
  f_open := infer_instance,
  t := λ i j, t 𝒰 f g i j,
  t_id := λ i, t_id 𝒰 f g i,
  t' := λ i j k, t' 𝒰 f g i j k,
  t_fac := λ i j k, begin
    apply pullback.hom_ext,
    apply pullback.hom_ext,
    all_goals { simp }
  end,
  cocycle := λ i j k, cocycle 𝒰 f g i j k }

/-- The first projection from the glued scheme into `X`. -/
def p1 : (gluing 𝒰 f g).glued ⟶ X :=
begin
  fapply multicoequalizer.desc,
  exact λ i, pullback.fst ≫ 𝒰.map i,
  rintro ⟨i, j⟩,
  change pullback.fst ≫ _ ≫ 𝒰.map i = (_ ≫ _) ≫ _ ≫ 𝒰.map j,
  rw pullback.condition,
  rw ← category.assoc,
  congr' 1,
  rw category.assoc,
  exact (t_fst_fst _ _ _ _ _).symm
end

/-- The second projection from the glued scheme into `Y`. -/
def p2 : (gluing 𝒰 f g).glued ⟶ Y :=
begin
  fapply multicoequalizer.desc,
  exact λ i, pullback.snd,
  rintro ⟨i, j⟩,
  change pullback.fst ≫ _ = (_ ≫ _) ≫ _,
  rw category.assoc,
  exact (t_fst_snd _ _ _ _ _).symm
end

lemma p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g :=
begin
  apply multicoequalizer.hom_ext,
  intro i,
  erw [multicoequalizer.π_desc_assoc, multicoequalizer.π_desc_assoc],
  rw [category.assoc, pullback.condition]
end

variable (s : pullback_cone f g)

/-- (Implementation)
The canonical map `(s.X ×[X] Uᵢ) ×[s.X] (s.X ×[X] Uⱼ) ⟶ (Uᵢ ×[Z] Y) ×[X] Uⱼ`

This is used in `glued_lift`. -/
def glued_lift_pullback_map (i j : 𝒰.J) :
  pullback ((𝒰.pullback_cover s.fst).map i) ((𝒰.pullback_cover s.fst).map j) ⟶
    (gluing 𝒰 f g).V ⟨i, j⟩ :=
begin
  change pullback pullback.fst pullback.fst ⟶ pullback _ _,
  refine (pullback_right_pullback_fst_iso _ _ _).hom ≫ _,
  refine pullback.map _ _ _ _ _ (𝟙 _) (𝟙 _) _ _,
  { exact (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition },
  { simpa using pullback.condition },
  { simp }
end

@[reassoc]
lemma glued_lift_pullback_map_fst (i j : 𝒰.J) :
  glued_lift_pullback_map 𝒰 f g s i j ≫ pullback.fst = pullback.fst ≫
    (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition :=
by { delta glued_lift_pullback_map, simp }

@[reassoc]
lemma glued_lift_pullback_map_snd (i j : 𝒰.J) :
  glued_lift_pullback_map 𝒰 f g s i j ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta glued_lift_pullback_map, simp }

/--
The lifted map `s.X ⟶ (gluing 𝒰 f g).glued` in order to show that `(gluing 𝒰 f g).glued` is
indeed the pullback.

Given a pullback cone `s`, we have the maps `s.fst ⁻¹' Uᵢ ⟶ Uᵢ` and
`s.fst ⁻¹' Uᵢ ⟶ s.X ⟶ Y` that we may lift to a map `s.fst ⁻¹' Uᵢ ⟶ Uᵢ ×[Z] Y`.

to glue these into a map `s.X ⟶ Uᵢ ×[Z] Y`, we need to show that the maps agree on
`(s.fst ⁻¹' Uᵢ) ×[s.X] (s.fst ⁻¹' Uⱼ) ⟶ Uᵢ ×[Z] Y`. This is achieved by showing that both of these
maps factors through `glued_lift_pullback_map`.
-/
def glued_lift : s.X ⟶ (gluing 𝒰 f g).glued :=
begin
  fapply (𝒰.pullback_cover s.fst).glue_morphisms,
  { exact λ i, (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition ≫
      (gluing 𝒰 f g).ι i },
  intros i j,
  rw ← glued_lift_pullback_map_fst_assoc,
  have : _ = pullback.fst ≫ _ := (gluing 𝒰 f g).glue_condition i j,
  rw [← this, gluing_to_glue_data_t, gluing_to_glue_data_f],
  simp_rw ← category.assoc,
  congr' 1,
  apply pullback.hom_ext; simp_rw category.assoc,
  { rw [t_fst_fst, glued_lift_pullback_map_snd],
    congr' 1,
    rw [← iso.inv_comp_eq, pullback_symmetry_inv_comp_snd],
    erw pullback.lift_fst,
    rw category.comp_id },
  { rw [t_fst_snd, glued_lift_pullback_map_fst_assoc],
    erw [pullback.lift_snd, pullback.lift_snd],
    rw [pullback_symmetry_hom_comp_snd_assoc, pullback_symmetry_hom_comp_snd_assoc],
    exact pullback.condition_assoc _ }
end

lemma glued_lift_p1 : glued_lift 𝒰 f g s ≫ p1 𝒰 f g = s.fst :=
begin
  rw ← cancel_epi (𝒰.pullback_cover s.fst).from_glued,
  apply multicoequalizer.hom_ext,
  intro b,
  erw [multicoequalizer.π_desc_assoc, multicoequalizer.π_desc_assoc],
  delta glued_lift,
  simp_rw ← category.assoc,
  rw (𝒰.pullback_cover s.fst).ι_glue_morphisms,
  simp_rw category.assoc,
  erw [multicoequalizer.π_desc, pullback.lift_fst_assoc, pullback.condition, category.comp_id],
  rw pullback_symmetry_hom_comp_fst_assoc,
end

lemma glued_lift_p2 : glued_lift 𝒰 f g s ≫ p2 𝒰 f g = s.snd :=
begin
  rw ← cancel_epi (𝒰.pullback_cover s.fst).from_glued,
  apply multicoequalizer.hom_ext,
  intro b,
  erw [multicoequalizer.π_desc_assoc, multicoequalizer.π_desc_assoc],
  delta glued_lift,
  simp_rw ← category.assoc,
  rw (𝒰.pullback_cover s.fst).ι_glue_morphisms,
  simp_rw category.assoc,
  erw [multicoequalizer.π_desc, pullback.lift_snd],
  rw pullback_symmetry_hom_comp_snd_assoc,
  refl
end

end pullback

end algebraic_geometry.Scheme
