/-
Copyright (c) 2022 Andrew Yang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Andrew Yang
-/
import algebraic_geometry.gluing
import category_theory.limits.opposites
import algebraic_geometry.AffineScheme
import category_theory.limits.shapes.diagonal

/-!
# Fibred products of schemes

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

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
begin
  delta t,
  simp only [category.assoc, id.def, pullback_symmetry_hom_comp_fst_assoc,
    pullback_assoc_hom_snd_fst, pullback.lift_fst_assoc, pullback_symmetry_hom_comp_snd,
    pullback_assoc_inv_fst_fst, pullback_symmetry_hom_comp_fst],
end

@[simp, reassoc]
lemma t_fst_snd (i j : 𝒰.J) :
  t 𝒰 f g i j ≫ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
begin
  delta t,
  simp only [pullback_symmetry_hom_comp_snd_assoc, category.comp_id, category.assoc, id.def,
    pullback_symmetry_hom_comp_fst_assoc, pullback_assoc_hom_snd_snd, pullback.lift_snd,
    pullback_assoc_inv_snd],
end

@[simp, reassoc]
lemma t_snd (i j : 𝒰.J) :
  t 𝒰 f g i j ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
begin
  delta t,
  simp only [pullback_symmetry_hom_comp_snd_assoc, category.assoc, id.def,
    pullback_symmetry_hom_comp_snd, pullback_assoc_hom_fst, pullback.lift_fst_assoc,
    pullback_symmetry_hom_comp_fst, pullback_assoc_inv_fst_snd],
end

lemma t_id (i : 𝒰.J) : t 𝒰 f g i i = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  { rw ← cancel_mono (𝒰.map i), simp only [pullback.condition, category.assoc, t_fst_fst] },
  { simp only [category.assoc, t_fst_snd]},
  { rw ← cancel_mono (𝒰.map i),simp only [pullback.condition, t_snd, category.assoc] }
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
  { simp only [←pullback.condition, category.comp_id, t_fst_fst_assoc] },
  { simp only [category.comp_id, category.id_comp]}
end

section end

@[simp, reassoc]
lemma t'_fst_fst_fst (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
begin
  delta t',
  simp only [category.assoc, pullback_symmetry_hom_comp_fst_assoc,
    pullback_right_pullback_fst_iso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullback_right_pullback_fst_iso_hom_fst_assoc],
end

@[simp, reassoc]
lemma t'_fst_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
begin
  delta t',
  simp only [category.assoc, pullback_symmetry_hom_comp_fst_assoc,
    pullback_right_pullback_fst_iso_inv_snd_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullback_right_pullback_fst_iso_hom_fst_assoc],
end

@[simp, reassoc]
lemma t'_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
begin
  delta t',
  simp only [category.comp_id, category.assoc, pullback_symmetry_hom_comp_fst_assoc,
    pullback_right_pullback_fst_iso_inv_snd_snd, pullback.lift_snd,
    pullback_right_pullback_fst_iso_hom_snd],
end

@[simp, reassoc]
lemma t'_snd_fst_fst (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
begin
  delta t',
  simp only [category.assoc, pullback_symmetry_hom_comp_snd_assoc,
    pullback_right_pullback_fst_iso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_fst,
    pullback_right_pullback_fst_iso_hom_fst_assoc],
end

@[simp, reassoc]
lemma t'_snd_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
begin
  delta t',
  simp only [category.assoc, pullback_symmetry_hom_comp_snd_assoc,
    pullback_right_pullback_fst_iso_inv_fst_assoc, pullback.lift_fst_assoc, t_fst_snd,
    pullback_right_pullback_fst_iso_hom_fst_assoc],
end

@[simp, reassoc]
lemma t'_snd_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
begin
  delta t',
  simp only [category.assoc, pullback_symmetry_hom_comp_snd_assoc,
    pullback_right_pullback_fst_iso_inv_fst_assoc, pullback.lift_fst_assoc, t_snd,
    pullback_right_pullback_fst_iso_hom_fst_assoc],
end

lemma cocycle_fst_fst_fst (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.fst ≫
  pullback.fst = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by simp only [t'_fst_fst_fst, t'_fst_snd, t'_snd_snd]

lemma cocycle_fst_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.fst ≫
  pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by simp only [t'_fst_fst_snd]

lemma cocycle_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.snd :=
by simp only [t'_fst_snd, t'_snd_snd, t'_fst_fst_fst]

lemma cocycle_snd_fst_fst (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.fst ≫
  pullback.fst = pullback.snd ≫ pullback.fst ≫ pullback.fst :=
begin
  rw ← cancel_mono (𝒰.map i),
  simp only [pullback.condition_assoc, t'_snd_fst_fst, t'_fst_snd, t'_snd_snd]
end

lemma cocycle_snd_fst_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.fst ≫
  pullback.snd = pullback.snd ≫ pullback.fst ≫ pullback.snd :=
by simp only [pullback.condition_assoc, t'_snd_fst_snd]

lemma cocycle_snd_snd (i j k : 𝒰.J) :
  t' 𝒰 f g i j k ≫ t' 𝒰 f g j k i ≫ t' 𝒰 f g k i j ≫ pullback.snd ≫ pullback.snd =
    pullback.snd ≫ pullback.snd :=
by simp only [t'_snd_snd, t'_fst_fst_fst, t'_fst_snd]

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
    all_goals { simp only [t'_snd_fst_fst, t'_snd_fst_snd, t'_snd_snd,
      t_fst_fst, t_fst_snd, t_snd, category.assoc] }
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
  { simp only [category.comp_id, category.id_comp] }
end

@[reassoc]
lemma glued_lift_pullback_map_fst (i j : 𝒰.J) :
  glued_lift_pullback_map 𝒰 f g s i j ≫ pullback.fst = pullback.fst ≫
    (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition :=
begin
  delta glued_lift_pullback_map,
  simp only [category.assoc, id.def, pullback.lift_fst,
    pullback_right_pullback_fst_iso_hom_fst_assoc],
end
@[reassoc]
lemma glued_lift_pullback_map_snd (i j : 𝒰.J) :
  glued_lift_pullback_map 𝒰 f g s i j ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
begin
  delta glued_lift_pullback_map,
  simp only [category.assoc, category.comp_id, id.def, pullback.lift_snd,
    pullback_right_pullback_fst_iso_hom_snd],
end

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

/-- (Implementation)
The canonical map `(W ×[X] Uᵢ) ×[W] (Uⱼ ×[Z] Y) ⟶ (Uⱼ ×[Z] Y) ×[X] Uᵢ = V j i` where `W` is
the glued fibred product.

This is used in `lift_comp_ι`. -/
def pullback_fst_ι_to_V (i j : 𝒰.J) :
  pullback (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map i) ⟶ _) ((gluing 𝒰 f g).ι j) ⟶
    V 𝒰 f g j i :=
(pullback_symmetry _ _ ≪≫
  (pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map i) _)).hom ≫
    (pullback.congr_hom (multicoequalizer.π_desc _ _ _ _ _) rfl).hom

@[simp, reassoc] lemma pullback_fst_ι_to_V_fst (i j : 𝒰.J) :
  pullback_fst_ι_to_V 𝒰 f g i j ≫ pullback.fst = pullback.snd :=
begin
  delta pullback_fst_ι_to_V,
  simp only [iso.trans_hom, pullback.congr_hom_hom, category.assoc, pullback.lift_fst,
    category.comp_id, pullback_right_pullback_fst_iso_hom_fst, pullback_symmetry_hom_comp_fst],
end

@[simp, reassoc] lemma pullback_fst_ι_to_V_snd (i j : 𝒰.J) :
  pullback_fst_ι_to_V 𝒰 f g i j ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
begin
  delta pullback_fst_ι_to_V,
  simp only [iso.trans_hom, pullback.congr_hom_hom, category.assoc, pullback.lift_snd,
    category.comp_id, pullback_right_pullback_fst_iso_hom_snd, pullback_symmetry_hom_comp_snd_assoc]
end
/-- We show that the map `W ×[X] Uᵢ ⟶ Uᵢ ×[Z] Y ⟶ W` is the first projection, where the
first map is given by the lift of `W ×[X] Uᵢ ⟶ Uᵢ` and `W ×[X] Uᵢ ⟶ W ⟶ Y`.

It suffices to show that the two map agrees when restricted onto `Uⱼ ×[Z] Y`. In this case,
both maps factor through `V j i` via `pullback_fst_ι_to_V` -/
lemma lift_comp_ι (i : 𝒰.J) : pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
  (by rw [← pullback.condition_assoc, category.assoc, p_comm]) ≫
  (gluing 𝒰 f g).ι i = (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map i) ⟶ _) :=
begin
  apply ((gluing 𝒰 f g).open_cover.pullback_cover pullback.fst).hom_ext,
  intro j,
  dsimp only [open_cover.pullback_cover],
  transitivity pullback_fst_ι_to_V 𝒰 f g i j ≫ fV 𝒰 f g j i ≫ (gluing 𝒰 f g).ι _,
  { rw ← (show _ = fV 𝒰 f g j i ≫ _, from (gluing 𝒰 f g).glue_condition j i),
    simp_rw ← category.assoc,
    congr' 1,
    rw [gluing_to_glue_data_f, gluing_to_glue_data_t],
    apply pullback.hom_ext; simp_rw category.assoc,
    { rw [t_fst_fst, pullback.lift_fst, pullback_fst_ι_to_V_snd] },
    { rw [t_fst_snd, pullback.lift_snd, pullback_fst_ι_to_V_fst_assoc,
        pullback.condition_assoc], erw multicoequalizer.π_desc } },
  { rw [pullback.condition, ← category.assoc],
    congr' 1,
    apply pullback.hom_ext,
    { simp only [pullback_fst_ι_to_V_fst] },
    { simp only [pullback_fst_ι_to_V_fst] } }
end

/-- The canonical isomorphism between `W ×[X] Uᵢ` and `Uᵢ ×[X] Y`. That is, the preimage of `Uᵢ` in
`W` along `p1` is indeed `Uᵢ ×[X] Y`. -/
def pullback_p1_iso (i : 𝒰.J) :
  pullback (p1 𝒰 f g) (𝒰.map i) ≅ pullback (𝒰.map i ≫ f) g :=
begin
  fsplit,
  exact pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
    (by rw [← pullback.condition_assoc, category.assoc, p_comm]),
  refine pullback.lift ((gluing 𝒰 f g).ι i) pullback.fst
    (by erw multicoequalizer.π_desc),
  { apply pullback.hom_ext,
    { simpa using lift_comp_ι 𝒰 f g i },
    { simp only [category.assoc, pullback.lift_snd, pullback.lift_fst, category.id_comp] } },
  { apply pullback.hom_ext,
    { simp only [category.assoc, pullback.lift_fst, pullback.lift_snd, category.id_comp] },
    { simp only [category.assoc, pullback.lift_snd, pullback.lift_fst_assoc, category.id_comp],
      erw multicoequalizer.π_desc } },
end

@[simp, reassoc] lemma pullback_p1_iso_hom_fst (i : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g i).hom ≫ pullback.fst = pullback.snd :=
by { delta pullback_p1_iso, simp only [pullback.lift_fst] }

@[simp, reassoc] lemma pullback_p1_iso_hom_snd (i : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g i).hom ≫ pullback.snd = pullback.fst ≫ p2 𝒰 f g :=
by { delta pullback_p1_iso, simp only [pullback.lift_snd] }

@[simp, reassoc] lemma pullback_p1_iso_inv_fst (i : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g i).inv ≫ pullback.fst = (gluing 𝒰 f g).ι i :=
by { delta pullback_p1_iso, simp only [pullback.lift_fst] }

@[simp, reassoc] lemma pullback_p1_iso_inv_snd (i : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g i).inv ≫ pullback.snd = pullback.fst :=
by { delta pullback_p1_iso, simp only [pullback.lift_snd] }

@[simp, reassoc]
lemma pullback_p1_iso_hom_ι (i : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g i).hom ≫ (gluing 𝒰 f g).ι i = pullback.fst :=
by rw [← pullback_p1_iso_inv_fst, iso.hom_inv_id_assoc]

/-- The glued scheme (`(gluing 𝒰 f g).glued`) is indeed the pullback of `f` and `g`. -/
def glued_is_limit : is_limit (pullback_cone.mk _ _ (p_comm 𝒰 f g)) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  refine ⟨glued_lift 𝒰 f g s, glued_lift_p1 𝒰 f g s, glued_lift_p2 𝒰 f g s, _⟩,
  intros m h₁ h₂,
  change m ≫ p1 𝒰 f g = _ at h₁,
  change m ≫ p2 𝒰 f g = _ at h₂,
  apply (𝒰.pullback_cover s.fst).hom_ext,
  intro i,
  rw open_cover.pullback_cover_map,
  have := pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map i) m
    ≪≫ pullback.congr_hom h₁ rfl,
  erw (𝒰.pullback_cover s.fst).ι_glue_morphisms,
  rw [← cancel_epi (pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map i) m
    ≪≫ pullback.congr_hom h₁ rfl).hom, iso.trans_hom, category.assoc, pullback.congr_hom_hom,
    pullback.lift_fst_assoc, category.comp_id, pullback_right_pullback_fst_iso_hom_fst_assoc,
    pullback.condition],
  transitivity pullback.snd ≫ (pullback_p1_iso 𝒰 f g _).hom ≫ (gluing 𝒰 f g).ι _,
  { congr' 1, rw ← pullback_p1_iso_hom_ι },
  simp_rw ← category.assoc,
  congr' 1,
  apply pullback.hom_ext,
  { simp only [category.comp_id, pullback_right_pullback_fst_iso_hom_snd, category.assoc,
      pullback_p1_iso_hom_fst, pullback.lift_snd, pullback.lift_fst,
      pullback_symmetry_hom_comp_fst] },
  { simp only [category.comp_id, pullback_right_pullback_fst_iso_hom_fst_assoc,
    pullback_p1_iso_hom_snd, category.assoc, pullback.lift_fst_assoc,
    pullback_symmetry_hom_comp_snd_assoc, pullback.lift_snd],
    rw [← pullback.condition_assoc, h₂] }
end

lemma has_pullback_of_cover : has_pullback f g := ⟨⟨⟨_, glued_is_limit 𝒰 f g⟩⟩⟩

instance affine_has_pullback {A B C : CommRing}
  (f : Spec.obj (opposite.op A) ⟶ Spec.obj (opposite.op C))
  (g : Spec.obj (opposite.op B) ⟶ Spec.obj (opposite.op C)) : has_pullback f g :=
begin
  rw [← Spec.image_preimage f, ← Spec.image_preimage g],
  exact ⟨⟨⟨_,is_limit_of_has_pullback_of_preserves_limit
    Spec (Spec.preimage f) (Spec.preimage g)⟩⟩⟩
end

lemma affine_affine_has_pullback {B C : CommRing} {X : Scheme}
  (f : X ⟶ Spec.obj (opposite.op C))
  (g : Spec.obj (opposite.op B) ⟶ Spec.obj (opposite.op C)) : has_pullback f g :=
has_pullback_of_cover X.affine_cover f g

instance base_affine_has_pullback {C : CommRing} {X Y : Scheme}
  (f : X ⟶ Spec.obj (opposite.op C))
  (g : Y ⟶ Spec.obj (opposite.op C)) : has_pullback f g :=
@@has_pullback_symmetry _ _ _
  (@@has_pullback_of_cover Y.affine_cover g f
    (λ i, @@has_pullback_symmetry _ _ _ $ affine_affine_has_pullback _ _))

instance left_affine_comp_pullback_has_pullback {X Y Z : Scheme}
  (f : X ⟶ Z) (g : Y ⟶ Z) (i : Z.affine_cover.J) :
    has_pullback ((Z.affine_cover.pullback_cover f).map i ≫ f) g :=
begin
  let Xᵢ := pullback f (Z.affine_cover.map i),
  let Yᵢ := pullback g (Z.affine_cover.map i),
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _),
  have := big_square_is_pullback (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _)
    (pullback.snd : Xᵢ ⟶ _) (Z.affine_cover.map i) pullback.snd pullback.snd g
    pullback.condition.symm pullback.condition.symm
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _)
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _),
  have : has_pullback (pullback.snd ≫ Z.affine_cover.map i : Xᵢ ⟶ _) g :=
    ⟨⟨⟨_,this⟩⟩⟩,
  rw ← pullback.condition at this,
  exact this,
end

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) : has_pullback f g :=
has_pullback_of_cover (Z.affine_cover.pullback_cover f) f g

instance : has_pullbacks Scheme := has_pullbacks_of_has_limit_cospan _

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) [is_affine X] [is_affine Y] [is_affine Z] :
  is_affine (pullback f g) :=
is_affine_of_iso (pullback.map f g (Spec.map (Γ.map f.op).op) (Spec.map (Γ.map g.op).op)
  (Γ_Spec.adjunction.unit.app X) (Γ_Spec.adjunction.unit.app Y) (Γ_Spec.adjunction.unit.app Z)
  (Γ_Spec.adjunction.unit.naturality f) (Γ_Spec.adjunction.unit.naturality g) ≫
    (preserves_pullback.iso Spec _ _).inv)

/-- Given an open cover `{ Xᵢ }` of `X`, then `X ×[Z] Y` is covered by `Xᵢ ×[Z] Y`. -/
@[simps J obj map]
def open_cover_of_left (𝒰 : open_cover X) (f : X ⟶ Z) (g : Y ⟶ Z) : open_cover (pullback f g) :=
begin
  fapply ((gluing 𝒰 f g).open_cover.pushforward_iso
    (limit.iso_limit_cone ⟨_, glued_is_limit 𝒰 f g⟩).inv).copy 𝒰.J
    (λ i, pullback (𝒰.map i ≫ f) g)
    (λ i, pullback.map _ _ _ _ (𝒰.map i) (𝟙 _) (𝟙 _) (category.comp_id _) (by simp))
    (equiv.refl 𝒰.J) (λ _, iso.refl _),
  rintro (i : 𝒰.J),
  change pullback.map _ _ _ _ _ _ _ _ _ = 𝟙 _ ≫ (gluing 𝒰 f g).ι i ≫ _,
  refine eq.trans _ (category.id_comp _).symm,
  apply pullback.hom_ext,
  all_goals
  { dsimp,
    simp only [limit.iso_limit_cone_inv_π, pullback_cone.mk_π_app_left, category.comp_id,
      pullback_cone.mk_π_app_right, category.assoc, pullback.lift_fst, pullback.lift_snd],
    symmetry,
    exact multicoequalizer.π_desc _ _ _ _ _ },
end

/-- Given an open cover `{ Yᵢ }` of `Y`, then `X ×[Z] Y` is covered by `X ×[Z] Yᵢ`. -/
@[simps J obj map]
def open_cover_of_right (𝒰 : open_cover Y) (f : X ⟶ Z) (g : Y ⟶ Z) : open_cover (pullback f g) :=
begin
  fapply ((open_cover_of_left 𝒰 g f).pushforward_iso (pullback_symmetry _ _).hom).copy 𝒰.J
    (λ i, pullback f (𝒰.map i ≫ g))
    (λ i, pullback.map _ _ _ _ (𝟙 _) (𝒰.map i) (𝟙 _) (by simp) (category.comp_id _))
    (equiv.refl _) (λ i, pullback_symmetry _ _),
  intro i,
  dsimp [open_cover.bind],
  apply pullback.hom_ext; simp,
end

/-- Given an open cover `{ Xᵢ }` of `X` and an open cover `{ Yⱼ }` of `Y`, then
`X ×[Z] Y` is covered by `Xᵢ ×[Z] Yⱼ`. -/
@[simps J obj map]
def open_cover_of_left_right (𝒰X : X.open_cover) (𝒰Y : Y.open_cover)
  (f : X ⟶ Z) (g : Y ⟶ Z) : (pullback f g).open_cover :=
begin
  fapply ((open_cover_of_left 𝒰X f g).bind (λ x, open_cover_of_right 𝒰Y (𝒰X.map x ≫ f) g)).copy
    (𝒰X.J × 𝒰Y.J)
    (λ ij, pullback (𝒰X.map ij.1 ≫ f) (𝒰Y.map ij.2 ≫ g))
    (λ ij, pullback.map _ _ _ _ (𝒰X.map ij.1) (𝒰Y.map ij.2) (𝟙 _)
      (category.comp_id _) (category.comp_id _))
    (equiv.sigma_equiv_prod _ _).symm
    (λ _, iso.refl _),
  rintro ⟨i, j⟩,
  apply pullback.hom_ext; simpa,
end

/-- (Implementation). Use `open_cover_of_base` instead. -/
def open_cover_of_base' (𝒰 : open_cover Z) (f : X ⟶ Z) (g : Y ⟶ Z) : open_cover (pullback f g) :=
begin
  apply (open_cover_of_left (𝒰.pullback_cover f) f g).bind,
  intro i,
  let Xᵢ := pullback f (𝒰.map i),
  let Yᵢ := pullback g (𝒰.map i),
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _),
  have := big_square_is_pullback (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _)
    (pullback.snd : Xᵢ ⟶ _) (𝒰.map i) pullback.snd pullback.snd g
    pullback.condition.symm pullback.condition.symm
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _)
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _),
  refine open_cover_of_is_iso
    ((pullback_symmetry _ _).hom ≫ (limit.iso_limit_cone ⟨_, this⟩).inv ≫
      pullback.map _ _ _ _ (𝟙 _) (𝟙 _) (𝟙 _) _ _),
  { simpa only [category.comp_id, category.id_comp, ← pullback.condition] },
  { simp only [category.comp_id, category.id_comp] },
  apply_instance
end

/-- Given an open cover `{ Zᵢ }` of `Z`, then `X ×[Z] Y` is covered by `Xᵢ ×[Zᵢ] Yᵢ`, where
  `Xᵢ = X ×[Z] Zᵢ` and `Yᵢ = Y ×[Z] Zᵢ` is the preimage of `Zᵢ` in `X` and `Y`. -/
@[simps J obj map]
def open_cover_of_base (𝒰 : open_cover Z) (f : X ⟶ Z) (g : Y ⟶ Z) : open_cover (pullback f g) :=
begin
  apply (open_cover_of_base' 𝒰 f g).copy
    𝒰.J
    (λ i, pullback (pullback.snd : pullback f (𝒰.map i) ⟶ _)
      (pullback.snd : pullback g (𝒰.map i) ⟶ _))
    (λ i, pullback.map _ _ _ _ pullback.fst pullback.fst (𝒰.map i)
      pullback.condition.symm pullback.condition.symm)
    ((equiv.prod_punit 𝒰.J).symm.trans (equiv.sigma_equiv_prod 𝒰.J punit).symm)
    (λ _, iso.refl _),
  intro i,
  change _ = _ ≫ _ ≫ _,
  refine eq.trans _ (category.id_comp _).symm,
  apply pullback.hom_ext; simp only [category.comp_id, open_cover_of_left_map,
    open_cover.pullback_cover_map, pullback_cone.mk_π_app_left, open_cover_of_is_iso_map,
    limit.iso_limit_cone_inv_π_assoc, category.assoc, pullback.lift_fst_assoc,
    pullback_symmetry_hom_comp_snd_assoc, pullback.lift_fst, limit.iso_limit_cone_inv_π,
    pullback_cone.mk_π_app_right, pullback_symmetry_hom_comp_fst_assoc, pullback.lift_snd],
end

end pullback

end algebraic_geometry.Scheme

namespace algebraic_geometry

instance {X Y S X' Y' S' : Scheme} (f : X ⟶ S) (g : Y ⟶ S) (f' : X' ⟶ S')
  (g' : Y' ⟶ S') (i₁ : X ⟶ X') (i₂ : Y ⟶ Y') (i₃ : S ⟶ S') (e₁ : f ≫ i₃ = i₁ ≫ f')
  (e₂ : g ≫ i₃ = i₂ ≫ g') [is_open_immersion i₁] [is_open_immersion i₂] [mono i₃] :
  is_open_immersion (pullback.map f g f' g' i₁ i₂ i₃ e₁ e₂) :=
begin
  rw pullback_map_eq_pullback_fst_fst_iso_inv,
  apply_instance
end

end algebraic_geometry
