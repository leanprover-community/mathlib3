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

-/
universes v u
noncomputable theory

open category_theory category_theory.limits algebraic_geometry
namespace algebraic_geometry.Scheme

variables {C : Type u} [category.{v} C]

variables {X Y Z : Scheme.{u}} (𝒰 : open_cover.{u} X) (f : X ⟶ Z) (g : Y ⟶ Z)
variables [∀ x, has_pullback (𝒰.map x ≫ f) g]

/-- (Xᵢ ×[Z] Y) ×[X] Xⱼ -/
def V (x y : 𝒰.J) : Scheme :=
pullback ((pullback.fst : pullback ((𝒰.map x) ≫ f) g ⟶ _) ≫ (𝒰.map x)) (𝒰.map y)

def t (x y : 𝒰.J) : V 𝒰 f g x y ⟶ V 𝒰 f g y x :=
begin
  haveI : has_pullback (pullback.snd ≫ 𝒰.map x ≫ f) g :=
    has_pullback_assoc_symm (𝒰.map y) (𝒰.map x) (𝒰.map x ≫ f) g,
  haveI : has_pullback (pullback.snd ≫ 𝒰.map y ≫ f) g :=
    has_pullback_assoc_symm (𝒰.map x) (𝒰.map y) (𝒰.map y ≫ f) g,
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
lemma t_fst_fst (x y : 𝒰.J) : t 𝒰 f g x y ≫ pullback.fst ≫ pullback.fst = pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_fst_snd (x y : 𝒰.J) :
  t 𝒰 f g x y ≫ pullback.fst ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
by { delta t, simp }

@[simp, reassoc]
lemma t_snd (x y : 𝒰.J) :
  t 𝒰 f g x y ≫ pullback.snd = pullback.fst ≫ pullback.fst :=
by { delta t, simp }

lemma t_id (x : 𝒰.J) : t 𝒰 f g x x = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  { rw ← cancel_mono (𝒰.map x),
    simp [pullback.condition] },
  { simp },
  { rw ← cancel_mono (𝒰.map x),
    simp [pullback.condition] }
end

abbreviation fV (x y : 𝒰.J) : V 𝒰 f g x y ⟶ pullback ((𝒰.map x) ≫ f) g := pullback.fst

/-- (Xᵢ ×[Z] Y) ×[X] Xⱼ ×[Xᵢ ×[Z] Y] (Xᵢ ×[Z] Y) ×[X] Xₖ  -/
def t' (x y z : 𝒰.J) :
  pullback (fV 𝒰 f g x y) (fV 𝒰 f g x z) ⟶ pullback (fV 𝒰 f g y z) (fV 𝒰 f g y x) :=
begin
  refine (pullback_right_pullback_fst_iso _ _ _).hom ≫ _,
  refine _ ≫ (pullback_symmetry _ _).hom,
  refine _ ≫ (pullback_right_pullback_fst_iso _ _ _).inv,
  refine pullback.map _ _ _ _ (t 𝒰 f g x y) (𝟙 _) (𝟙 _) _ _,
  { simp [← pullback.condition] },
  { simp }
end

section end

@[simp, reassoc]
lemma t'_fst_fst_fst (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.fst ≫ pullback.snd = pullback.snd ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_fst (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.fst ≫ pullback.fst = pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by { delta t', simp }

@[simp, reassoc]
lemma t'_snd_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ pullback.snd ≫ pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by { delta t', simp, }

lemma cocycle_fst_fst_fst (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.fst ≫
  pullback.fst = pullback.fst ≫ pullback.fst ≫ pullback.fst :=
by simp

lemma cocycle_fst_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.fst ≫
  pullback.snd = pullback.fst ≫ pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.fst ≫ pullback.snd =
    pullback.fst ≫ pullback.snd :=
by simp

lemma cocycle_snd_fst_fst (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.fst ≫
  pullback.fst = pullback.snd ≫ pullback.fst ≫ pullback.fst :=
by { rw ← cancel_mono (𝒰.map x), simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_fst_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.fst ≫
  pullback.snd = pullback.snd ≫ pullback.fst ≫ pullback.snd :=
by { simp [pullback.condition_assoc, pullback.condition] }

lemma cocycle_snd_snd (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y ≫ pullback.snd ≫ pullback.snd =
    pullback.snd ≫ pullback.snd :=
by simp

lemma cocycle (x y z : 𝒰.J) :
  t' 𝒰 f g x y z ≫ t' 𝒰 f g y z x ≫ t' 𝒰 f g z x y = 𝟙 _ :=
begin
  apply pullback.hom_ext; rw category.id_comp,
  apply pullback.hom_ext,
  apply pullback.hom_ext,
  simp_rw category.assoc,
  exact cocycle_fst_fst_fst 𝒰 f g x y z,
  simp_rw category.assoc,
  exact cocycle_fst_fst_snd 𝒰 f g x y z,
  simp_rw category.assoc,
  exact cocycle_fst_snd 𝒰 f g x y z,
  apply pullback.hom_ext,
  apply pullback.hom_ext,
  simp_rw category.assoc,
  exact cocycle_snd_fst_fst 𝒰 f g x y z,
  simp_rw category.assoc,
  exact cocycle_snd_fst_snd 𝒰 f g x y z,
  simp_rw category.assoc,
  exact cocycle_snd_snd 𝒰 f g x y z
end

@[simps]
def gluing : Scheme.glue_data.{u} :=
{ J := 𝒰.J,
  U := λ x, pullback ((𝒰.map x) ≫ f) g,
  V := λ ⟨x, y⟩, V 𝒰 f g x y, -- p⁻¹(Xᵢ ∩ Xⱼ)
  f := λ x y, pullback.fst,
  f_id := λ x, infer_instance,
  f_open := infer_instance,
  t := λ x y, t 𝒰 f g x y,
  t_id := λ x, t_id 𝒰 f g x,
  t' := λ x y z, t' 𝒰 f g x y z,
  t_fac := λ x y z, begin
    apply pullback.hom_ext,
    apply pullback.hom_ext,
    all_goals { simp }
  end,
  cocycle := λ x y z, cocycle 𝒰 f g x y z }

section end

def p1 : (gluing 𝒰 f g).glued ⟶ X :=
begin
  fapply multicoequalizer.desc,
  exact λ x, pullback.fst ≫ 𝒰.map x,
  rintro ⟨x,y⟩,
  change pullback.fst ≫ _ ≫ 𝒰.map x = (_ ≫ _) ≫ _ ≫ 𝒰.map y,
  rw pullback.condition,
  rw ← category.assoc,
  congr' 1,
  rw category.assoc,
  exact (t_fst_fst _ _ _ _ _).symm
end

def p2 : (gluing 𝒰 f g).glued ⟶ Y :=
begin
  fapply multicoequalizer.desc,
  exact λ x, pullback.snd,
  rintro ⟨x,y⟩,
  change pullback.fst ≫ _ = (_ ≫ _) ≫ _,
  rw category.assoc,
  exact (t_fst_snd _ _ _ _ _).symm
end

section end

lemma p_comm : p1 𝒰 f g ≫ f = p2 𝒰 f g ≫ g :=
begin
  apply multicoequalizer.hom_ext,
  intro x,
  erw [multicoequalizer.π_desc_assoc, multicoequalizer.π_desc_assoc],
  rw [category.assoc, pullback.condition]
end

section end

variable (s : pullback_cone f g)

def pullback_map (x y : 𝒰.J) :
  pullback ((𝒰.pullback_cover s.fst).map x) ((𝒰.pullback_cover s.fst).map y) ⟶
    (gluing 𝒰 f g).V ⟨x, y⟩ :=
begin
  change pullback pullback.fst pullback.fst ⟶ pullback _ _,
  refine (pullback_right_pullback_fst_iso _ _ _).hom ≫ _,
  refine pullback.map _ _ _ _ _ (𝟙 _) (𝟙 _) _ _,
  { exact (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition },
  { simpa using pullback.condition },
  { simp }
end

section end

@[reassoc]
lemma pullback_map_fst (x y : 𝒰.J) :
  pullback_map 𝒰 f g s x y ≫ pullback.fst = pullback.fst ≫
    (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition :=
by { delta pullback_map, simp }

@[reassoc]
lemma pullback_map_snd (x y : 𝒰.J) :
  pullback_map 𝒰 f g s x y ≫ pullback.snd = pullback.snd ≫ pullback.snd  :=
by { delta pullback_map, simp }


def glued_lift : s.X ⟶ (gluing 𝒰 f g).glued :=
begin
  fapply (𝒰.pullback_cover s.fst).glue_morphisms,
  { exact λ x, (pullback_symmetry _ _).hom ≫
      pullback.map _ _ _ _ (𝟙 _) s.snd f (category.id_comp _).symm s.condition ≫
      (gluing 𝒰 f g).ι x },
  intros x y,
  rw ← pullback_map_fst_assoc,
  have : _ = pullback.fst ≫ _ :=
    (gluing 𝒰 f g).glue_condition x y,
  rw ← this,
  rw [gluing_to_glue_data_t, gluing_to_glue_data_f],
  simp_rw ← category.assoc,
  congr' 1,
  apply pullback.hom_ext; simp_rw category.assoc,
  { rw t_fst_fst,
    rw pullback_map_snd,
    congr' 1,
    rw [← iso.inv_comp_eq, pullback_symmetry_inv_comp_snd],
    erw pullback.lift_fst,
    rw category.comp_id },
  { rw t_fst_snd,
    rw pullback_map_fst_assoc,
    erw [pullback.lift_snd, pullback.lift_snd],
    rw [pullback_symmetry_hom_comp_snd_assoc, pullback_symmetry_hom_comp_snd_assoc],
    exact pullback.condition_assoc _ }
end

section end

lemma glued_lift_p1 : glued_lift 𝒰 f g s ≫ p1 𝒰 f g = s.fst :=
begin
  rw ← cancel_epi (𝒰.pullback_cover s.fst).from_glued,
  apply multicoequalizer.hom_ext,
  intro b,
  erw multicoequalizer.π_desc_assoc,
  erw multicoequalizer.π_desc_assoc,
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
  erw multicoequalizer.π_desc_assoc,
  erw multicoequalizer.π_desc_assoc,
  delta glued_lift,
  simp_rw ← category.assoc,
  rw (𝒰.pullback_cover s.fst).ι_glue_morphisms,
  simp_rw category.assoc,
  erw [multicoequalizer.π_desc, pullback.lift_snd],
  rw pullback_symmetry_hom_comp_snd_assoc,
  refl
end

section end

namespace open_cover
lemma hom_ext (f₁ f₂ : X ⟶ Y) (h : ∀ x, 𝒰.map x ≫ f₁ = 𝒰.map x ≫ f₂) : f₁ = f₂ :=
begin
  rw ← cancel_epi 𝒰.from_glued,
  apply multicoequalizer.hom_ext,
  intro x,
  erw multicoequalizer.π_desc_assoc,
  erw multicoequalizer.π_desc_assoc,
  exact h x,
end

end open_cover

def pullback_p1_ι_ι (x y : 𝒰.J) :
  pullback (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map x) ⟶ _) ((gluing 𝒰 f g).ι y) ⟶
    V 𝒰 f g y x :=
(pullback_symmetry _ _ ≪≫
  (pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map x) _)).hom ≫
    (pullback.congr_hom (multicoequalizer.π_desc _ _ _ _ _) rfl).hom

@[simp, reassoc] lemma pullback_p1_ι_ι_fst (x y : 𝒰.J) :
  pullback_p1_ι_ι 𝒰 f g x y ≫ pullback.fst = pullback.snd :=
by { delta pullback_p1_ι_ι, simp }

@[simp, reassoc] lemma pullback_p1_ι_ι_snd (x y : 𝒰.J) :
  pullback_p1_ι_ι 𝒰 f g x y ≫ pullback.snd = pullback.fst ≫ pullback.snd :=
by { delta pullback_p1_ι_ι, simp }

lemma lift_p1_ι_ι_eq (x : 𝒰.J) : pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
  (by rw [← pullback.condition_assoc, category.assoc, p_comm]) ≫
  (gluing 𝒰 f g).ι x = (pullback.fst : pullback (p1 𝒰 f g) (𝒰.map x) ⟶ _) :=
begin
  apply ((gluing 𝒰 f g).open_cover.pullback_cover pullback.fst).hom_ext,
  intro y,
  dsimp only [open_cover.pullback_cover],
  transitivity pullback_p1_ι_ι 𝒰 f g x y ≫ fV 𝒰 f g y x ≫ (gluing 𝒰 f g).ι _,
  { rw ← (show _ = fV 𝒰 f g y x ≫ _, from (gluing 𝒰 f g).glue_condition y x),
    simp_rw ← category.assoc,
    congr' 1,
    rw [gluing_to_glue_data_f, gluing_to_glue_data_t],
    apply pullback.hom_ext; simp_rw category.assoc,
    { rw [t_fst_fst, pullback.lift_fst, pullback_p1_ι_ι_snd] },
    { rw [t_fst_snd, pullback.lift_snd, pullback_p1_ι_ι_fst_assoc,
        pullback.condition_assoc], erw multicoequalizer.π_desc } },
  { rw [pullback.condition, ← category.assoc],
    congr' 1,
    apply pullback.hom_ext,
    { simp },
    { simp } }
end

section end

def pullback_p1_iso (x : 𝒰.J) :
  pullback (p1 𝒰 f g) (𝒰.map x) ≅ pullback (𝒰.map x ≫ f) g :=
begin
  fsplit,
  exact pullback.lift pullback.snd (pullback.fst ≫ p2 𝒰 f g)
    (by rw [← pullback.condition_assoc, category.assoc, p_comm]),
  refine pullback.lift ((gluing 𝒰 f g).ι x) pullback.fst
    (by erw multicoequalizer.π_desc),
  { apply pullback.hom_ext,
    { simpa using lift_p1_ι_ι_eq 𝒰 f g x },
    { simp } },
  { apply pullback.hom_ext,
    { simp },
    { simp, erw multicoequalizer.π_desc } },
end

section end

@[simp, reassoc] lemma pullback_p1_iso_hom_fst (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).hom ≫ pullback.fst = pullback.snd :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc] lemma pullback_p1_iso_hom_snd (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).hom ≫ pullback.snd = pullback.fst ≫ p2 𝒰 f g :=
by { delta pullback_p1_iso, simp, }

@[simp, reassoc] lemma pullback_p1_iso_inv_fst (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).inv ≫ pullback.fst = (gluing 𝒰 f g).ι x :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc] lemma pullback_p1_iso_inv_snd (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).inv ≫ pullback.snd = pullback.fst :=
by { delta pullback_p1_iso, simp }

@[simp, reassoc]
lemma pullback_p1_iso_hom_ι (x : 𝒰.J) :
  (pullback_p1_iso 𝒰 f g x).hom ≫ (gluing 𝒰 f g).ι x = pullback.fst :=
by rw [← pullback_p1_iso_inv_fst, iso.hom_inv_id_assoc]

lemma glued_is_limit : is_limit (pullback_cone.mk _ _ (p_comm 𝒰 f g)) :=
begin
  apply pullback_cone.is_limit_aux',
  intro s,
  use glued_lift 𝒰 f g s,
  use glued_lift_p1 𝒰 f g s,
  use glued_lift_p2 𝒰 f g s,
  intros m h₁ h₂,
  change m ≫ p1 𝒰 f g = _ at h₁,
  change m ≫ p2 𝒰 f g = _ at h₂,
  apply (𝒰.pullback_cover s.fst).hom_ext,
  intro x,
  rw open_cover.pullback_cover_map,
  have := pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map x) m
    ≪≫ pullback.congr_hom h₁ rfl,
  erw (𝒰.pullback_cover s.fst).ι_glue_morphisms,
  rw ← cancel_epi (pullback_right_pullback_fst_iso (p1 𝒰 f g) (𝒰.map x) m
    ≪≫ pullback.congr_hom h₁ rfl).hom,
  rw [iso.trans_hom, category.assoc, pullback.congr_hom_hom, pullback.lift_fst_assoc,
    category.comp_id, pullback_right_pullback_fst_iso_hom_fst_assoc, pullback.condition],
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

instance : has_limits CommRingᵒᵖ := has_limits_op_of_has_colimits

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
    (λ x, @@has_pullback_symmetry _ _ _ $ affine_affine_has_pullback _ _))

instance left_affine_comp_pullback_has_pullback {X Y Z : Scheme}
  (f : X ⟶ Z) (g : Y ⟶ Z) (x : Z.affine_cover.J) :
    has_pullback ((Z.affine_cover.pullback_cover f).map x ≫ f) g :=
begin
  let Xᵢ := pullback f (Z.affine_cover.map x),
  let Yᵢ := pullback g (Z.affine_cover.map x),
  let W := pullback (pullback.snd : Yᵢ ⟶ _) (pullback.snd : Xᵢ ⟶ _),
  have := big_square_is_pullback (pullback.fst : W ⟶ _) (pullback.fst : Yᵢ ⟶ _)
    (pullback.snd : Xᵢ ⟶ _) (Z.affine_cover.map x) pullback.snd pullback.snd g
    pullback.condition.symm pullback.condition.symm
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _)
      (pullback_cone.flip_is_limit $ pullback_is_pullback _ _),
  have : has_pullback (pullback.snd ≫ Z.affine_cover.map x : Xᵢ ⟶ _) g :=
    ⟨⟨⟨_,this⟩⟩⟩,
  rw ← pullback.condition at this,
  exact this,
end

instance {X Y Z : Scheme} (f : X ⟶ Z) (g : Y ⟶ Z) : has_pullback f g :=
has_pullback_of_cover (Z.affine_cover.pullback_cover f) f g

end algebraic_geometry.Scheme
