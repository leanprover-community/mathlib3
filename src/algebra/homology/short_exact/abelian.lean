/-
Copyright (c) 2021 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Andrew Yang, Pierre-Alexandre Bazin
-/
import algebra.homology.short_exact.preadditive
import category_theory.abelian.diagram_lemmas.four

/-!
# Short exact sequences in abelian categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In an abelian category, a left-split or right-split short exact sequence admits a splitting.
-/

noncomputable theory

open category_theory category_theory.limits category_theory.preadditive

variables {𝒜 : Type*} [category 𝒜]

namespace category_theory

variables {A B C A' B' C' : 𝒜} {f : A ⟶ B} {g : B ⟶ C} {f' : A' ⟶ B'} {g' : B' ⟶ C'}
variables [abelian 𝒜]
open_locale zero_object

lemma is_iso_of_short_exact_of_is_iso_of_is_iso (h : short_exact f g) (h' : short_exact f' g')
  (i₁ : A ⟶ A') (i₂ : B ⟶ B') (i₃ : C ⟶ C')
  (comm₁ : i₁ ≫ f' = f ≫ i₂) (comm₂ : i₂ ≫ g' = g ≫ i₃) [is_iso i₁] [is_iso i₃] :
  is_iso i₂ :=
begin
  obtain ⟨_⟩ := h,
  obtain ⟨_⟩ := h',
  resetI,
  refine @abelian.is_iso_of_is_iso_of_is_iso_of_is_iso_of_is_iso 𝒜 _ _ 0 _ _ _ 0 _ _ _
    0 f g 0 f' g' 0 i₁ i₂ i₃ _ comm₁ comm₂ 0 0 0 0 0 _ _ _ _ _ _ _ _ _ _ _;
  try { simp };
  try { apply exact_zero_left_of_mono };
  try { assumption };
  rwa ← epi_iff_exact_zero_right,
end

/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : B ⟶ A ⊞ C` such that `f ≫ i` is the canonical map `biprod.inl : A ⟶ A ⊞ C` and
`i ≫ q = g`, where `q` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is then automatically an isomorphism. -/
def splitting.mk' (h : short_exact f g) (i : B ⟶ A ⊞ C)
  (h1 : f ≫ i = biprod.inl) (h2 : i ≫ biprod.snd = g) : splitting f g :=
{ iso :=
  begin
    refine @as_iso _ _ _ _ i (id _),
    refine is_iso_of_short_exact_of_is_iso_of_is_iso h _ _ _ _
      (h1.trans (category.id_comp _).symm).symm (h2.trans (category.comp_id _).symm),
    split,
    apply exact_inl_snd
  end,
  comp_iso_eq_inl := by { rwa as_iso_hom, },
  iso_comp_snd_eq := h2 }

/-- To construct a splitting of `A -f⟶ B -g⟶ C` it suffices to supply
a *morphism* `i : A ⊞ C ⟶ B` such that `p ≫ i = f` where `p` is the canonical map
`biprod.inl : A ⟶ A ⊞ C`, and `i ≫ g` is the canonical map `biprod.snd : A ⊞ C ⟶ C`,
together with proofs that `f` is mono and `g` is epi.

The morphism `i` is then automatically an isomorphism. -/
def splitting.mk'' (h : short_exact f g) (i : A ⊞ C ⟶ B)
  (h1 : biprod.inl ≫ i = f) (h2 : i ≫ g = biprod.snd) : splitting f g :=
{ iso :=
  begin
    refine (@as_iso _ _ _ _ i (id _)).symm,
    refine is_iso_of_short_exact_of_is_iso_of_is_iso _ h _ _ _
      (h1.trans (category.id_comp _).symm).symm (h2.trans (category.comp_id _).symm),
    split,
    apply exact_inl_snd
  end,
  comp_iso_eq_inl := by rw [iso.symm_hom, as_iso_inv, is_iso.comp_inv_eq, h1],
  iso_comp_snd_eq := by rw [iso.symm_hom, as_iso_inv, is_iso.inv_comp_eq, h2] }

/-- A short exact sequence that is left split admits a splitting. -/
def left_split.splitting {f : A ⟶ B} {g : B ⟶ C} (h : left_split f g) : splitting f g :=
splitting.mk' h.short_exact (biprod.lift h.left_split.some g)
(by { ext,
  { simpa only [biprod.inl_fst, biprod.lift_fst, category.assoc] using h.left_split.some_spec },
  { simp only [biprod.inl_snd, biprod.lift_snd, category.assoc, h.exact.w], } })
(by { simp only [biprod.lift_snd], })

/-- A short exact sequence that is right split admits a splitting. -/
def right_split.splitting {f : A ⟶ B} {g : B ⟶ C} (h : right_split f g) : splitting f g :=
splitting.mk'' h.short_exact (biprod.desc f h.right_split.some)
(biprod.inl_desc _ _)
(by { ext,
  { rw [biprod.inl_snd, ← category.assoc, biprod.inl_desc, h.exact.w] },
  { rw [biprod.inr_snd, ← category.assoc, biprod.inr_desc, h.right_split.some_spec] } })

end category_theory
