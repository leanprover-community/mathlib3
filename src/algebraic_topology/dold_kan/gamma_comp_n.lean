/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.functor_gamma
import algebraic_topology.dold_kan.split_simplicial_object

/-! The counit isomorphism of the Dold-Kan equivlence

The purpose of this file is to construct natural isomorphisms
`N₁Γ₀ : Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ)`
and `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (karoubi (chain_complex C ℕ))` (TODO).

 -/

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.idempotents
  simplex_category opposite simplicial_object
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C] [has_finite_coproducts C]

/-- The isomorphism  `(Γ₀.splitting K).nondeg_complex ≅ K` for all `K : chain_complex C ℕ`. -/
@[simps]
def Γ₀_nondeg_complex_iso (K : chain_complex C ℕ) : (Γ₀.splitting K).nondeg_complex ≅ K :=
homological_complex.hom.iso_of_components (λ n, iso.refl _)
begin
  rintros _ n (rfl : n+1=_),
  dsimp,
  simp only [id_comp, comp_id, alternating_face_map_complex.obj_d_eq,
    preadditive.sum_comp, preadditive.comp_sum],
  rw fintype.sum_eq_single (0 : fin (n+2)),
  { simp only [fin.coe_zero, pow_zero, one_zsmul],
    erw [Γ₀.obj.map_mono_on_summand_id_assoc, Γ₀.obj.termwise.map_mono_δ₀,
      splitting.ι_π_summand_eq_id, comp_id], },
  { intros i hi,
    dsimp,
    simp only [preadditive.zsmul_comp, preadditive.comp_zsmul, assoc],
    erw [Γ₀.obj.map_mono_on_summand_id_assoc, Γ₀.obj.termwise.map_mono_eq_zero,
      zero_comp, zsmul_zero],
    { intro h,
      replace h := congr_arg simplex_category.len h,
      change n+1 = n at h,
      linarith, },
    { simpa only [is_δ₀.iff] using hi, }, },
end

/-- The natural isomorphism `(Γ₀.splitting K).nondeg_complex ≅ K` for `K : chain_complex C ℕ`. -/
def Γ₀'_comp_nondeg_complex_functor : Γ₀' ⋙ split.nondeg_complex_functor ≅ 𝟭 (chain_complex C ℕ) :=
nat_iso.of_components Γ₀_nondeg_complex_iso (λ X Y f, by { ext n, dsimp, simp only [comp_id, id_comp], })

/-- The natural isomorphism `Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ)`. -/
def N₁Γ₀ : Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ) :=
calc Γ₀ ⋙ N₁ ≅ Γ₀' ⋙ split.forget C ⋙ N₁ : functor.associator _ _ _
... ≅ Γ₀' ⋙ split.nondeg_complex_functor ⋙ to_karoubi _ :
  iso_whisker_left Γ₀' split.to_karoubi_nondeg_complex_functor_iso_N₁.symm
... ≅ (Γ₀' ⋙ split.nondeg_complex_functor) ⋙ to_karoubi _ : (functor.associator _ _ _).symm
... ≅ 𝟭 _ ⋙ to_karoubi (chain_complex C ℕ) : iso_whisker_right Γ₀'_comp_nondeg_complex_functor _
... ≅ to_karoubi (chain_complex C ℕ) : functor.left_unitor _

lemma N₁Γ₀_app (K : chain_complex C ℕ) :
  N₁Γ₀.app K = (Γ₀.splitting K).to_karoubi_nondeg_complex_iso_N₁.symm
    ≪≫ (to_karoubi _).map_iso (Γ₀_nondeg_complex_iso K) :=
begin
  ext1,
  dsimp [N₁Γ₀],
  erw [id_comp, comp_id, comp_id],
  refl,
end

lemma N₁Γ₀_hom_app (K : chain_complex C ℕ) :
  N₁Γ₀.hom.app K = (Γ₀.splitting K).to_karoubi_nondeg_complex_iso_N₁.inv
    ≫ (to_karoubi _).map (Γ₀_nondeg_complex_iso K).hom :=
by { change (N₁Γ₀.app K).hom = _, simpa only [N₁Γ₀_app], }

lemma N₁Γ₀_inv_app (K : chain_complex C ℕ) :
  N₁Γ₀.inv.app K = (to_karoubi _).map (Γ₀_nondeg_complex_iso K).inv ≫
   (Γ₀.splitting K).to_karoubi_nondeg_complex_iso_N₁.hom :=
by { change (N₁Γ₀.app K).inv = _, simpa only [N₁Γ₀_app], }

@[simp]
lemma N₁Γ₀_hom_app_f_f (K : chain_complex C ℕ) (n : ℕ) :
  (N₁Γ₀.hom.app K).f.f n = (Γ₀.splitting K).to_karoubi_nondeg_complex_iso_N₁.inv.f.f n :=
by { rw N₁Γ₀_hom_app, apply comp_id, }

@[simp]
lemma N₁Γ₀_inv_app_f_f (K : chain_complex C ℕ) (n : ℕ) :
  (N₁Γ₀.inv.app K).f.f n = (Γ₀.splitting K).to_karoubi_nondeg_complex_iso_N₁.hom.f.f n :=
by { rw N₁Γ₀_inv_app, apply id_comp, }

lemma N₂Γ₂_to_karoubi : to_karoubi (chain_complex C ℕ) ⋙ Γ₂ ⋙ N₂ = Γ₀ ⋙ N₁ :=
begin
  have h := functor.congr_obj (functor_extension₂_comp_whiskering_left_to_karoubi
    (chain_complex C ℕ) (simplicial_object C)) Γ₀,
  have h' := functor.congr_obj (functor_extension₁_comp_whiskering_left_to_karoubi
    (simplicial_object C) (chain_complex C ℕ)) N₁,
  dsimp [N₂, Γ₂, functor_extension₁] at h h' ⊢,
  rw [← functor.assoc, h, functor.assoc, h'],
end

/-- Compatibility isomorphism between `to_karoubi _ ⋙ Γ₂ ⋙ N₂` and `Γ₀ ⋙ N₁` which
are functors `chain_complex C ℕ ⥤ karoubi (chain_complex C ℕ)`. -/
@[simps]
def N₂Γ₂_to_karoubi_iso : to_karoubi (chain_complex C ℕ) ⋙ Γ₂ ⋙ N₂ ≅ Γ₀ ⋙ N₁ :=
eq_to_iso (N₂Γ₂_to_karoubi)

end dold_kan

end algebraic_topology
