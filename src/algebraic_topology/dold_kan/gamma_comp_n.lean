/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.functor_gamma
import category_theory.idempotents.homological_complex

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
 The counit isomorphism of the Dold-Kan equivalence

The purpose of this file is to construct natural isomorphisms
`N₁Γ₀ : Γ₀ ⋙ N₁ ≅ to_karoubi (chain_complex C ℕ)`
and `N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (karoubi (chain_complex C ℕ))`.

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits category_theory.idempotents
  opposite simplicial_object
open_locale simplicial

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
def Γ₀'_comp_nondeg_complex_functor :
  Γ₀' ⋙ split.nondeg_complex_functor ≅ 𝟭 (chain_complex C ℕ) :=
nat_iso.of_components Γ₀_nondeg_complex_iso
  (λ X Y f, by { ext n, dsimp, simp only [comp_id, id_comp], })

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

/-- The counit isomorphism of the Dold-Kan equivalence for additive categories. -/
def N₂Γ₂ : Γ₂ ⋙ N₂ ≅ 𝟭 (karoubi (chain_complex C ℕ)) :=
((whiskering_left _ _ _).obj (to_karoubi (chain_complex C ℕ))).preimage_iso
  (N₂Γ₂_to_karoubi_iso ≪≫ N₁Γ₀)

lemma N₂Γ₂_compatible_with_N₁Γ₀ (K : chain_complex C ℕ) :
  N₂Γ₂.hom.app ((to_karoubi _).obj K) = N₂Γ₂_to_karoubi_iso.hom.app K ≫ N₁Γ₀.hom.app K :=
congr_app (((whiskering_left _ _ (karoubi (chain_complex C ℕ ))).obj
  (to_karoubi (chain_complex C ℕ))).image_preimage
  (N₂Γ₂_to_karoubi_iso.hom ≫ N₁Γ₀.hom : _ ⟶ to_karoubi _ ⋙ 𝟭 _)) K

@[simp]
lemma N₂Γ₂_inv_app_f_f (X : karoubi (chain_complex C ℕ)) (n : ℕ) :
  (N₂Γ₂.inv.app X).f.f n =
    X.p.f n ≫ (Γ₀.splitting X.X).ι_summand (splitting.index_set.id (op [n])) :=
begin
  dsimp only [N₂Γ₂, functor.preimage_iso, iso.trans],
  simp only [whiskering_left_obj_preimage_app, N₂Γ₂_to_karoubi_iso_inv, functor.id_map,
    nat_trans.comp_app, eq_to_hom_app, functor.comp_map, assoc, karoubi.comp_f,
    karoubi.eq_to_hom_f, eq_to_hom_refl, comp_id, karoubi.comp_p_assoc, N₂_map_f_f,
    homological_complex.comp_f, N₁Γ₀_inv_app_f_f, P_infty_on_Γ₀_splitting_summand_eq_self_assoc,
    splitting.to_karoubi_nondeg_complex_iso_N₁_hom_f_f, Γ₂_map_f_app, karoubi.decomp_id_p_f],
  dsimp [to_karoubi],
  rw [splitting.ι_desc],
  dsimp [splitting.index_set.id],
  rw karoubi.homological_complex.p_idem_assoc,
end

end dold_kan

end algebraic_topology
