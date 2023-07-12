/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.gamma_comp_n
import algebraic_topology.dold_kan.n_reflects_iso

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
 The unit isomorphism of the Dold-Kan equivalence

In order to construct the unit isomorphism of the Dold-Kan equivalence,
we first construct natural transformations
`Γ₂N₁.nat_trans : N₁ ⋙ Γ₂ ⟶ to_karoubi (simplicial_object C)` and
`Γ₂N₂.nat_trans : N₂ ⋙ Γ₂ ⟶ 𝟭 (simplicial_object C)`.
It is then shown that `Γ₂N₂.nat_trans` is an isomorphism by using
that it becomes an isomorphism after the application of the functor
`N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
which reflects isomorphisms.

-/

noncomputable theory

open category_theory category_theory.category category_theory.limits
  category_theory.idempotents simplex_category opposite simplicial_object
open_locale simplicial dold_kan

namespace algebraic_topology

namespace dold_kan

variables {C : Type*} [category C] [preadditive C]

lemma P_infty_comp_map_mono_eq_zero (X : simplicial_object C) {n : ℕ}
  {Δ' : simplex_category} (i : Δ' ⟶ [n]) [hi : mono i] (h₁ : Δ'.len ≠ n) (h₂ : ¬is_δ₀ i) :
  P_infty.f n ≫ X.map i.op = 0 :=
begin
  unfreezingI { induction Δ' using simplex_category.rec with m, },
  obtain ⟨k, hk⟩ := nat.exists_eq_add_of_lt (len_lt_of_mono i
    (λ h, by { rw ← h at h₁,  exact h₁ rfl, })),
  simp only [len_mk] at hk,
  cases k,
  { change n = m + 1 at hk,
    unfreezingI { subst hk, obtain ⟨j, rfl⟩ := eq_δ_of_mono i, },
    rw is_δ₀.iff at h₂,
    have h₃ : 1 ≤ (j : ℕ),
    { by_contra,
      exact h₂ (by simpa only [fin.ext_iff, not_le, nat.lt_one_iff] using h), },
    exact (higher_faces_vanish.of_P (m+1) m).comp_δ_eq_zero j h₂ (by linarith), },
  { simp only [nat.succ_eq_add_one, ← add_assoc] at hk,
    clear h₂ hi,
    subst hk,
    obtain ⟨j₁, i, rfl⟩ := eq_comp_δ_of_not_surjective i (λ h, begin
      have h' := len_le_of_epi (simplex_category.epi_iff_surjective.2 h),
      dsimp at h',
      linarith,
    end),
    obtain ⟨j₂, i, rfl⟩ := eq_comp_δ_of_not_surjective i (λ h, begin
      have h' := len_le_of_epi (simplex_category.epi_iff_surjective.2 h),
      dsimp at h',
      linarith,
    end),
    by_cases hj₁ : j₁ = 0,
    { unfreezingI { subst hj₁, },
      rw [assoc, ← simplex_category.δ_comp_δ'' (fin.zero_le _)],
      simp only [op_comp, X.map_comp, assoc, P_infty_f],
      erw [(higher_faces_vanish.of_P _ _).comp_δ_eq_zero_assoc _ j₂.succ_ne_zero, zero_comp],
      rw fin.coe_succ,
      linarith, },
    { simp only [op_comp, X.map_comp, assoc, P_infty_f],
      erw [(higher_faces_vanish.of_P _ _).comp_δ_eq_zero_assoc _ hj₁, zero_comp],
      by_contra,
      exact hj₁ (by { simp only [fin.ext_iff, fin.coe_zero], linarith, }), }, },
end

@[reassoc]
lemma Γ₀_obj_termwise_map_mono_comp_P_infty (X : simplicial_object C) {Δ Δ' : simplex_category}
  (i : Δ ⟶ Δ') [mono i] :
  Γ₀.obj.termwise.map_mono (alternating_face_map_complex.obj X) i ≫ P_infty.f (Δ.len) =
    P_infty.f (Δ'.len) ≫ X.map i.op :=
begin
  unfreezingI
  { induction Δ using simplex_category.rec with n,
    induction Δ' using simplex_category.rec with n', },
  dsimp,
  /- We start with the case `i` is an identity -/
  by_cases n = n',
  { unfreezingI { subst h, },
    simp only [simplex_category.eq_id_of_mono i, Γ₀.obj.termwise.map_mono_id, op_id, X.map_id],
    dsimp,
    simp only [id_comp, comp_id], },
  by_cases hi : is_δ₀ i,
  /- The case `i = δ 0` -/
  { have h' : n' = n + 1 := hi.left,
    unfreezingI { subst h', },
    simp only [Γ₀.obj.termwise.map_mono_δ₀' _ i hi],
    dsimp,
    rw [← P_infty.comm' _ n rfl, alternating_face_map_complex.obj_d_eq],
    simp only [eq_self_iff_true, id_comp, if_true, preadditive.comp_sum],
    rw finset.sum_eq_single (0 : fin (n+2)), rotate,
    { intros b hb hb',
      rw preadditive.comp_zsmul,
      erw [P_infty_comp_map_mono_eq_zero X (simplex_category.δ b) h
        (by { rw is_δ₀.iff, exact hb', }), zsmul_zero], },
    { simp only [finset.mem_univ, not_true, is_empty.forall_iff], },
    { simpa only [hi.eq_δ₀, fin.coe_zero, pow_zero, one_zsmul], }, },
  /- The case `i ≠ δ 0` -/
  { rw [Γ₀.obj.termwise.map_mono_eq_zero _ i _ hi, zero_comp], swap,
    { by_contradiction h',
      exact h (congr_arg simplex_category.len h'.symm), },
    rw P_infty_comp_map_mono_eq_zero,
    { exact h, },
    { by_contradiction h',
      exact hi h', }, },
end

variable [has_finite_coproducts C]

namespace Γ₂N₁

/-- The natural transformation `N₁ ⋙ Γ₂ ⟶ to_karoubi (simplicial_object C)`. -/
@[simps]
def nat_trans : (N₁ : simplicial_object C ⥤ _) ⋙ Γ₂ ⟶ to_karoubi _ :=
{ app := λ X,
  { f :=
    { app := λ Δ, (Γ₀.splitting K[X]).desc Δ (λ A, P_infty.f A.1.unop.len ≫ X.map (A.e.op)),
      naturality' := λ Δ Δ' θ, begin
        apply (Γ₀.splitting K[X]).hom_ext',
        intro A,
        change _ ≫ (Γ₀.obj K[X]).map θ  ≫ _ = _,
        simp only [splitting.ι_desc_assoc, assoc,
          Γ₀.obj.map_on_summand'_assoc, splitting.ι_desc],
        erw Γ₀_obj_termwise_map_mono_comp_P_infty_assoc X (image.ι (θ.unop ≫ A.e)),
        dsimp only [to_karoubi],
        simp only [← X.map_comp],
        congr' 2,
        simp only [eq_to_hom_refl, id_comp, comp_id, ← op_comp],
        exact quiver.hom.unop_inj (A.fac_pull θ),
      end, },
    comm := begin
      apply (Γ₀.splitting K[X]).hom_ext,
      intro n,
      dsimp [N₁],
      simp only [← splitting.ι_summand_id, splitting.ι_desc,
        comp_id, splitting.ι_desc_assoc, assoc, P_infty_f_idem_assoc],
    end, },
  naturality' := λ X Y f, begin
    ext1,
    apply (Γ₀.splitting K[X]).hom_ext,
    intro n,
    dsimp [N₁, to_karoubi],
    simpa only [←splitting.ι_summand_id, splitting.ι_desc, splitting.ι_desc_assoc,
      assoc, P_infty_f_idem_assoc, karoubi.comp_f, nat_trans.comp_app, Γ₂_map_f_app,
      homological_complex.comp_f, alternating_face_map_complex.map_f,
      P_infty_f_naturality_assoc, nat_trans.naturality],
  end, }

end Γ₂N₁

/-- The compatibility isomorphism relating `N₂ ⋙ Γ₂` and `N₁ ⋙ Γ₂`. -/
@[simps]
def compatibility_Γ₂N₁_Γ₂N₂ : to_karoubi (simplicial_object C) ⋙ N₂ ⋙ Γ₂ ≅ N₁ ⋙ Γ₂ :=
eq_to_iso (functor.congr_obj (functor_extension₁_comp_whiskering_left_to_karoubi _ _) (N₁ ⋙ Γ₂))

namespace Γ₂N₂

/-- The natural transformation `N₂ ⋙ Γ₂ ⟶ 𝟭 (simplicial_object C)`. -/
def nat_trans : (N₂ : karoubi (simplicial_object C) ⥤ _) ⋙ Γ₂ ⟶ 𝟭 _ :=
((whiskering_left _ _ _).obj _).preimage (compatibility_Γ₂N₁_Γ₂N₂.hom ≫ Γ₂N₁.nat_trans)

lemma nat_trans_app_f_app (P : karoubi (simplicial_object C)) :
  Γ₂N₂.nat_trans.app P = (N₂ ⋙ Γ₂).map P.decomp_id_i ≫
    (compatibility_Γ₂N₁_Γ₂N₂.hom ≫ Γ₂N₁.nat_trans).app P.X ≫ P.decomp_id_p :=
whiskering_left_obj_preimage_app ((compatibility_Γ₂N₁_Γ₂N₂.hom ≫ Γ₂N₁.nat_trans)) P

end Γ₂N₂

lemma compatibility_Γ₂N₁_Γ₂N₂_nat_trans (X : simplicial_object C) :
  Γ₂N₁.nat_trans.app X = (compatibility_Γ₂N₁_Γ₂N₂.app X).inv ≫
    Γ₂N₂.nat_trans.app ((to_karoubi _).obj X) :=
begin
  rw [← cancel_epi (compatibility_Γ₂N₁_Γ₂N₂.app X).hom, iso.hom_inv_id_assoc],
  exact congr_app (((whiskering_left _ _ _).obj _).image_preimage
    (compatibility_Γ₂N₁_Γ₂N₂.hom ≫ Γ₂N₁.nat_trans : _ ⟶ to_karoubi _ ⋙ 𝟭 _ )).symm X,
end

lemma identity_N₂_objectwise (P : karoubi (simplicial_object C)) :
  N₂Γ₂.inv.app (N₂.obj P) ≫ N₂.map (Γ₂N₂.nat_trans.app P) = 𝟙 (N₂.obj P) :=
begin
  ext n,
  have eq₁ : (N₂Γ₂.inv.app (N₂.obj P)).f.f n = P_infty.f n ≫ P.p.app (op [n]) ≫
    (Γ₀.splitting (N₂.obj P).X).ι_summand (splitting.index_set.id (op [n])),
  { simp only [N₂Γ₂_inv_app_f_f, N₂_obj_p_f, assoc], },
  have eq₂ : (Γ₀.splitting (N₂.obj P).X).ι_summand (splitting.index_set.id (op [n])) ≫
    (N₂.map (Γ₂N₂.nat_trans.app P)).f.f n = P_infty.f n ≫ P.p.app (op [n]),
  { dsimp [N₂],
    simp only [Γ₂N₂.nat_trans_app_f_app, P_infty_on_Γ₀_splitting_summand_eq_self_assoc,
      functor.comp_map, compatibility_Γ₂N₁_Γ₂N₂_hom, nat_trans.comp_app,
      eq_to_hom_app, assoc, karoubi.comp_f, karoubi.eq_to_hom_f, eq_to_hom_refl, comp_id,
      karoubi.decomp_id_p_f, karoubi.comp_p_assoc, Γ₂_map_f_app,
      N₂_map_f_f, karoubi.decomp_id_i_f, Γ₂N₁.nat_trans_app_f_app],
    erw [splitting.ι_desc_assoc, assoc, assoc, splitting.ι_desc_assoc],
    dsimp [splitting.index_set.id, splitting.index_set.e],
    simp only [assoc, nat_trans.naturality, P_infty_f_naturality_assoc,
      app_idem_assoc, P_infty_f_idem_assoc],
    erw [P.X.map_id, comp_id], },
  simp only [karoubi.comp_f, homological_complex.comp_f, karoubi.id_eq, N₂_obj_p_f, assoc,
    eq₁, eq₂, P_infty_f_naturality_assoc, app_idem, P_infty_f_idem_assoc],
end

lemma identity_N₂ :
  ((𝟙 (N₂ : karoubi (simplicial_object C) ⥤ _ ) ◫ N₂Γ₂.inv) ≫
    (Γ₂N₂.nat_trans ◫ 𝟙 N₂) : N₂ ⟶ N₂) = 𝟙 N₂ :=
by { ext P : 2, dsimp, rw [Γ₂.map_id, N₂.map_id, comp_id, id_comp, identity_N₂_objectwise P], }

instance : is_iso (Γ₂N₂.nat_trans : (N₂ : karoubi (simplicial_object C) ⥤ _ ) ⋙ _ ⟶ _) :=
begin
  haveI : ∀ (P : karoubi (simplicial_object C)), is_iso (Γ₂N₂.nat_trans.app P),
  { intro P,
    haveI : is_iso (N₂.map (Γ₂N₂.nat_trans.app P)),
    { have h := identity_N₂_objectwise P,
      erw hom_comp_eq_id at h,
      rw h,
      apply_instance, },
    exact is_iso_of_reflects_iso _ N₂, },
  apply nat_iso.is_iso_of_is_iso_app,
end

instance : is_iso (Γ₂N₁.nat_trans : (N₁ : simplicial_object C ⥤ _ ) ⋙ _ ⟶ _) :=
begin
  haveI : ∀ (X : simplicial_object C), is_iso (Γ₂N₁.nat_trans.app X),
  { intro X,
    rw compatibility_Γ₂N₁_Γ₂N₂_nat_trans,
    apply_instance, },
  apply nat_iso.is_iso_of_is_iso_app,
end

/-- The unit isomorphism of the Dold-Kan equivalence. -/
@[simp]
def Γ₂N₂ : 𝟭 _ ≅ (N₂ : karoubi (simplicial_object C) ⥤ _) ⋙ Γ₂ :=
(as_iso Γ₂N₂.nat_trans).symm

/-- The natural isomorphism `to_karoubi (simplicial_object C) ≅ N₁ ⋙ Γ₂`. -/
@[simps]
def Γ₂N₁ : to_karoubi _  ≅ (N₁ : simplicial_object C ⥤ _) ⋙ Γ₂ :=
(as_iso Γ₂N₁.nat_trans).symm

end dold_kan

end algebraic_topology
