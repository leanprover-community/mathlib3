/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.dold_kan.gamma_comp_n
import algebraic_topology.dold_kan.n_reflects_iso

/-! The unit isomorphism of the Dold-Kan equivalence

In order to construct the unit isomorphism of the Dold-Kan equivalence,
we first construct natural transformations
`Γ₂N₁.nat_trans : N₁ ⋙ Γ₂ ⟶ to_karoubi (simplicial_object C)` and
`Γ₂N₂.nat_trans : N₂ ⋙ Γ₂ ⟶ 𝟭 (simplicial_object C)` (TODO).
It is then shown that `Γ₂N₂.nat_trans` is an isomorphism by using
that it becomes an isomorphism after the application of the functor
`N₂ : karoubi (simplicial_object C) ⥤ karoubi (chain_complex C ℕ)`
which reflects isomorphisms (TODO).

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

end dold_kan

end algebraic_topology
