/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.split_simplicial_object
import category_theory.preadditive.basic
import algebraic_topology.dold_kan.degeneracies

/-!

# Split simplicial objects in preadditive categories

TODO @joelriou: Define a functor `N' : simplicial_object.split C ⥤ chain_complex C ℕ`
when `C` is a preadditive category, and get an isomorphism
`N' ⋙ to_karoubi (chain_complex C ℕ) ≅ forget C ⋙ dold_kan.N₁`

-/

noncomputable theory

open category_theory category_theory.limits category_theory.category
  category_theory.preadditive opposite algebraic_topology.dold_kan

open_locale big_operators simplicial

namespace simplicial_object

namespace splitting

variables {C : Type*} [category C] [has_finite_coproducts C]
  {X : simplicial_object C} (s : splitting X)

/-- The projection on a summand of the coproduct decomposition given
by a splitting of a simplicial object. -/
def π_summand [has_zero_morphisms C] {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  X.obj Δ ⟶ s.N A.1.unop.len :=
begin
  refine (s.iso Δ).inv ≫ sigma.desc (λ B, _),
  by_cases B = A,
  { exact eq_to_hom (by { subst h, refl, }), },
  { exact 0, },
end

@[simp, reassoc]
lemma ι_π_summand_eq_id [has_zero_morphisms C] {Δ : simplex_categoryᵒᵖ} (A : index_set Δ) :
  s.ι_summand A ≫ s.π_summand A = 𝟙 _ :=
begin
  dsimp [ι_summand, π_summand],
  simp only [summand, assoc, is_iso.hom_inv_id_assoc],
  erw [colimit.ι_desc, cofan.mk_ι_app],
  dsimp,
  simp only [eq_self_iff_true, if_true],
end

@[simp, reassoc]
lemma ι_π_summand_eq_zero [has_zero_morphisms C] {Δ : simplex_categoryᵒᵖ} (A B : index_set Δ)
  (h : B ≠ A) : s.ι_summand A ≫ s.π_summand B = 0 :=
begin
  dsimp [ι_summand, π_summand],
  simp only [summand, assoc, is_iso.hom_inv_id_assoc],
  erw [colimit.ι_desc, cofan.mk_ι_app],
  apply dif_neg,
  exact h.symm,
end

variable [preadditive C]

lemma decomposition_id (Δ : simplex_categoryᵒᵖ) :
  𝟙 (X.obj Δ) = ∑ (A : index_set Δ), s.π_summand A ≫ s.ι_summand A :=
begin
  apply s.hom_ext',
  intro A,
  rw [comp_id, comp_sum, finset.sum_eq_single A, ι_π_summand_eq_id_assoc],
  { intros B h₁ h₂,
    rw [s.ι_π_summand_eq_zero_assoc _ _ h₂, zero_comp], },
  { simp only [finset.mem_univ, not_true, is_empty.forall_iff], },
end

@[simp, reassoc]
lemma σ_comp_π_summand_id_eq_zero {n : ℕ} (i : fin (n+1)) :
  X.σ i ≫ s.π_summand (index_set.id (op [n+1])) = 0 :=
begin
  apply s.hom_ext',
  intro A,
  dsimp only [simplicial_object.σ],
  rw [comp_zero, s.ι_summand_epi_naturality_assoc A (simplex_category.σ i).op,
    ι_π_summand_eq_zero],
  symmetry,
  change ¬ (A.epi_comp (simplex_category.σ i).op).eq_id,
  rw index_set.eq_id_iff_len_eq,
  have h := simplex_category.len_le_of_epi (infer_instance : epi A.e),
  dsimp at ⊢ h,
  linarith,
end

/-- If a simplicial object `X` in an additive category is split,
then `P_infty` vanishes on all the summands of `X _[n]` which do
not correspond to the identity of `[n]`. -/
lemma ι_summand_comp_P_infty_eq_zero {X : simplicial_object C}
  (s : simplicial_object.splitting X)
  {n : ℕ} (A : simplicial_object.splitting.index_set (op [n]))
  (hA : ¬ A.eq_id) :
  s.ι_summand A ≫ P_infty.f n = 0 :=
begin
  rw simplicial_object.splitting.index_set.eq_id_iff_mono at hA,
  rw [simplicial_object.splitting.ι_summand_eq, assoc,
    degeneracy_comp_P_infty X n A.e hA, comp_zero],
end

end splitting

end simplicial_object
