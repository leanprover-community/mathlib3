/-
Copyright (c) 2022 Joël Riou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Joël Riou
-/

import algebraic_topology.split_simplicial_object
import algebraic_topology.dold_kan.degeneracies
import algebraic_topology.dold_kan.functor_n

/-!

# Split simplicial objects in preadditive categories

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file we define a functor `nondeg_complex : simplicial_object.split C ⥤ chain_complex C ℕ`
when `C` is a preadditive category with finite coproducts, and get an isomorphism
`to_karoubi_nondeg_complex_iso_N₁ : nondeg_complex ⋙ to_karoubi _ ≅ forget C ⋙ dold_kan.N₁`.
-/

noncomputable theory

open category_theory category_theory.limits category_theory.category
  category_theory.preadditive category_theory.idempotents opposite
  algebraic_topology algebraic_topology.dold_kan

open_locale big_operators simplicial dold_kan

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

lemma comp_P_infty_eq_zero_iff {Z : C} {n : ℕ} (f : Z ⟶ X _[n]) :
  f ≫ P_infty.f n = 0 ↔ f ≫ s.π_summand (index_set.id (op [n])) = 0 :=
begin
  split,
  { intro h,
    cases n,
    { dsimp at h,
      rw [comp_id] at h,
      rw [h, zero_comp], },
    { have h' := f ≫= P_infty_f_add_Q_infty_f (n+1),
      dsimp at h',
      rw [comp_id, comp_add, h, zero_add] at h',
      rw [← h', assoc, Q_infty_f, decomposition_Q, preadditive.sum_comp,
        preadditive.comp_sum, finset.sum_eq_zero],
      intros i hi,
      simp only [assoc, σ_comp_π_summand_id_eq_zero, comp_zero], }, },
  { intro h,
    rw [← comp_id f, assoc, s.decomposition_id, preadditive.sum_comp,
      preadditive.comp_sum, fintype.sum_eq_zero],
    intro A,
    by_cases hA : A.eq_id,
    { dsimp at hA,
      subst hA,
      rw [assoc, reassoc_of h, zero_comp], },
    { simp only [assoc, s.ι_summand_comp_P_infty_eq_zero A hA, comp_zero], }, },
end

@[simp, reassoc]
lemma P_infty_comp_π_summand_id (n : ℕ) :
  P_infty.f n ≫ s.π_summand (index_set.id (op [n])) = s.π_summand (index_set.id (op [n])) :=
begin
  conv_rhs { rw ← id_comp (s.π_summand _), },
  symmetry,
  rw [← sub_eq_zero, ← sub_comp, ← comp_P_infty_eq_zero_iff, sub_comp, id_comp,
    P_infty_f_idem, sub_self],
end

@[simp, reassoc]
lemma π_summand_comp_ι_summand_comp_P_infty_eq_P_infty (n : ℕ) :
  s.π_summand (index_set.id (op [n])) ≫ s.ι_summand (index_set.id (op [n])) ≫ P_infty.f n =
    P_infty.f n :=
begin
  conv_rhs { rw ← id_comp (P_infty.f n), },
  erw [s.decomposition_id, preadditive.sum_comp],
  rw [fintype.sum_eq_single (index_set.id (op [n])), assoc],
  rintros A (hA : ¬A.eq_id),
  rw [assoc, s.ι_summand_comp_P_infty_eq_zero A hA, comp_zero],
end

/-- The differentials `s.d i j : s.N i ⟶ s.N j` on nondegenerate simplices of a split
simplicial object are induced by the differentials on the alternating face map complex. -/
@[simp]
def d (i j : ℕ) : s.N i ⟶ s.N j :=
s.ι_summand (index_set.id (op [i])) ≫ K[X].d i j ≫ s.π_summand (index_set.id (op [j]))

lemma ι_summand_comp_d_comp_π_summand_eq_zero (j k : ℕ) (A : index_set (op [j])) (hA : ¬A.eq_id) :
  s.ι_summand A ≫ K[X].d j k ≫ s.π_summand (index_set.id (op [k])) = 0 :=
begin
  rw A.eq_id_iff_mono at hA,
  rw [← assoc, ← s.comp_P_infty_eq_zero_iff, assoc, ← P_infty.comm j k, s.ι_summand_eq, assoc,
    degeneracy_comp_P_infty_assoc X j A.e hA, zero_comp, comp_zero],
end

/-- If `s` is a splitting of a simplicial object `X` in a preadditive category,
`s.nondeg_complex` is a chain complex which is given in degree `n` by
the nondegenerate `n`-simplices of `X`. -/
@[simps]
def nondeg_complex : chain_complex C ℕ :=
{ X := s.N,
  d := s.d,
  shape' := λ i j hij, by simp only [d, K[X].shape i j hij, zero_comp, comp_zero],
  d_comp_d' := λ i j k hij hjk, begin
    simp only [d, assoc],
    have eq : K[X].d i j ≫ 𝟙 (X.obj (op [j])) ≫ K[X].d j k ≫
      s.π_summand (index_set.id (op [k])) = 0 :=
      by erw [id_comp, homological_complex.d_comp_d_assoc, zero_comp],
    rw s.decomposition_id at eq,
    classical,
    rw [fintype.sum_eq_add_sum_compl (index_set.id (op [j])), add_comp, comp_add, assoc,
      preadditive.sum_comp, preadditive.comp_sum, finset.sum_eq_zero, add_zero] at eq, swap,
    { intros A hA,
      simp only [finset.mem_compl, finset.mem_singleton] at hA,
      simp only [assoc, ι_summand_comp_d_comp_π_summand_eq_zero _ _ _ _ hA, comp_zero], },
    rw [eq, comp_zero],
  end }

/-- The chain complex `s.nondeg_complex` attached to a splitting of a simplicial object `X`
becomes isomorphic to the normalized Moore complex `N₁.obj X` defined as a formal direct
factor in the category `karoubi (chain_complex C ℕ)`. -/
@[simps]
def to_karoubi_nondeg_complex_iso_N₁ : (to_karoubi _).obj s.nondeg_complex ≅ N₁.obj X :=
{ hom :=
  { f :=
    { f := λ n, s.ι_summand (index_set.id (op [n])) ≫ P_infty.f n,
      comm' := λ i j hij, begin
        dsimp,
        rw [assoc, assoc, assoc, π_summand_comp_ι_summand_comp_P_infty_eq_P_infty,
          homological_complex.hom.comm],
      end, },
    comm := by { ext n, dsimp, rw [id_comp, assoc, P_infty_f_idem], }, },
  inv :=
  { f :=
    { f := λ n, s.π_summand (index_set.id (op [n])),
      comm' := λ i j hij, begin
        dsimp,
        slice_rhs 1 1 { rw ← id_comp (K[X].d i j), },
        erw s.decomposition_id,
        rw [sum_comp, sum_comp, finset.sum_eq_single (index_set.id (op [i])), assoc, assoc],
        { intros A h hA,
          simp only [assoc, s.ι_summand_comp_d_comp_π_summand_eq_zero _ _ _ hA, comp_zero], },
        { simp only [finset.mem_univ, not_true, is_empty.forall_iff], },
      end, },
    comm := by { ext n, dsimp, simp only [comp_id, P_infty_comp_π_summand_id], }, },
  hom_inv_id' := begin
    ext n,
    simpa only [assoc, P_infty_comp_π_summand_id, karoubi.comp_f,
      homological_complex.comp_f, ι_π_summand_eq_id],
  end,
  inv_hom_id' := begin
    ext n,
    simp only [π_summand_comp_ι_summand_comp_P_infty_eq_P_infty, karoubi.comp_f,
      homological_complex.comp_f, N₁_obj_p, karoubi.id_eq],
  end, }

end splitting

namespace split

variables {C : Type*} [category C] [preadditive C] [has_finite_coproducts C]

/-- The functor which sends a split simplicial object in a preadditive category to
the chain complex which consists of nondegenerate simplices. -/
@[simps]
def nondeg_complex_functor : split C ⥤ chain_complex C ℕ :=
{ obj := λ S, S.s.nondeg_complex,
  map := λ S₁ S₂ Φ,
  { f := Φ.f,
    comm' := λ i j hij, begin
      dsimp,
      erw [← ι_summand_naturality_symm_assoc Φ (splitting.index_set.id (op [i])),
        ((alternating_face_map_complex C).map Φ.F).comm_assoc i j],
      simp only [assoc],
      congr' 2,
      apply S₁.s.hom_ext',
      intro A,
      dsimp [alternating_face_map_complex],
      erw ι_summand_naturality_symm_assoc Φ A,
      by_cases A.eq_id,
      { dsimp at h,
        subst h,
        simpa only [splitting.ι_π_summand_eq_id, comp_id, splitting.ι_π_summand_eq_id_assoc], },
      { have h' : splitting.index_set.id (op [j]) ≠ A := by { symmetry, exact h, },
        rw [S₁.s.ι_π_summand_eq_zero_assoc _ _ h', S₂.s.ι_π_summand_eq_zero _ _ h',
          zero_comp, comp_zero], },
    end }, }

/-- The natural isomorphism (in `karoubi (chain_complex C ℕ)`) between the chain complex
of nondegenerate simplices of a split simplicial object and the normalized Moore complex
defined as a formal direct factor of the alternating face map complex. -/
@[simps]
def to_karoubi_nondeg_complex_functor_iso_N₁ :
  nondeg_complex_functor ⋙ to_karoubi (chain_complex C ℕ) ≅ forget C ⋙ dold_kan.N₁ :=
nat_iso.of_components (λ S, S.s.to_karoubi_nondeg_complex_iso_N₁)
  (λ S₁ S₂ Φ, begin
    ext n,
    dsimp,
    simp only [karoubi.comp_f, to_karoubi_map_f, homological_complex.comp_f,
      nondeg_complex_functor_map_f, splitting.to_karoubi_nondeg_complex_iso_N₁_hom_f_f,
      N₁_map_f, alternating_face_map_complex.map_f, assoc, P_infty_f_idem_assoc],
    erw ← split.ι_summand_naturality_symm_assoc Φ (splitting.index_set.id (op [n])),
    rw P_infty_f_naturality,
  end)

end split

end simplicial_object
