/-
Copyleft 2020 Johan Commelin. No rights reserved.
Authors: Johan Commelin
-/

import topology.simplicial.move_this
import algebraic_topology.simplicial_set
import algebra.category.Module.adjunctions
import algebra.homology.homology
import linear_algebra.tensor_product

/-! # The simplicial module associated with a simplicial type -/

noncomputable theory

universe variables u

open category_theory

variables (R : Type u) [comm_ring R]

/-- The category of simplicial modules over a ring. -/
@[derive category]
def simplicial_module := simplicial_object.{u} (Module.{u} R)

namespace sSet

/-- The free simplicial module on a simplicial type. -/
def free_simplicial_module : sSet.{u} ⥤ (simplicial_module R) :=
functor.comp_right (Module.free R)

end sSet

namespace simplicial_module
open simplex_category simplicial_object linear_map opposite finset
open_locale big_operators classical

variables {R} (M : simplicial_module R)

def boundary (n : ℕ) :
  (skeletal.obj M).obj (op (n+1 : ℕ)) ⟶
  (skeletal.obj M).obj (op n) :=
∑ i : fin (n+2), (-1:R)^(i:ℕ) • (M.δ i)

@[reassoc]
lemma boundary_boundary (n : ℕ) : boundary M (n+1) ≫ boundary M n = 0 :=
begin
  let s : finset (fin (n+3) × fin (n+2)) := univ.filter (λ ij, (ij.1:ℕ) ≤ ij.2),
  calc boundary M (n+1) ≫ boundary M n
      = llcomp R _ _ _
          (∑ (i:fin (n+2)), (-1:R)^(i:ℕ) • δ M i) (∑ (i:fin (n+3)), (-1:R)^(i:ℕ) • δ M i) : rfl
  -- ... = ∑ (i : fin (n+3)) (j : fin (n+2)), (-1:R)^(i+j:ℕ) • (llcomp R _ _ _ (δ M j) (δ M i)) :
  ... = ∑ (i : fin (n+3)) (j : fin (n+2)), (-1:R)^(i+j:ℕ) • ((δ M i) ≫ (δ M j)) :
        by simp_rw [map_sum, linear_map.sum_apply, map_smul, smul_apply, smul_smul, ← pow_add]; refl
  ... = ∑ ij : fin (n+3) × fin (n+2), (-1:R)^(ij.1+ij.2:ℕ) • ((δ M ij.1) ≫ (δ M ij.2)) :
        by rw [← univ_product_univ, sum_product]
  ... =   (∑ ij in s,  (-1:R)^(ij.1+ij.2:ℕ) • ((δ M ij.1) ≫ (δ M ij.2)))
        + (∑ ij in sᶜ, (-1:R)^(ij.1+ij.2:ℕ) • ((δ M ij.1) ≫ (δ M ij.2))) : by rw sum_add_sum_compl
  ... = 0 : _,

  erw [← eq_neg_iff_add_eq_zero, ← finset.sum_neg_distrib],
  -- The sums are equal because we can give a bijection
  -- between the indexing sets, such that corresponding terms are equal.
  -- We get 4 goals. All the substance is in the second goal.
  refine (finset.sum_bij (λ (ij : fin (n+3) × fin (n+2)) hij,
    (ij.2.succ, ij.1.cast_lt (lt_of_le_of_lt (mem_filter.mp hij).right ij.2.is_lt)))
    _ _ _ _),
  { -- Show that our function is well-defined
    rintro ⟨i,j⟩ hij, simp only [mem_filter, true_and, mem_compl_iff, mem_univ, not_le],
    unfold_coes, dsimp [s] at hij ⊢, simp only [true_and, mem_filter, mem_univ] at *,
    exact nat.succ_le_succ (by assumption) },
  { -- The core of the proof.
    -- After all, we have to use the simplicial identity somewhere.
    rintros ⟨i,j⟩ hij,
    show (-1:R)^(i+j:ℕ) • δ M i ≫ δ M j =
      -((-1:R)^(j.succ + i.cast_lt _ :ℕ) • δ M j.succ ≫ δ M (i.cast_lt _)),
    rw M.δ_comp_δ (show i.cast_lt _ ≤ j, from (mem_filter.mp hij).2),
    rw [← neg_smul],
    congr' 1,
    unfold_coes,
    simp only [fin.succ_val, nat.succ_eq_add_one, pow_add, mul_comm,
      one_mul, pow_one, mul_neg_eq_neg_mul_symm, fin.cast_lt_val, neg_neg], },
  { -- Show that our function is injective
    rintro ⟨i₁, j₁⟩ ⟨i₂, j₂⟩ hij₁ hij₂ h,
    rw [prod.mk.inj_iff, fin.eq_iff_veq, fin.eq_iff_veq] at h ⊢,
    simp only [fin.cast_lt_val, fin.succ_val] at h,
    rwa [and_comm] at h, },
  { -- Show that our function is surjective
    rintro ⟨i,j⟩ hij,
    refine ⟨⟨j.cast_succ, i.pred _⟩, _, _⟩,
    { intro H,
      rw [H, mem_compl_iff, mem_filter, not_and] at hij,
      exact hij (mem_univ _) (nat.zero_le _) },
    { cases i,
      simp only [true_and, mem_compl_iff, mem_filter, mem_univ, not_le] at hij ⊢,
      exact nat.le_pred_of_lt hij, },
    { ext; simp only [fin.succ_pred, fin.pred_succ, fin.cast_lt_cast_succ], }, },
end


end simplicial_module
