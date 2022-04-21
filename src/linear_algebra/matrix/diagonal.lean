/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.to_lin

/-!
# Diagonal matrices

This file contains some results on the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

## Tags

matrix, diagonal, linear_map
-/

noncomputable theory

open linear_map matrix set submodule
open_locale big_operators
open_locale matrix

universes u v w

namespace matrix

section comm_ring

variables {n : Type*} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]

lemma proj_diagonal (i : n) (w : n → R) :
  (proj i).comp (to_lin' (diagonal w)) = (w i) • proj i :=
by ext j; simp [mul_vec_diagonal]

lemma diagonal_comp_std_basis (w : n → R) (i : n) :
  (diagonal w).to_lin'.comp (linear_map.std_basis R (λ_:n, R) i) =
  (w i) • linear_map.std_basis R (λ_:n, R) i :=
begin
  ext j,
  simp_rw [linear_map.comp_apply, to_lin'_apply, mul_vec_diagonal, linear_map.smul_apply,
           pi.smul_apply, algebra.id.smul_eq_mul],
  by_cases i = j,
  { subst h },
  { rw [std_basis_ne R (λ_:n, R) _ _ (ne.symm h), _root_.mul_zero, _root_.mul_zero] }
end

lemma diagonal_to_lin' (w : n → R) :
  (diagonal w).to_lin' = linear_map.pi (λi, w i • linear_map.proj i) :=
by ext v j; simp [mul_vec_diagonal]

end comm_ring

section field

variables {m n : Type*} [fintype m] [fintype n]
variables {K : Type u} [field K] -- maybe try to relax the universe constraint

lemma ker_diagonal_to_lin' [decidable_eq m] (w : m → K) :
  ker (diagonal w).to_lin' = (⨆i∈{i | w i = 0 }, range (linear_map.std_basis K (λi, K) i)) :=
begin
  rw [← comap_bot, ← infi_ker_proj, comap_infi],
  have := λ i : m, ker_comp (to_lin' (diagonal w)) (proj i),
  simp only [comap_infi, ← this, proj_diagonal, ker_smul'],
  have : univ ⊆ {i : m | w i = 0} ∪ {i : m | w i = 0}ᶜ, { rw set.union_compl_self },
  exact (supr_range_std_basis_eq_infi_ker_proj K (λi:m, K)
    disjoint_compl_right this (finite.of_fintype _)).symm
end

lemma range_diagonal [decidable_eq m] (w : m → K) :
  (diagonal w).to_lin'.range = (⨆ i ∈ {i | w i ≠ 0}, (linear_map.std_basis K (λi, K) i).range) :=
begin
  dsimp only [mem_set_of_eq],
  rw [← map_top, ← supr_range_std_basis, map_supr],
  congr, funext i,
  rw [← linear_map.range_comp, diagonal_comp_std_basis, ← range_smul']
end

lemma rank_diagonal [decidable_eq m] [decidable_eq K] (w : m → K) :
  rank (diagonal w).to_lin' = fintype.card { i // w i ≠ 0 } :=
begin
  have hu : univ ⊆ {i : m | w i = 0}ᶜ ∪ {i : m | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : m | w i ≠ 0} {i : m | w i = 0} := disjoint_compl_left,
  have B₁ := supr_range_std_basis_eq_infi_ker_proj K (λi:m, K) hd hu (finite.of_fintype _),
  have B₂ := @infi_ker_proj_equiv K _ _ (λi:m, K) _ _ _ _ (by simp; apply_instance) hd hu,
  rw [rank, range_diagonal, B₁, ←@dim_fun' K],
  apply linear_equiv.dim_eq,
  apply B₂,
end

end field

end matrix
