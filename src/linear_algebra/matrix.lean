/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl

Linear structures on function with finit support `α →₀ β` and multivariate polynomials.
-/
import data.matrix
import linear_algebra.dimension linear_algebra.tensor_product
noncomputable theory

open lattice set linear_map submodule

namespace matrix
universes u v
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]

instance [decidable_eq m] [decidable_eq n] (α) [fintype α] : fintype (matrix m n α) :=
by unfold matrix; apply_instance

section ring
variables {α : Type v} [comm_ring α]

def eval : (matrix m n α) →ₗ[α] ((n → α) →ₗ[α] (m → α)) :=
begin
  refine linear_map.mk₂ α mul_vec _ _ _ _,
  { assume M N v, funext x,
    change finset.univ.sum (λy:n, (M x y + N x y) * v y) = _,
    simp only [_root_.add_mul, finset.sum_add_distrib],
    refl },
  { assume c M v, funext x,
    change finset.univ.sum (λy:n, (c * M x y) * v y) = _,
    simp only [_root_.mul_assoc, finset.mul_sum.symm],
    refl },
  { assume M v w, funext x,
    change finset.univ.sum (λy:n, M x y * (v y + w y)) = _,
    simp [_root_.mul_add, finset.sum_add_distrib],
    refl },
  { assume c M v, funext x,
    change finset.univ.sum (λy:n, M x y * (c * v y)) = _,
    rw [show (λy:n, M x y * (c * v y)) = (λy:n, c * (M x y * v y)), { funext n, ac_refl },
      ← finset.mul_sum],
    refl }
end

def to_lin : matrix m n α → (n → α) →ₗ[α] (m → α) := eval.to_fun

lemma to_lin_add (M N : matrix m n α) : (M + N).to_lin = M.to_lin + N.to_lin :=
matrix.eval.map_add M N

@[simp] lemma to_lin_zero : (0 : matrix m n α).to_lin = 0 :=
matrix.eval.map_zero

instance to_lin.is_linear_map :
  @is_linear_map α (matrix m n α) ((n → α) →ₗ[α] (m → α)) _ _ _ _ _ to_lin :=
matrix.eval.is_linear

instance to_lin.is_add_monoid_hom :
  @is_add_monoid_hom (matrix m n α) ((n → α) →ₗ[α] (m → α)) _ _ to_lin :=
{ map_zero := to_lin_zero, map_add := to_lin_add }

@[simp] lemma to_lin_apply (M : matrix m n α) (v : n → α) :
  (M.to_lin : (n → α) → (m → α)) v = mul_vec M v := rfl

lemma mul_to_lin [decidable_eq l] (M : matrix m n α) (N : matrix n l α) :
  (M.mul N).to_lin = M.to_lin.comp N.to_lin :=
begin
  ext v x,
  simp [to_lin_apply, mul_vec, matrix.mul, finset.sum_mul, finset.mul_sum],
  rw [finset.sum_comm],
  congr, funext x, congr, funext y,
  rw [mul_assoc]
end

def to_matrixₗ [decidable_eq n] : ((n → α) →ₗ[α] (m → α)) →ₗ[α] matrix m n α :=
begin
  refine linear_map.mk (λ f i j, f (λ n, ite (j = n) 1 0) i) _ _,
  { assume f g, simp only [add_apply], refl },
  { assume f g, simp only [smul_apply], refl }
end

def to_matrix [decidable_eq n]: ((n → α) →ₗ[α] (m → α)) → matrix m n α := to_matrixₗ.to_fun

variables (f : (n → α) →ₗ[α] (m → α)) [decidable_eq n] (y : n → α)

variables {R : Type*} [comm_ring R]
variables {M : Type*} {N : Type*} {P : Type*} {Q : Type*}
variables [add_comm_group M] [add_comm_group N] [add_comm_group P] [add_comm_group Q]
variables [module R M] [module R N] [module R P] [module R Q]
include R
@[simp] theorem mk₂_apply2
  (f : M → N → P) {H1 H2 H3 H4} (m : M) (n : N) :
  ((mk₂ R f H1 H2 H3 H4 : M →ₗ[R] N →ₗ P).to_fun m).to_fun n = f m n := rfl

lemma to_matrix_to_lin [decidable_eq n] {f : (n → α) →ₗ[α] (m → α)} : to_lin (to_matrix f) = f :=
begin
unfold to_lin,
unfold eval,
ext y : 1,
change ((mk₂ α mul_vec _ _ _ _).to_fun (to_matrix f)).to_fun y = f.to_fun y,
rw [mk₂_apply2],
{ unfold to_matrix,
  unfold to_matrixₗ,
  simp,
  sorry
 },
 repeat {sorry}
end

lemma to_lin_to_matrix [decidable_eq n] (M : matrix m n α) : to_matrix (to_lin M) = M := sorry

section
open linear_map

lemma proj_diagonal [decidable_eq m] (i : m) (w : m → α) :
  (proj i).comp (to_lin (diagonal w)) = (w i) • proj i :=
by ext j; simp [mul_vec_diagonal]

lemma diagonal_comp_std_basis [decidable_eq n] (w : n → α) (i : n) :
  (diagonal w).to_lin.comp (std_basis α (λ_:n, α) i) = (w i) • std_basis α (λ_:n, α) i :=
begin
  ext a j,
  simp only [linear_map.comp_apply, smul_apply, to_lin_apply, mul_vec_diagonal, smul_apply,
    pi.smul_apply, smul_eq_mul],
  by_cases i = j,
  { subst h },
  { rw [std_basis_ne α (λ_:n, α) _ _ (ne.symm h), _root_.mul_zero, _root_.mul_zero] }
end
end

end ring

section vector_space
variables {α : Type u} [discrete_field α] -- maybe try to relax the universe constraint

open linear_map

lemma rank_vec_mul_vec [decidable_eq n] (w : m → α) (v : n → α) :
  rank (vec_mul_vec w v).to_lin ≤ 1 :=
begin
  rw [vec_mul_vec_eq, mul_to_lin],
  refine le_trans (rank_comp_le1 _ _) _,
  refine le_trans (rank_le_domain _) _,
  rw [dim_fun', ← cardinal.fintype_card],
  exact le_refl _
end

set_option class.instance_max_depth 100

lemma diagonal_to_lin [decidable_eq m] (w : m → α) :
  (diagonal w).to_lin = linear_map.pi (λi, w i • linear_map.proj i) :=
by ext v j; simp [mul_vec_diagonal]

lemma ker_diagonal_to_lin [decidable_eq m] (w : m → α) :
  ker (diagonal w).to_lin = (⨆i∈{i | w i = 0 }, range (std_basis α (λi, α) i)) :=
begin
  rw [← comap_bot, ← infi_ker_proj],
  simp only [comap_infi, (ker_comp _ _).symm, proj_diagonal, ker_smul'],
  have : univ ⊆ {i : m | w i = 0} ∪ -{i : m | w i = 0}, { rw set.union_compl_self },
  exact (supr_range_std_basis_eq_infi_ker_proj α (λi:m, α)
    (disjoint_compl {i | w i = 0}) this (finite.of_fintype _)).symm
end

lemma range_diagonal [decidable_eq m] (w : m → α) :
  (diagonal w).to_lin.range = (⨆ i ∈ {i | w i ≠ 0}, (std_basis α (λi, α) i).range) :=
begin
  dsimp only [mem_set_of_eq],
  rw [← map_top, ← supr_range_std_basis, map_supr],
  congr, funext i,
  rw [← linear_map.range_comp, diagonal_comp_std_basis, range_smul'],
end

lemma rank_diagonal [decidable_eq m] [decidable_eq α] (w : m → α) :
  rank (diagonal w).to_lin = fintype.card { i // w i ≠ 0 } :=
begin
  have hu : univ ⊆ - {i : m | w i = 0} ∪ {i : m | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : m | w i ≠ 0} {i : m | w i = 0} := (disjoint_compl {i | w i = 0}).symm,
  have h₁ := supr_range_std_basis_eq_infi_ker_proj α (λi:m, α) hd hu (finite.of_fintype _),
  have h₂ := @infi_ker_proj_equiv α _ _ (λi:m, α) _ _ _ _ (by simp; apply_instance) hd hu,
  rw [rank, range_diagonal, h₁, ←@dim_fun' α],
  apply linear_equiv.dim_eq,
  apply h₂,
end

end vector_space

end matrix
