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
universes u v w
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

section
open finsupp

lemma is_basis_single [decidable_eq n] [decidable_eq α] :
  is_basis α (λ i:n, (single i (1:α)).to_fun) :=
begin
  convert pi.is_basis_fun α; apply_instance <|>
  ext i j,
  rw [std_basis_apply, show (single _ _).to_fun _ = _, from single_apply],
  split_ifs,
  { rw [h, function.update_same] },
  { rw [function.update_noteq (ne.symm h)], refl },
  apply_instance
end

lemma to_matrix_to_lin [decidable_eq n] [decidable_eq α] {f : (n → α) →ₗ[α] (m → α)} :
  to_lin (to_matrix f) = f :=
begin
  ext g : 1,
  convert linear_eq_on (set.range (λ i : n, (single i (1:α)).to_fun)) _ _,
  { assume e he,
    rw [set.mem_range] at he,
    cases he with i h,
    ext j,
    change finset.univ.sum (λ k, (f.to_fun (single k 1).to_fun) j * (e k)) = _,
    conv_lhs { congr, skip, funext, rw [mul_comm _ (e k)] },
    change finset.univ.sum (λ k, (e k) • (f.to_fun (single k 1).to_fun) j) = _,
    rw [←h],
    conv_lhs { congr, skip, funext,
      rw [←pi.smul_apply, ←linear_map.smul,
        show (single _ _).to_fun _ = _, from @single_swap n α _ _ _ i k _],
      rw [single_apply],
      rw [show ite (k = i) (1:α) 0 • (single k (1:α)).to_fun = ite (k = i) (single i 1).to_fun 0, from
        begin split_ifs, { rw[h_1, one_smul] }, { exact zero_smul _ _ } end],
      rw [show f.to_fun (ite (k = i) (single i 1).to_fun 0) = ite (k = i) (f.to_fun (single k 1).to_fun) 0, from
        begin split_ifs, { rw [h_1] }, { exact linear_map.map_zero f } end],
      },
      convert finset.sum_eq_single i _ _,
      { rw [if_pos rfl], refl },
      { assume _ _ hbi, rw [if_neg hbi], refl },
      { assume hi, exact false.elim (hi $ finset.mem_univ i) } },
  { refine is_basis.mem_span _ g,
    convert pi.is_basis_fun α; apply_instance <|>
    ext i j,
    rw [std_basis_apply, show (single _ _).to_fun _ = _, from single_apply],
    split_ifs,
    { rw [h, function.update_same] },
    { rw [function.update_noteq (ne.symm h)], refl },
    apply_instance }
end

lemma to_lin_to_matrix [decidable_eq n] {M : matrix m n α} : to_matrix (to_lin M) = M :=
begin
  ext,
  change finset.sum finset.univ (λ y, M i y * ite (j = y) 1 0) = M i j,
  have : (λ y, M i y * ite (j = y) 1 0) = (λ y, ite (j = y) (M i y) 0),
    { ext, split_ifs, exact mul_one _, exact ring.mul_zero _ },
  rw [this],
  --from proof of to_finset_sum_count_eq in big_operators.lean (make a lemma?)
  have : finset.univ.sum (λ y, ite (j = y) (M i y) 0) = (finset.singleton j).sum (λ y, ite (j = y) (M i y) 0),
  { refine (finset.sum_subset _ _).symm,
    { intros _ H, rwa finset.mem_singleton.1 H, exact finset.mem_univ _ },
    { exact λ _ _ H, if_neg (mt (finset.mem_singleton.2 ∘ eq.symm) H) } },
  rw [this, finset.sum_singleton],
  exact if_pos rfl,
end

def lin_equiv_matrix' [decidable_eq α] [decidable_eq n] : ((n → α) →ₗ[α] (m → α)) ≃ₗ[α] matrix m n α :=
{ to_fun := to_matrix,
  inv_fun := to_lin,
  right_inv := λ _, to_lin_to_matrix,
  left_inv := λ _, to_matrix_to_lin,
  add := to_matrixₗ.add,
  smul := to_matrixₗ.smul }

def arrow_congr {α β₁ β₂ γ₁ γ₂ : Sort*} [comm_ring α]
  [add_comm_group β₁] [add_comm_group β₂] [add_comm_group γ₁] [add_comm_group γ₂]
  [module α β₁] [module α β₂] [module α γ₁] [module α γ₂]
  (e₁ : β₁ ≃ₗ[α] β₂) (e₂ : γ₁ ≃ₗ[α] γ₂) :
  (β₁ →ₗ[α] γ₁) ≃ₗ[α] (β₂ →ₗ[α] γ₂) :=
{ to_fun := λ f, e₂.to_linear_map.comp $ f.comp e₁.symm.to_linear_map,
  inv_fun := λ f, e₂.symm.to_linear_map.comp $ f.comp e₁.to_linear_map,
  left_inv := λ f, by { ext x, unfold_coes,
    change e₂.inv_fun (e₂.to_fun $ f.to_fun $ e₁.inv_fun $ e₁.to_fun x) = _,
    rw [e₁.left_inv, e₂.left_inv] },
  right_inv := λ f, by { ext x, dsimp, unfold_coes,
    change e₂.to_fun (e₂.inv_fun $ f.to_fun $ e₁.to_fun $ e₁.inv_fun x) = _,
    rw [e₁.right_inv, e₂.right_inv] },
  add := λ f g, by { ext x, change e₂.to_fun ((f + g) (e₁.inv_fun x)) = _,
    rw [linear_map.add_apply, e₂.add], refl },
  smul := λ c f, by { ext x, change e₂.to_fun ((c • f) (e₁.inv_fun x)) = _,
    rw [linear_map.smul_apply, e₂.smul], refl } }

def conj {α : Type u} {β : Type v} {γ : Type w} [comm_ring α] [add_comm_group β] [add_comm_group γ]
  [module α β] [module α γ] (e : β ≃ₗ[α] γ) : (β →ₗ[α] β) ≃ₗ[α] (γ →ₗ[α] γ) :=
arrow_congr e e

--TODO: Can do module instead of vector_space
set_option class.instance_max_depth 60
def lin_equiv_matrix {ι α : Type*} (β : Type*) [discrete_field α] [add_comm_group β] [decidable_eq β]
  [decidable_eq (ι → β)] [vector_space α β] [fintype ι] [decidable_eq ι] {v : ι → β} (hv : is_basis α v) :
  (β →ₗ[α] β) ≃ₗ[α] matrix ι ι α :=
linear_equiv.trans (conj $ equiv_fun_basis hv) lin_equiv_matrix'

end

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
