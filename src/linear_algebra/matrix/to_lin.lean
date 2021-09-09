/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import data.matrix.block
import linear_algebra.matrix.finite_dimensional
import linear_algebra.std_basis
import ring_theory.algebra_tower

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

 * `linear_map.to_matrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`,
   the `R`-linear equivalence from `M₁ →ₗ[R] M₂` to `matrix κ ι R`
 * `matrix.to_lin`: the inverse of `linear_map.to_matrix`
 * `linear_map.to_matrix'`: the `R`-linear equivalence from `(n → R) →ₗ[R] (m → R)`
   to `matrix n m R` (with the standard basis on `n → R` and `m → R`)
 * `matrix.to_lin'`: the inverse of `linear_map.to_matrix'`
 * `alg_equiv_matrix`: given a basis indexed by `n`, the `R`-algebra equivalence between
   `R`-endomorphisms of `M` and `matrix n n R`

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace
-/

noncomputable theory

open linear_map matrix set submodule
open_locale big_operators
open_locale matrix

universes u v w

section to_matrix'

instance {n m} [fintype m] [decidable_eq m] [fintype n] [decidable_eq n] (R) [fintype R] :
  fintype (matrix m n R) := by unfold matrix; apply_instance

variables {R : Type*} [comm_ring R]
variables {l m n : Type*}

/-- `matrix.mul_vec M` is a linear map. -/
def matrix.mul_vec_lin [fintype n] (M : matrix m n R) : (n → R) →ₗ[R] (m → R) :=
{ to_fun := M.mul_vec,
  map_add' := λ v w, funext (λ i, dot_product_add _ _ _),
  map_smul' := λ c v, funext (λ i, dot_product_smul _ _ _) }

@[simp] lemma matrix.mul_vec_lin_apply [fintype n] (M : matrix m n R) (v : n → R) :
  matrix.mul_vec_lin M v = M.mul_vec v := rfl

variables [fintype n] [decidable_eq n]

@[simp] lemma matrix.mul_vec_std_basis (M : matrix m n R) (i j) :
  M.mul_vec (std_basis R (λ _, R) j 1) i = M i j :=
begin
  have : (∑ j', M i j' * if j = j' then 1 else 0) = M i j,
  { simp_rw [mul_boole, finset.sum_ite_eq, finset.mem_univ, if_true] },
  convert this,
  ext,
  split_ifs with h; simp only [std_basis_apply],
  { rw [h, function.update_same] },
  { rw [function.update_noteq (ne.symm h), pi.zero_apply] }
end

/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `matrix m n R`. -/
def linear_map.to_matrix' : ((n → R) →ₗ[R] (m → R)) ≃ₗ[R] matrix m n R :=
{ to_fun := λ f i j, f (std_basis R (λ _, R) j 1) i,
  inv_fun := matrix.mul_vec_lin,
  right_inv := λ M, by { ext i j, simp only [matrix.mul_vec_std_basis, matrix.mul_vec_lin_apply] },
  left_inv := λ f, begin
    apply (pi.basis_fun R n).ext,
    intro j, ext i,
    simp only [pi.basis_fun_apply, matrix.mul_vec_std_basis, matrix.mul_vec_lin_apply]
  end,
  map_add' := λ f g, by { ext i j, simp only [pi.add_apply, linear_map.add_apply] },
  map_smul' := λ c f, by { ext i j, simp [pi.smul_apply, linear_map.smul_apply] } }

/-- A `matrix m n R` is linearly equivalent to a linear map `(n → R) →ₗ[R] (m → R)`. -/
def matrix.to_lin' : matrix m n R ≃ₗ[R] ((n → R) →ₗ[R] (m → R)) :=
linear_map.to_matrix'.symm

@[simp] lemma linear_map.to_matrix'_symm :
  (linear_map.to_matrix'.symm : matrix m n R ≃ₗ[R] _) = matrix.to_lin' :=
rfl

@[simp] lemma matrix.to_lin'_symm :
  (matrix.to_lin'.symm : ((n → R) →ₗ[R] (m → R)) ≃ₗ[R] _) = linear_map.to_matrix' :=
rfl

@[simp] lemma linear_map.to_matrix'_to_lin' (M : matrix m n R) :
  linear_map.to_matrix' (matrix.to_lin' M) = M :=
linear_map.to_matrix'.apply_symm_apply M

@[simp] lemma matrix.to_lin'_to_matrix' (f : (n → R) →ₗ[R] (m → R)) :
  matrix.to_lin' (linear_map.to_matrix' f) = f :=
matrix.to_lin'.apply_symm_apply f

@[simp] lemma linear_map.to_matrix'_apply (f : (n → R) →ₗ[R] (m → R)) (i j) :
  linear_map.to_matrix' f i j = f (λ j', if j' = j then 1 else 0) i :=
begin
  simp only [linear_map.to_matrix', linear_equiv.coe_mk],
  congr,
  ext j',
  split_ifs with h,
  { rw [h, std_basis_same] },
  apply std_basis_ne _ _ _ _ h
end

@[simp] lemma matrix.to_lin'_apply (M : matrix m n R) (v : n → R) :
  matrix.to_lin' M v = M.mul_vec v := rfl

@[simp] lemma matrix.to_lin'_one :
  matrix.to_lin' (1 : matrix n n R) = id :=
by { ext, simp [linear_map.one_apply, std_basis_apply] }

@[simp] lemma linear_map.to_matrix'_id :
  (linear_map.to_matrix' (linear_map.id : (n → R) →ₗ[R] (n → R))) = 1 :=
by { ext, rw [matrix.one_apply, linear_map.to_matrix'_apply, id_apply] }

@[simp] lemma matrix.to_lin'_mul [fintype m] [decidable_eq m] (M : matrix l m R)
  (N : matrix m n R) : matrix.to_lin' (M ⬝ N) = (matrix.to_lin' M).comp (matrix.to_lin' N) :=
by { ext, simp }

/-- Shortcut lemma for `matrix.to_lin'_mul` and `linear_map.comp_apply` -/
lemma matrix.to_lin'_mul_apply [fintype m] [decidable_eq m] (M : matrix l m R)
  (N : matrix m n R) (x) : matrix.to_lin' (M ⬝ N) x = (matrix.to_lin' M (matrix.to_lin' N x)) :=
by rw [matrix.to_lin'_mul, linear_map.comp_apply]

lemma linear_map.to_matrix'_comp [fintype l] [decidable_eq l]
  (f : (n → R) →ₗ[R] (m → R)) (g : (l → R) →ₗ[R] (n → R)) :
  (f.comp g).to_matrix' = f.to_matrix' ⬝ g.to_matrix' :=
suffices (f.comp g) = (f.to_matrix' ⬝ g.to_matrix').to_lin',
  by rw [this, linear_map.to_matrix'_to_lin'],
by rw [matrix.to_lin'_mul, matrix.to_lin'_to_matrix', matrix.to_lin'_to_matrix']

lemma linear_map.to_matrix'_mul [fintype m] [decidable_eq m]
  (f g : (m → R) →ₗ[R] (m → R)) :
  (f * g).to_matrix' = f.to_matrix' ⬝ g.to_matrix' :=
linear_map.to_matrix'_comp f g

lemma matrix.ker_to_lin'_eq_bot_iff {M : matrix n n R} :
  M.to_lin'.ker = ⊥ ↔ ∀ v, M.mul_vec v = 0 → v = 0 :=
by simp only [submodule.eq_bot_iff, linear_map.mem_ker, matrix.to_lin'_apply]

/-- If `M` and `M'` are each other's inverse matrices, they provide an equivalence between `m → A`
and `n → A` corresponding to `M.mul_vec` and `M'.mul_vec`. -/
@[simps]
def matrix.to_lin'_of_inv [fintype m] [decidable_eq m]
  {M : matrix m n R} {M' : matrix n m R}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  (m → R) ≃ₗ[R] (n → R) :=
{ to_fun := matrix.to_lin' M',
  inv_fun := M.to_lin',
  left_inv := λ x, by rw [← matrix.to_lin'_mul_apply, hMM', matrix.to_lin'_one, id_apply],
  right_inv := λ x, by rw [← matrix.to_lin'_mul_apply, hM'M, matrix.to_lin'_one, id_apply],
  .. matrix.to_lin' M' }

/-- Linear maps `(n → R) →ₗ[R] (n → R)` are algebra equivalent to `matrix n n R`. -/
def linear_map.to_matrix_alg_equiv' : ((n → R) →ₗ[R] (n → R)) ≃ₐ[R] matrix n n R :=
alg_equiv.of_linear_equiv linear_map.to_matrix' linear_map.to_matrix'_mul
  (by simp [module.algebra_map_End_eq_smul_id])

/-- A `matrix n n R` is algebra equivalent to a linear map `(n → R) →ₗ[R] (n → R)`. -/
def matrix.to_lin_alg_equiv' : matrix n n R ≃ₐ[R] ((n → R) →ₗ[R] (n → R)) :=
linear_map.to_matrix_alg_equiv'.symm

@[simp] lemma linear_map.to_matrix_alg_equiv'_symm :
  (linear_map.to_matrix_alg_equiv'.symm : matrix n n R ≃ₐ[R] _) = matrix.to_lin_alg_equiv' :=
rfl

@[simp] lemma matrix.to_lin_alg_equiv'_symm :
  (matrix.to_lin_alg_equiv'.symm : ((n → R) →ₗ[R] (n → R)) ≃ₐ[R] _) =
    linear_map.to_matrix_alg_equiv' :=
rfl

@[simp] lemma linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv' (M : matrix n n R) :
  linear_map.to_matrix_alg_equiv' (matrix.to_lin_alg_equiv' M) = M :=
linear_map.to_matrix_alg_equiv'.apply_symm_apply M

@[simp] lemma matrix.to_lin_alg_equiv'_to_matrix_alg_equiv' (f : (n → R) →ₗ[R] (n → R)) :
  matrix.to_lin_alg_equiv' (linear_map.to_matrix_alg_equiv' f) = f :=
matrix.to_lin_alg_equiv'.apply_symm_apply f

@[simp] lemma linear_map.to_matrix_alg_equiv'_apply (f : (n → R) →ₗ[R] (n → R)) (i j) :
  linear_map.to_matrix_alg_equiv' f i j = f (λ j', if j' = j then 1 else 0) i :=
by simp [linear_map.to_matrix_alg_equiv']

@[simp] lemma matrix.to_lin_alg_equiv'_apply (M : matrix n n R) (v : n → R) :
  matrix.to_lin_alg_equiv' M v = M.mul_vec v := rfl

@[simp] lemma matrix.to_lin_alg_equiv'_one :
  matrix.to_lin_alg_equiv' (1 : matrix n n R) = id :=
by { ext, simp [matrix.one_apply, std_basis_apply] }

@[simp] lemma linear_map.to_matrix_alg_equiv'_id :
  (linear_map.to_matrix_alg_equiv' (linear_map.id : (n → R) →ₗ[R] (n → R))) = 1 :=
by { ext, rw [matrix.one_apply, linear_map.to_matrix_alg_equiv'_apply, id_apply] }

@[simp] lemma matrix.to_lin_alg_equiv'_mul (M N : matrix n n R) :
  matrix.to_lin_alg_equiv' (M ⬝ N) =
    (matrix.to_lin_alg_equiv' M).comp (matrix.to_lin_alg_equiv' N) :=
by { ext, simp }

lemma linear_map.to_matrix_alg_equiv'_comp (f g : (n → R) →ₗ[R] (n → R)) :
  (f.comp g).to_matrix_alg_equiv' = f.to_matrix_alg_equiv' ⬝ g.to_matrix_alg_equiv' :=
suffices (f.comp g) = (f.to_matrix_alg_equiv' ⬝ g.to_matrix_alg_equiv').to_lin_alg_equiv',
  by rw [this, linear_map.to_matrix_alg_equiv'_to_lin_alg_equiv'],
by rw [matrix.to_lin_alg_equiv'_mul, matrix.to_lin_alg_equiv'_to_matrix_alg_equiv',
       matrix.to_lin_alg_equiv'_to_matrix_alg_equiv']

lemma linear_map.to_matrix_alg_equiv'_mul
  (f g : (n → R) →ₗ[R] (n → R)) :
  (f * g).to_matrix_alg_equiv' = f.to_matrix_alg_equiv' ⬝ g.to_matrix_alg_equiv' :=
linear_map.to_matrix_alg_equiv'_comp f g

lemma matrix.rank_vec_mul_vec {K m n : Type u} [field K] [fintype n] [decidable_eq n]
  (w : m → K) (v : n → K) :
rank (vec_mul_vec w v).to_lin' ≤ 1 :=
begin
  rw [vec_mul_vec_eq, matrix.to_lin'_mul],
  refine le_trans (rank_comp_le1 _ _) _,
  refine le_trans (rank_le_domain _) _,
  rw [dim_fun', ← cardinal.lift_eq_nat_iff.mpr (cardinal.fintype_card unit), cardinal.mk_unit],
  exact le_of_eq (cardinal.lift_one)
end

end to_matrix'

section to_matrix

variables {R : Type*} [comm_ring R]
variables {l m n : Type*} [fintype n] [fintype m] [decidable_eq n]
variables {M₁ M₂ : Type*} [add_comm_group M₁] [add_comm_group M₂] [module R M₁] [module R M₂]
variables (v₁ : basis n R M₁) (v₂ : basis m R M₂)

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def linear_map.to_matrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] matrix m n R :=
linear_equiv.trans (linear_equiv.arrow_congr v₁.equiv_fun v₂.equiv_fun) linear_map.to_matrix'

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
def matrix.to_lin : matrix m n R ≃ₗ[R] (M₁ →ₗ[R] M₂) :=
(linear_map.to_matrix v₁ v₂).symm

@[simp] lemma linear_map.to_matrix_symm :
  (linear_map.to_matrix v₁ v₂).symm = matrix.to_lin v₁ v₂ :=
rfl

@[simp] lemma matrix.to_lin_symm :
  (matrix.to_lin v₁ v₂).symm = linear_map.to_matrix v₁ v₂ :=
rfl

@[simp] lemma matrix.to_lin_to_matrix (f : M₁ →ₗ[R] M₂) :
  matrix.to_lin v₁ v₂ (linear_map.to_matrix v₁ v₂ f) = f :=
by rw [← matrix.to_lin_symm, linear_equiv.apply_symm_apply]

@[simp] lemma linear_map.to_matrix_to_lin (M : matrix m n R) :
  linear_map.to_matrix v₁ v₂ (matrix.to_lin v₁ v₂ M) = M :=
by rw [← matrix.to_lin_symm, linear_equiv.symm_apply_apply]

lemma linear_map.to_matrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
  linear_map.to_matrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
begin
  rw [linear_map.to_matrix, linear_equiv.trans_apply, linear_map.to_matrix'_apply,
      linear_equiv.arrow_congr_apply, basis.equiv_fun_symm_apply, finset.sum_eq_single j,
      if_pos rfl, one_smul, basis.equiv_fun_apply],
  { intros j' _ hj',
    rw [if_neg hj', zero_smul] },
  { intro hj,
    have := finset.mem_univ j,
    contradiction }
end

lemma linear_map.to_matrix_transpose_apply (f : M₁ →ₗ[R] M₂) (j : n) :
  (linear_map.to_matrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
funext $ λ i, f.to_matrix_apply _ _ i j

lemma linear_map.to_matrix_apply' (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
  linear_map.to_matrix v₁ v₂ f i j = v₂.repr (f (v₁ j)) i :=
linear_map.to_matrix_apply v₁ v₂ f i j

lemma linear_map.to_matrix_transpose_apply' (f : M₁ →ₗ[R] M₂) (j : n) :
  (linear_map.to_matrix v₁ v₂ f)ᵀ j = v₂.repr (f (v₁ j)) :=
linear_map.to_matrix_transpose_apply v₁ v₂ f j

lemma matrix.to_lin_apply (M : matrix m n R) (v : M₁) :
  matrix.to_lin v₁ v₂ M v = ∑ j, M.mul_vec (v₁.repr v) j • v₂ j :=
show v₂.equiv_fun.symm (matrix.to_lin' M (v₁.repr v)) = _,
by rw [matrix.to_lin'_apply, v₂.equiv_fun_symm_apply]

@[simp] lemma matrix.to_lin_self (M : matrix m n R) (i : n) :
  matrix.to_lin v₁ v₂ M (v₁ i) = ∑ j, M j i • v₂ j :=
begin
  rw [matrix.to_lin_apply, finset.sum_congr rfl (λ j hj, _)],
  rw [basis.repr_self, matrix.mul_vec, dot_product, finset.sum_eq_single i,
      finsupp.single_eq_same, mul_one],
  { intros i' _ i'_ne, rw [finsupp.single_eq_of_ne i'_ne.symm, mul_zero] },
  { intros,
    have := finset.mem_univ i,
    contradiction },
end

/-- This will be a special case of `linear_map.to_matrix_id_eq_basis_to_matrix`. -/
lemma linear_map.to_matrix_id : linear_map.to_matrix v₁ v₁ id = 1 :=
begin
  ext i j,
  simp [linear_map.to_matrix_apply, matrix.one_apply, finsupp.single, eq_comm]
end

lemma linear_map.to_matrix_one : linear_map.to_matrix v₁ v₁ 1 = 1 :=
linear_map.to_matrix_id v₁

@[simp]
lemma matrix.to_lin_one : matrix.to_lin v₁ v₁ 1 = id :=
by rw [← linear_map.to_matrix_id v₁, matrix.to_lin_to_matrix]

theorem linear_map.to_matrix_reindex_range [decidable_eq M₁] [decidable_eq M₂]
  (f : M₁ →ₗ[R] M₂) (k : m) (i : n) :
  linear_map.to_matrix v₁.reindex_range v₂.reindex_range f
      ⟨v₂ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_map.to_matrix v₁ v₂ f k i :=
by simp_rw [linear_map.to_matrix_apply, basis.reindex_range_self, basis.reindex_range_repr]

variables {M₃ : Type*} [add_comm_group M₃] [module R M₃] (v₃ : basis l R M₃)

lemma linear_map.to_matrix_comp [fintype l] [decidable_eq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
  linear_map.to_matrix v₁ v₃ (f.comp g) =
  linear_map.to_matrix v₂ v₃ f ⬝ linear_map.to_matrix v₁ v₂ g :=
by simp_rw [linear_map.to_matrix, linear_equiv.trans_apply,
            linear_equiv.arrow_congr_comp _ v₂.equiv_fun, linear_map.to_matrix'_comp]

lemma linear_map.to_matrix_mul (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix v₁ v₁ (f * g) =
    linear_map.to_matrix v₁ v₁ f ⬝ linear_map.to_matrix v₁ v₁ g :=
by { rw [show (@has_mul.mul (M₁ →ₗ[R] M₁) _) = linear_map.comp, from rfl,
         linear_map.to_matrix_comp v₁ v₁ v₁ f g] }

lemma linear_map.to_matrix_mul_vec_repr (f : M₁ →ₗ[R] M₂) (x : M₁) :
  (linear_map.to_matrix v₁ v₂ f).mul_vec (v₁.repr x) = v₂.repr (f x) :=
by { ext i,
     rw [← matrix.to_lin'_apply, linear_map.to_matrix, linear_equiv.trans_apply,
         matrix.to_lin'_to_matrix', linear_equiv.arrow_congr_apply, v₂.equiv_fun_apply],
     congr,
     exact v₁.equiv_fun.symm_apply_apply x }

lemma matrix.to_lin_mul [fintype l] [decidable_eq m] (A : matrix l m R) (B : matrix m n R) :
  matrix.to_lin v₁ v₃ (A ⬝ B) =
  (matrix.to_lin v₂ v₃ A).comp (matrix.to_lin v₁ v₂ B) :=
begin
  apply (linear_map.to_matrix v₁ v₃).injective,
  haveI : decidable_eq l := λ _ _, classical.prop_decidable _,
  rw linear_map.to_matrix_comp v₁ v₂ v₃,
  repeat { rw linear_map.to_matrix_to_lin },
end

/-- Shortcut lemma for `matrix.to_lin_mul` and `linear_map.comp_apply`. -/
lemma matrix.to_lin_mul_apply [fintype l] [decidable_eq m]
  (A : matrix l m R) (B : matrix m n R) (x) :
  matrix.to_lin v₁ v₃ (A ⬝ B) x =
    (matrix.to_lin v₂ v₃ A) (matrix.to_lin v₁ v₂ B x) :=
by rw [matrix.to_lin_mul v₁ v₂, linear_map.comp_apply]

/-- If `M` and `M` are each other's inverse matrices, `matrix.to_lin M` and `matrix.to_lin M'`
form a linear equivalence. -/
@[simps]
def matrix.to_lin_of_inv [decidable_eq m]
  {M : matrix m n R} {M' : matrix n m R}
  (hMM' : M ⬝ M' = 1) (hM'M : M' ⬝ M = 1) :
  M₁ ≃ₗ[R] M₂ :=
{ to_fun := matrix.to_lin v₁ v₂ M,
  inv_fun := matrix.to_lin v₂ v₁ M',
  left_inv := λ x, by rw [← matrix.to_lin_mul_apply, hM'M, matrix.to_lin_one, id_apply],
  right_inv := λ x, by rw [← matrix.to_lin_mul_apply, hMM', matrix.to_lin_one, id_apply],
  .. matrix.to_lin v₁ v₂ M }

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed by the basis. -/
def linear_map.to_matrix_alg_equiv :
  (M₁ →ₗ[R] M₁) ≃ₐ[R] matrix n n R :=
alg_equiv.of_linear_equiv (linear_map.to_matrix v₁ v₁) (linear_map.to_matrix_mul v₁)
  (by simp [module.algebra_map_End_eq_smul_id, linear_map.to_matrix_id])

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear maps `M₁ →ₗ M₁`. -/
def matrix.to_lin_alg_equiv : matrix n n R ≃ₐ[R] (M₁ →ₗ[R] M₁) :=
(linear_map.to_matrix_alg_equiv v₁).symm

@[simp] lemma linear_map.to_matrix_alg_equiv_symm :
  (linear_map.to_matrix_alg_equiv v₁).symm = matrix.to_lin_alg_equiv v₁ :=
rfl

@[simp] lemma matrix.to_lin_alg_equiv_symm :
  (matrix.to_lin_alg_equiv v₁).symm = linear_map.to_matrix_alg_equiv v₁ :=
rfl

@[simp] lemma matrix.to_lin_alg_equiv_to_matrix_alg_equiv (f : M₁ →ₗ[R] M₁) :
  matrix.to_lin_alg_equiv v₁ (linear_map.to_matrix_alg_equiv v₁ f) = f :=
by rw [← matrix.to_lin_alg_equiv_symm, alg_equiv.apply_symm_apply]

@[simp] lemma linear_map.to_matrix_alg_equiv_to_lin_alg_equiv (M : matrix n n R) :
  linear_map.to_matrix_alg_equiv v₁ (matrix.to_lin_alg_equiv v₁ M) = M :=
by rw [← matrix.to_lin_alg_equiv_symm, alg_equiv.symm_apply_apply]

lemma linear_map.to_matrix_alg_equiv_apply (f : M₁ →ₗ[R] M₁) (i j : n) :
  linear_map.to_matrix_alg_equiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
by simp [linear_map.to_matrix_alg_equiv, linear_map.to_matrix_apply]

lemma linear_map.to_matrix_alg_equiv_transpose_apply (f : M₁ →ₗ[R] M₁) (j : n) :
  (linear_map.to_matrix_alg_equiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
funext $ λ i, f.to_matrix_apply _ _ i j

lemma linear_map.to_matrix_alg_equiv_apply' (f : M₁ →ₗ[R] M₁) (i j : n) :
  linear_map.to_matrix_alg_equiv v₁ f i j = v₁.repr (f (v₁ j)) i :=
linear_map.to_matrix_alg_equiv_apply v₁ f i j

lemma linear_map.to_matrix_alg_equiv_transpose_apply' (f : M₁ →ₗ[R] M₁) (j : n) :
  (linear_map.to_matrix_alg_equiv v₁ f)ᵀ j = v₁.repr (f (v₁ j)) :=
linear_map.to_matrix_alg_equiv_transpose_apply v₁ f j

lemma matrix.to_lin_alg_equiv_apply (M : matrix n n R) (v : M₁) :
  matrix.to_lin_alg_equiv v₁ M v = ∑ j, M.mul_vec (v₁.repr v) j • v₁ j :=
show v₁.equiv_fun.symm (matrix.to_lin_alg_equiv' M (v₁.repr v)) = _,
by rw [matrix.to_lin_alg_equiv'_apply, v₁.equiv_fun_symm_apply]

@[simp] lemma matrix.to_lin_alg_equiv_self (M : matrix n n R) (i : n) :
  matrix.to_lin_alg_equiv v₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
matrix.to_lin_self _ _ _ _

lemma linear_map.to_matrix_alg_equiv_id : linear_map.to_matrix_alg_equiv v₁ id = 1 :=
by simp_rw [linear_map.to_matrix_alg_equiv, alg_equiv.of_linear_equiv_apply,
            linear_map.to_matrix_id]

@[simp]
lemma matrix.to_lin_alg_equiv_one : matrix.to_lin_alg_equiv v₁ 1 = id :=
by rw [← linear_map.to_matrix_alg_equiv_id v₁, matrix.to_lin_alg_equiv_to_matrix_alg_equiv]

theorem linear_map.to_matrix_alg_equiv_reindex_range [decidable_eq M₁]
  (f : M₁ →ₗ[R] M₁) (k i : n) :
  linear_map.to_matrix_alg_equiv v₁.reindex_range f
      ⟨v₁ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_map.to_matrix_alg_equiv v₁ f k i :=
by simp_rw [linear_map.to_matrix_alg_equiv_apply,
            basis.reindex_range_self, basis.reindex_range_repr]

lemma linear_map.to_matrix_alg_equiv_comp (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix_alg_equiv v₁ (f.comp g) =
  linear_map.to_matrix_alg_equiv v₁ f ⬝ linear_map.to_matrix_alg_equiv v₁ g :=
by simp [linear_map.to_matrix_alg_equiv, linear_map.to_matrix_comp v₁ v₁ v₁ f g]

lemma linear_map.to_matrix_alg_equiv_mul (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix_alg_equiv v₁ (f * g) =
    linear_map.to_matrix_alg_equiv v₁ f ⬝ linear_map.to_matrix_alg_equiv v₁ g :=
by { rw [show (@has_mul.mul (M₁ →ₗ[R] M₁) _) = linear_map.comp, from rfl,
         linear_map.to_matrix_alg_equiv_comp v₁ f g] }

lemma matrix.to_lin_alg_equiv_mul (A B : matrix n n R) :
  matrix.to_lin_alg_equiv v₁ (A ⬝ B) =
  (matrix.to_lin_alg_equiv v₁ A).comp (matrix.to_lin_alg_equiv v₁ B) :=
by convert matrix.to_lin_mul v₁ v₁ v₁ A B

end to_matrix

namespace algebra

section lmul

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra S T] [algebra R T] [is_scalar_tower R S T]
variables {m n : Type*} [fintype m] [decidable_eq m] [decidable_eq n]
variables (b : basis m R S) (c : basis n S T)

open algebra

lemma to_matrix_lmul' (x : S) (i j) :
  linear_map.to_matrix b b (lmul R S x) i j = b.repr (x * b j) i :=
by rw [linear_map.to_matrix_apply', lmul_apply]

@[simp] lemma to_matrix_lsmul (x : R) (i j) :
  linear_map.to_matrix b b (algebra.lsmul R S x) i j = if i = j then x else 0 :=
by { rw [linear_map.to_matrix_apply', algebra.lsmul_coe, linear_equiv.map_smul, finsupp.smul_apply,
         b.repr_self_apply, smul_eq_mul, mul_boole],
     congr' 1; simp only [eq_comm] }

/-- `left_mul_matrix b x` is the matrix corresponding to the linear map `λ y, x * y`.

`left_mul_matrix_eq_repr_mul` gives a formula for the entries of `left_mul_matrix`.

This definition is useful for doing (more) explicit computations with `algebra.lmul`,
such as the trace form or norm map for algebras.
-/
noncomputable def left_mul_matrix : S →ₐ[R] matrix m m R :=
{ to_fun := λ x, linear_map.to_matrix b b (algebra.lmul R S x),
  map_zero' := by rw [alg_hom.map_zero, linear_equiv.map_zero],
  map_one' := by rw [alg_hom.map_one, linear_map.to_matrix_one],
  map_add' := λ x y, by rw [alg_hom.map_add, linear_equiv.map_add],
  map_mul' := λ x y, by rw [alg_hom.map_mul, linear_map.to_matrix_mul, matrix.mul_eq_mul],
  commutes' := λ r, by { ext, rw [lmul_algebra_map, to_matrix_lsmul,
                                  algebra_map_matrix_apply, id.map_eq_self] } }

lemma left_mul_matrix_apply (x : S) :
  left_mul_matrix b x = linear_map.to_matrix b b (lmul R S x) := rfl

lemma left_mul_matrix_eq_repr_mul (x : S) (i j) :
  left_mul_matrix b x i j = b.repr (x * b j) i :=
-- This is defeq to just `to_matrix_lmul' b x i j`,
-- but the unfolding goes a lot faster with this explicit `rw`.
by rw [left_mul_matrix_apply, to_matrix_lmul' b x i j]

lemma left_mul_matrix_mul_vec_repr (x y : S) :
  (left_mul_matrix b x).mul_vec (b.repr y) = b.repr (x * y) :=
linear_map.to_matrix_mul_vec_repr b b (algebra.lmul R S x) y

@[simp] lemma to_matrix_lmul_eq (x : S) :
  linear_map.to_matrix b b (lmul R S x) = left_mul_matrix b x :=
rfl

lemma left_mul_matrix_injective : function.injective (left_mul_matrix b) :=
λ x x' h, calc x = algebra.lmul R S x 1 : (mul_one x).symm
             ... = algebra.lmul R S x' 1 : by rw (linear_map.to_matrix b b).injective h
             ... = x' : mul_one x'

variable [fintype n]

lemma smul_left_mul_matrix (x) (ik jk) :
  left_mul_matrix (b.smul c) x ik jk =
    left_mul_matrix b (left_mul_matrix c x ik.2 jk.2) ik.1 jk.1 :=
by simp only [left_mul_matrix_apply, linear_map.to_matrix_apply, mul_comm, basis.smul_apply,
              basis.smul_repr, finsupp.smul_apply, algebra.lmul_apply, id.smul_eq_mul,
              linear_equiv.map_smul, mul_smul_comm]

lemma smul_left_mul_matrix_algebra_map (x : S) :
  left_mul_matrix (b.smul c) (algebra_map _ _ x) = block_diagonal (λ k, left_mul_matrix b x) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  rw [smul_left_mul_matrix, alg_hom.commutes, block_diagonal_apply, algebra_map_matrix_apply],
  split_ifs with h; simp [h],
end

lemma smul_left_mul_matrix_algebra_map_eq (x : S) (i j k) :
  left_mul_matrix (b.smul c) (algebra_map _ _ x) (i, k) (j, k) = left_mul_matrix b x i j :=
by rw [smul_left_mul_matrix_algebra_map, block_diagonal_apply_eq]

lemma smul_left_mul_matrix_algebra_map_ne (x : S) (i j) {k k'}
  (h : k ≠ k') : left_mul_matrix (b.smul c) (algebra_map _ _ x) (i, k) (j, k') = 0 :=
by rw [smul_left_mul_matrix_algebra_map, block_diagonal_apply_ne _ _ _ h]

end lmul

end algebra

namespace linear_map

section finite_dimensional

open_locale classical

variables {K : Type*} [field K]
variables {V : Type*} [add_comm_group V] [module K V] [finite_dimensional K V]
variables {W : Type*} [add_comm_group W] [module K W] [finite_dimensional K W]

instance : finite_dimensional K (V →ₗ[K] W) :=
linear_equiv.finite_dimensional
  (linear_map.to_matrix (basis.of_vector_space K V) (basis.of_vector_space K W)).symm

/--
The dimension of the space of linear transformations is the product of the dimensions of the
domain and codomain.
-/
@[simp] lemma finrank_linear_map :
  finite_dimensional.finrank K (V →ₗ[K] W) =
  (finite_dimensional.finrank K V) * (finite_dimensional.finrank K W) :=
begin
  let hbV := basis.of_vector_space K V,
  let hbW := basis.of_vector_space K W,
  rw [linear_equiv.finrank_eq (linear_map.to_matrix hbV hbW), matrix.finrank_matrix,
    finite_dimensional.finrank_eq_card_basis hbV, finite_dimensional.finrank_eq_card_basis hbW,
    mul_comm],
end

end finite_dimensional
end linear_map

section

variables {R : Type v} [comm_ring R] {n : Type*} [decidable_eq n]
variables {M M₁ M₂ : Type*} [add_comm_group M] [module R M]
variables [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂]

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def alg_equiv_matrix' [fintype n] : module.End R (n → R) ≃ₐ[R] matrix n n R :=
{ map_mul'  := linear_map.to_matrix'_comp,
  map_add'  := linear_map.to_matrix'.map_add,
  commutes' := λ r, by { change (r • (linear_map.id : module.End R _)).to_matrix' = r • 1,
                         rw ←linear_map.to_matrix'_id, refl, apply_instance },
  ..linear_map.to_matrix' }

/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
def linear_equiv.alg_conj (e : M₁ ≃ₗ[R] M₂) :
  module.End R M₁ ≃ₐ[R] module.End R M₂ :=
{ map_mul'  := λ f g, by apply e.arrow_congr_comp,
  map_add'  := e.conj.map_add,
  commutes' := λ r, by { change e.conj (r • linear_map.id) = r • linear_map.id,
                         rw [linear_equiv.map_smul, linear_equiv.conj_id], },
  ..e.conj }

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def alg_equiv_matrix [fintype n] (h : basis n R M) : module.End R M ≃ₐ[R] matrix n n R :=
h.equiv_fun.alg_conj.trans alg_equiv_matrix'

end
