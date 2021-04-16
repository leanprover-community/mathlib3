/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz
-/
import linear_algebra.finite_dimensional
import linear_algebra.nonsingular_inverse
import linear_algebra.multilinear
import linear_algebra.dual
import ring_theory.algebra_tower
import ring_theory.matrix_algebra

/-!
# Linear maps and matrices

This file defines the maps to send matrices to a linear map,
and to send linear maps between modules with a finite bases
to matrices. This defines a linear equivalence between linear maps
between finite-dimensional vector spaces and matrices indexed by
the respective bases.

It also defines the trace of an endomorphism, and the determinant of a family of vectors with
respect to some basis.

Some results are proved about the linear map corresponding to a
diagonal matrix (`range`, `ker` and `rank`).

Some results are proved for determinants of block triangular matrices.

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
 * `matrix.trace`: the trace of a square matrix
 * `linear_map.trace`: the trace of an endomorphism
 * `basis.to_matrix`: the matrix whose columns are a given family of vectors in a given basis
 * `basis.to_matrix_equiv`: given a basis, the linear equivalence between families of vectors
   and matrices arising from `basis.to_matrix`
 * `basis.det`: the determinant of a family of vectors with respect to a basis, as a multilinear
   map

## Tags

linear_map, matrix, linear_equiv, diagonal, det, trace

-/

noncomputable theory

open linear_map matrix set submodule
open_locale big_operators
open_locale matrix

universes u v w

section to_matrix'

variables {R : Type*} [comm_ring R]
variables {l m n : Type*} [fintype l] [fintype m] [fintype n]

instance [decidable_eq m] [decidable_eq n] (R) [fintype R] : fintype (matrix m n R) :=
by unfold matrix; apply_instance

/-- `matrix.mul_vec M` is a linear map. -/
def matrix.mul_vec_lin (M : matrix m n R) : (n → R) →ₗ[R] (m → R) :=
{ to_fun := M.mul_vec,
  map_add' := λ v w, funext (λ i, dot_product_add _ _ _),
  map_smul' := λ c v, funext (λ i, dot_product_smul _ _ _) }

@[simp] lemma matrix.mul_vec_lin_apply (M : matrix m n R) (v : n → R) :
  matrix.mul_vec_lin M v = M.mul_vec v := rfl

variables [decidable_eq n]

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
  map_smul' := λ c f, by { ext i j, simp only [pi.smul_apply, linear_map.smul_apply] } }

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

@[simp] lemma matrix.to_lin'_mul [decidable_eq m] (M : matrix l m R) (N : matrix m n R) :
  matrix.to_lin' (M ⬝ N) = (matrix.to_lin' M).comp (matrix.to_lin' N) :=
by { ext, simp }

lemma linear_map.to_matrix'_comp [decidable_eq l]
  (f : (n → R) →ₗ[R] (m → R)) (g : (l → R) →ₗ[R] (n → R)) :
  (f.comp g).to_matrix' = f.to_matrix' ⬝ g.to_matrix' :=
suffices (f.comp g) = (f.to_matrix' ⬝ g.to_matrix').to_lin',
  by rw [this, linear_map.to_matrix'_to_lin'],
by rw [matrix.to_lin'_mul, matrix.to_lin'_to_matrix', matrix.to_lin'_to_matrix']

lemma linear_map.to_matrix'_mul [decidable_eq m]
  (f g : (m → R) →ₗ[R] (m → R)) :
  (f * g).to_matrix' = f.to_matrix' ⬝ g.to_matrix' :=
linear_map.to_matrix'_comp f g

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

end to_matrix'

section to_matrix

variables {R : Type*} [comm_ring R]
variables {l m n : Type*} [fintype l] [fintype m] [fintype n] [decidable_eq n]
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

theorem linear_map.to_matrix_reindex_range [nontrivial R] [decidable_eq M₁] [decidable_eq M₂]
  (f : M₁ →ₗ[R] M₂) (k : m) (i : n) :
  linear_map.to_matrix v₁.reindex_range v₂.reindex_range f
      ⟨v₂ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_map.to_matrix v₁ v₂ f k i :=
by simp_rw [linear_map.to_matrix_apply, basis.reindex_range_self, basis.reindex_range_repr]

variables {M₃ : Type*} [add_comm_group M₃] [module R M₃] (v₃ : basis l R M₃)

lemma linear_map.to_matrix_comp [decidable_eq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
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

lemma matrix.to_lin_mul [decidable_eq m] (A : matrix l m R) (B : matrix m n R) :
  matrix.to_lin v₁ v₃ (A ⬝ B) =
  (matrix.to_lin v₂ v₃ A).comp (matrix.to_lin v₁ v₂ B) :=
begin
  apply (linear_map.to_matrix v₁ v₃).injective,
  haveI : decidable_eq l := λ _ _, classical.prop_decidable _,
  rw linear_map.to_matrix_comp v₁ v₂ v₃,
  repeat { rw linear_map.to_matrix_to_lin },
end

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

theorem linear_map.to_matrix_alg_equiv_reindex_range [nontrivial R] [decidable_eq M₁]
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

section basis_to_matrix

variables {ι ι' κ κ' : Type*} [fintype ι] [fintype ι'] [fintype κ] [fintype κ']
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

open function matrix

/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def basis.to_matrix (e : basis ι R M) (v : ι' → M) : matrix ι ι' R :=
λ i j, e.repr (v j) i

variables (e : basis ι R M) (v : ι' → M) (i : ι) (j : ι')

namespace basis

lemma to_matrix_apply : e.to_matrix v i j = e.repr (v j) i :=
rfl

lemma to_matrix_transpose_apply : (e.to_matrix v)ᵀ j = e.repr (v j) :=
funext $ (λ _, rfl)

lemma to_matrix_eq_to_matrix_constr [decidable_eq ι] (v : ι → M) :
  e.to_matrix v = linear_map.to_matrix e e (e.constr ℕ v) :=
by { ext, rw [basis.to_matrix_apply, linear_map.to_matrix_apply, basis.constr_basis] }

@[simp] lemma to_matrix_self [decidable_eq ι] : e.to_matrix e = 1 :=
begin
  rw basis.to_matrix,
  ext i j,
  simp [basis.equiv_fun, matrix.one_apply, finsupp.single, eq_comm]
end

lemma to_matrix_update [decidable_eq ι'] (x : M) :
  e.to_matrix (function.update v j x) = matrix.update_column (e.to_matrix v) j (e.repr x) :=
begin
  ext i' k,
  rw [basis.to_matrix, matrix.update_column_apply, e.to_matrix_apply],
  split_ifs,
  { rw [h, update_same j x v] },
  { rw update_noteq h },
end

@[simp] lemma sum_to_matrix_smul_self : ∑ (i : ι), e.to_matrix v i j • e i = v j :=
by simp_rw [e.to_matrix_apply, e.sum_repr]

@[simp] lemma to_lin_to_matrix [decidable_eq ι'] (v : basis ι' R M) :
  matrix.to_lin v e (e.to_matrix v) = id :=
v.ext (λ i, by rw [to_lin_self, id_apply, e.sum_to_matrix_smul_self])

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def to_matrix_equiv (e : basis ι R M) : (ι → M) ≃ₗ[R] matrix ι ι R :=
{ to_fun := e.to_matrix,
  map_add' := λ v w, begin
    ext i j,
    change _ = _ + _,
    rw [e.to_matrix_apply, pi.add_apply, linear_equiv.map_add],
    refl
  end,
  map_smul' := begin
    intros c v,
    ext i j,
    rw [e.to_matrix_apply, pi.smul_apply, linear_equiv.map_smul],
    refl
  end,
  inv_fun := λ m j, ∑ i, (m i j) • e i,
  left_inv := begin
    intro v,
    ext j,
    exact e.sum_to_matrix_smul_self v j
  end,
  right_inv := begin
    intros m,
    ext k l,
    simp only [e.to_matrix_apply, ← e.equiv_fun_apply, ← e.equiv_fun_symm_apply,
               linear_equiv.apply_symm_apply],
  end }

end basis

section mul_linear_map_to_matrix

variables {N : Type*} [add_comm_group N] [module R N]
variables (b : basis ι R M) (b' : basis ι' R M) (c : basis κ R N) (c' : basis κ' R N)
variables (f : M →ₗ[R] N)

open linear_map

@[simp] lemma basis_to_matrix_mul_linear_map_to_matrix [decidable_eq ι'] :
  c.to_matrix c' ⬝ linear_map.to_matrix b' c' f = linear_map.to_matrix b' c f :=
(matrix.to_lin b' c).injective
  (by haveI := classical.dec_eq κ';
      rw [to_lin_to_matrix, to_lin_mul b' c' c, to_lin_to_matrix, c.to_lin_to_matrix, id_comp])

@[simp] lemma linear_map_to_matrix_mul_basis_to_matrix [decidable_eq ι] [decidable_eq ι'] :
  linear_map.to_matrix b' c' f ⬝ b'.to_matrix b = linear_map.to_matrix b c' f :=
(matrix.to_lin b c').injective
  (by rw [to_lin_to_matrix, to_lin_mul b b' c', to_lin_to_matrix, b'.to_lin_to_matrix, comp_id])

/-- A generalization of `linear_map.to_matrix_id`. -/
@[simp] lemma linear_map.to_matrix_id_eq_basis_to_matrix [decidable_eq ι] :
  linear_map.to_matrix b b' id = b'.to_matrix b :=
by { haveI := classical.dec_eq ι',
      rw [← basis_to_matrix_mul_linear_map_to_matrix b b', to_matrix_id, matrix.mul_one] }

/-- A generalization of `basis.to_matrix_self`, in the opposite direction. -/
@[simp] lemma basis.to_matrix_mul_to_matrix
  {ι'' : Type*} [fintype ι''] (b'' : basis ι'' R M) :
  b.to_matrix b' ⬝ b'.to_matrix b'' = b.to_matrix b'' :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq ι',
  haveI := classical.dec_eq ι'',
  rw [← linear_map.to_matrix_id_eq_basis_to_matrix b' b,
      ← linear_map.to_matrix_id_eq_basis_to_matrix b'' b',
      ← to_matrix_comp, id_comp, linear_map.to_matrix_id_eq_basis_to_matrix],
end

end mul_linear_map_to_matrix

end basis_to_matrix

open_locale matrix

section det

open linear_map matrix

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {M' : Type*} [add_comm_group M'] [module R M']
variables {ι : Type*} [decidable_eq ι] [fintype ι]

lemma linear_equiv.is_unit_det (f : M ≃ₗ[R] M') (v : basis ι R M) (v' : basis ι R M') :
  is_unit (linear_map.to_matrix v v' f).det :=
begin
  apply is_unit_det_of_left_inverse,
  simpa using (linear_map.to_matrix_comp v v' v f.symm f).symm
end

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
@[simps]
def linear_equiv.of_is_unit_det {f : M →ₗ[R] M'} {v : basis ι R M} {v' : basis ι R M'}
  (h : is_unit (linear_map.to_matrix v v' f).det) : M ≃ₗ[R] M' :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := f.map_smul,
  inv_fun := to_lin v' v (to_matrix v v' f)⁻¹,
  left_inv := λ x,
    calc to_lin v' v (to_matrix v v' f)⁻¹ (f x)
        = to_lin v v ((to_matrix v v' f)⁻¹ ⬝ to_matrix v v' f) x :
      by { rw [to_lin_mul v v' v, to_lin_to_matrix, linear_map.comp_apply] }
    ... = x : by simp [h],
  right_inv := λ x,
    calc f (to_lin v' v (to_matrix v v' f)⁻¹ x)
        = to_lin v' v' (to_matrix v v' f ⬝ (to_matrix v v' f)⁻¹) x :
      by { rw [to_lin_mul v' v v', linear_map.comp_apply, to_lin_to_matrix v v'] }
    ... = x : by simp [h],
  }

variables (e : basis ι R M)

/-- Te determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
def basis.det : alternating_map R M R ι :=
{ to_fun := λ v, det (e.to_matrix v),
  map_add' := begin
    intros v i x y,
    simp only [e.to_matrix_update, linear_equiv.map_add],
    apply det_update_column_add
  end,
  map_smul' := begin
    intros u i c x,
    simp only [e.to_matrix_update, algebra.id.smul_eq_mul, linear_equiv.map_smul],
    apply det_update_column_smul
  end,
  map_eq_zero_of_eq' := begin
    intros v i j h hij,
    rw [←function.update_eq_self i v, h, ←det_transpose, e.to_matrix_update,
        ←update_row_transpose, ←e.to_matrix_transpose_apply],
    apply det_zero_of_row_eq hij,
    rw [update_row_ne hij.symm, update_row_self],
  end }

lemma basis.det_apply (v : ι → M) : e.det v = det (e.to_matrix v) := rfl

lemma basis.det_self : e.det e = 1 :=
by simp [e.det_apply]

lemma is_basis.iff_det {v : ι → M} :
  linear_independent R v ∧ span R (set.range v) = ⊤ ↔ is_unit (e.det v) :=
begin
  split,
  { rintro ⟨hli, hspan⟩,
    set v' := basis.mk hli hspan with v'_eq,
    rw e.det_apply,
    convert linear_equiv.is_unit_det (linear_equiv.refl _ _) v' e using 2,
    ext i j,
    simp },
  { intro h,
    rw [basis.det_apply, basis.to_matrix_eq_to_matrix_constr] at h,
    set v' := basis.map e (linear_equiv.of_is_unit_det h) with v'_def,
    have : ⇑ v' = v,
    { ext i, rw [v'_def, basis.map_apply, linear_equiv.of_is_unit_det_apply, e.constr_basis] },
    rw ← this,
    exact ⟨v'.linear_independent, v'.span_eq⟩ },
end

end det

section transpose

variables {K V₁ V₂ ι₁ ι₂ : Type*} [field K]
          [add_comm_group V₁] [module K V₁]
          [add_comm_group V₂] [module K V₂]
          [fintype ι₁] [fintype ι₂] [decidable_eq ι₁] [decidable_eq ι₂]
          {B₁ : basis ι₁ K V₁}
          {B₂ : basis ι₂ K V₂}

@[simp] lemma linear_map.to_matrix_transpose (u : V₁ →ₗ[K] V₂) :
  linear_map.to_matrix B₂.dual_basis B₁.dual_basis (module.dual.transpose u) =
  (linear_map.to_matrix B₁ B₂ u)ᵀ :=
begin
  ext i j,
  simp only [linear_map.to_matrix_apply, module.dual.transpose_apply, B₁.dual_basis_repr,
             B₂.dual_basis_apply, matrix.transpose_apply, linear_map.comp_apply]
end

@[simp] lemma matrix.to_lin_transpose (M : matrix ι₁ ι₂ K) :
  matrix.to_lin B₁.dual_basis B₂.dual_basis Mᵀ =
    module.dual.transpose (matrix.to_lin B₂ B₁ M) :=
begin
  apply (linear_map.to_matrix B₁.dual_basis B₂.dual_basis).injective,
  rw [linear_map.to_matrix_to_lin, linear_map.to_matrix_transpose, linear_map.to_matrix_to_lin]
end

end transpose
namespace matrix

section trace

variables {m : Type*} [fintype m] (n : Type*) [fintype n]
variables (R : Type v) (M : Type w) [semiring R] [add_comm_monoid M] [module R M]

/--
The diagonal of a square matrix.
-/
def diag : (matrix n n M) →ₗ[R] n → M :=
{ to_fun    := λ A i, A i i,
  map_add'  := by { intros, ext, refl, },
  map_smul' := by { intros, ext, refl, } }

variables {n} {R} {M}

@[simp] lemma diag_apply (A : matrix n n M) (i : n) : diag n R M A i = A i i := rfl

@[simp] lemma diag_one [decidable_eq n] :
  diag n R R 1 = λ i, 1 := by { dunfold diag, ext, simp [one_apply_eq] }

@[simp] lemma diag_transpose (A : matrix n n M) : diag n R M Aᵀ = diag n R M A := rfl

variables (n) (R) (M)

/--
The trace of a square matrix.
-/
def trace : (matrix n n M) →ₗ[R] M :=
{ to_fun    := λ A, ∑ i, diag n R M A i,
  map_add'  := by { intros, apply finset.sum_add_distrib, },
  map_smul' := by { intros, simp [finset.smul_sum], } }

variables {n} {R} {M}

@[simp] lemma trace_diag (A : matrix n n M) : trace n R M A = ∑ i, diag n R M A i := rfl

lemma trace_apply (A : matrix n n M) : trace n R M A = ∑ i, A i i := rfl

@[simp] lemma trace_one [decidable_eq n] :
  trace n R R 1 = fintype.card n :=
have h : trace n R R 1 = ∑ i, diag n R R 1 i := rfl,
by simp_rw [h, diag_one, finset.sum_const, nsmul_one]; refl

@[simp] lemma trace_transpose (A : matrix n n M) : trace n R M Aᵀ = trace n R M A := rfl

@[simp] lemma trace_transpose_mul (A : matrix m n R) (B : matrix n m R) :
  trace n R R (Aᵀ ⬝ Bᵀ) = trace m R R (A ⬝ B) := finset.sum_comm

lemma trace_mul_comm {S : Type v} [comm_ring S] (A : matrix m n S) (B : matrix n m S) :
  trace n S S (B ⬝ A) = trace m S S (A ⬝ B) :=
by rw [←trace_transpose, ←trace_transpose_mul, transpose_mul]

end trace

section ring

variables {n : Type*} [fintype n] [decidable_eq n] {R : Type v} [comm_ring R]
open linear_map matrix

lemma proj_diagonal (i : n) (w : n → R) :
  (proj i).comp (to_lin' (diagonal w)) = (w i) • proj i :=
by ext j; simp [mul_vec_diagonal]

lemma diagonal_comp_std_basis (w : n → R) (i : n) :
  (diagonal w).to_lin'.comp (std_basis R (λ_:n, R) i) = (w i) • std_basis R (λ_:n, R) i :=
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

/-- An invertible matrix yields a linear equivalence from the free module to itself.

See `matrix.to_linear_equiv` for the same map on arbitrary modules.
-/
def to_linear_equiv' (P : matrix n n R) (h : is_unit P) : (n → R) ≃ₗ[R] (n → R) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
{ inv_fun   := P⁻¹.to_lin',
  left_inv  := λ v,
    show (P⁻¹.to_lin'.comp P.to_lin') v = v,
    by rw [← matrix.to_lin'_mul, P.nonsing_inv_mul h', matrix.to_lin'_one, linear_map.id_apply],
  right_inv := λ v,
    show (P.to_lin'.comp P⁻¹.to_lin') v = v,
    by rw [← matrix.to_lin'_mul, P.mul_nonsing_inv h', matrix.to_lin'_one, linear_map.id_apply],
  ..P.to_lin' }

@[simp] lemma to_linear_equiv'_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv' h) : module.End R (n → R)) = P.to_lin' := rfl

@[simp] lemma to_linear_equiv'_symm_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv' h).symm : module.End R (n → R)) = P⁻¹.to_lin' := rfl

end ring

section module

variables {m n : Type*} [fintype m] [fintype n]
variables {K : Type u} [field K] -- maybe try to relax the universe constraint

open linear_map matrix

lemma rank_vec_mul_vec {m n : Type u} [fintype m] [fintype n] [decidable_eq n]
  (w : m → K) (v : n → K) :
  rank (vec_mul_vec w v).to_lin' ≤ 1 :=
begin
  rw [vec_mul_vec_eq, to_lin'_mul],
  refine le_trans (rank_comp_le1 _ _) _,
  refine le_trans (rank_le_domain _) _,
  rw [dim_fun', ← cardinal.lift_eq_nat_iff.mpr (cardinal.fintype_card unit), cardinal.mk_unit],
  exact le_of_eq (cardinal.lift_one)
end

lemma ker_diagonal_to_lin' [decidable_eq m] (w : m → K) :
  ker (diagonal w).to_lin' = (⨆i∈{i | w i = 0 }, range (std_basis K (λi, K) i)) :=
begin
  rw [← comap_bot, ← infi_ker_proj],
  simp only [comap_infi, (ker_comp _ _).symm, proj_diagonal, ker_smul'],
  have : univ ⊆ {i : m | w i = 0} ∪ {i : m | w i = 0}ᶜ, { rw set.union_compl_self },
  exact (supr_range_std_basis_eq_infi_ker_proj K (λi:m, K)
    disjoint_compl_right this (finite.of_fintype _)).symm
end

lemma range_diagonal [decidable_eq m] (w : m → K) :
  (diagonal w).to_lin'.range = (⨆ i ∈ {i | w i ≠ 0}, (std_basis K (λi, K) i).range) :=
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

variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]
variables (b : basis n R M)

include b

/-- Given `hA : is_unit A.det` and `b : basis R b`, `A.to_linear_equiv b hA` is
the `linear_equiv` arising from `to_lin b b A`.

See `matrix.to_linear_equiv'` for this result on `n → R`.
-/
@[simps apply]
def to_linear_equiv [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  M ≃ₗ[R] M :=
begin
  refine ⟨to_lin b b A, linear_map.map_add _, linear_map.map_smul _, to_lin b b A⁻¹,
          λ x, _, λ x, _⟩;
  simp only [← linear_map.comp_apply, ← matrix.to_lin_mul b b b,
             matrix.nonsing_inv_mul _ hA, matrix.mul_nonsing_inv _ hA,
             to_lin_one, linear_map.id_apply]
end
lemma ker_to_lin_eq_bot [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  (to_lin b b A).ker = ⊥ :=
ker_eq_bot.mpr (to_linear_equiv b A hA).injective

lemma range_to_lin_eq_top [decidable_eq n] (A : matrix n n R) (hA : is_unit A.det) :
  (to_lin b b A).range = ⊤ :=
range_eq_top.mpr (to_linear_equiv b A hA).surjective

end module

section finite_dimensional

variables {m n : Type*} [fintype m] [fintype n]
variables {R : Type v} [field R]

instance : finite_dimensional R (matrix m n R) :=
linear_equiv.finite_dimensional (linear_equiv.uncurry R m n).symm

/--
The dimension of the space of finite dimensional matrices
is the product of the number of rows and columns.
-/
@[simp] lemma finrank_matrix :
  finite_dimensional.finrank R (matrix m n R) = fintype.card m * fintype.card n :=
by rw [@linear_equiv.finrank_eq R (matrix m n R) _ _ _ _ _ _ (linear_equiv.uncurry R m n),
       finite_dimensional.finrank_fintype_fun_eq_card, fintype.card_prod]

end finite_dimensional

section reindexing

variables {l m n : Type*} [fintype l] [fintype m] [fintype n]
variables {l' m' n' : Type*} [fintype l'] [fintype m'] [fintype n']
variables {R : Type v}

/-- The natural map that reindexes a matrix's rows and columns with equivalent types,
`matrix.reindex`, is a linear equivalence. -/
def reindex_linear_equiv [semiring R] (eₘ : m ≃ m') (eₙ : n ≃ n') :
  matrix m n R ≃ₗ[R] matrix m' n' R :=
{ map_add'  := λ M N, rfl,
  map_smul' := λ M N, rfl,
  ..(reindex eₘ eₙ)}

@[simp] lemma reindex_linear_equiv_apply [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) :
  reindex_linear_equiv eₘ eₙ M = reindex eₘ eₙ M :=
rfl

@[simp] lemma reindex_linear_equiv_symm [semiring R] (eₘ : m ≃ m') (eₙ : n ≃ n') :
  (reindex_linear_equiv eₘ eₙ : _ ≃ₗ[R] _).symm = reindex_linear_equiv eₘ.symm eₙ.symm :=
rfl

@[simp] lemma reindex_linear_equiv_refl_refl [semiring R] :
  reindex_linear_equiv (equiv.refl m) (equiv.refl n) = linear_equiv.refl R _ :=
linear_equiv.ext $ λ _, rfl

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types, `matrix.reindex`, is an equivalence of algebras. -/
def reindex_alg_equiv [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) : matrix m m R ≃ₐ[R] matrix n n R :=
{ to_fun    := reindex e e,
  map_mul'  := λ M N, minor_mul_equiv M N e.symm e.symm e.symm,
  commutes' := λ r, by simp [algebra_map, algebra.to_ring_hom, minor_smul],
  ..(reindex_linear_equiv e e) }

@[simp] lemma reindex_alg_equiv_apply [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix m m R) :
  reindex_alg_equiv e M = reindex e e M :=
rfl

@[simp] lemma reindex_alg_equiv_symm [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) :
  (reindex_alg_equiv e : _ ≃ₐ[R] _).symm = reindex_alg_equiv e.symm :=
rfl

@[simp] lemma reindex_alg_equiv_refl [comm_semiring R] [decidable_eq m] :
  reindex_alg_equiv (equiv.refl m) = (alg_equiv.refl : _ ≃ₐ[R] _) :=
alg_equiv.ext $ λ _, rfl

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`.
-/
lemma det_reindex_linear_equiv_self [decidable_eq m] [decidable_eq n] [comm_ring R]
  (e : m ≃ n) (A : matrix m m R) :
  det (reindex_linear_equiv e e A) = det A :=
det_reindex_self e A

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_minor_equiv_self`.
-/
lemma det_reindex_alg_equiv [decidable_eq m] [decidable_eq n] [comm_ring R]
  (e : m ≃ n) (A : matrix m m R) :
  det (reindex_alg_equiv e A) = det A :=
det_reindex_self e A

end reindexing

end matrix

namespace algebra

section lmul

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra S T] [algebra R T] [is_scalar_tower R S T]
variables {m n : Type*} [fintype m] [decidable_eq m] [fintype n] [decidable_eq n]
variables (b : basis m R S) (c : basis m S T)

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

lemma smul_left_mul_matrix (x) (i j) (k k') :
  left_mul_matrix (b.smul c) x (i, k) (j, k') =
    left_mul_matrix b (left_mul_matrix c x k k') i j :=
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

open_locale matrix

variables (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
variables {ι : Type w} [decidable_eq ι] [fintype ι]
variables {κ : Type*} [decidable_eq κ] [fintype κ]
variables (b : basis ι R M) (c : basis κ R M)

/-- The trace of an endomorphism given a basis. -/
def trace_aux :
  (M →ₗ[R] M) →ₗ[R] R :=
(matrix.trace ι R R).comp $ linear_map.to_matrix b b

-- Can't be `simp` because it would cause a loop.
lemma trace_aux_def (b : basis ι R M) (f : M →ₗ[R] M) :
  trace_aux R b f = matrix.trace ι R R (linear_map.to_matrix b b f) :=
rfl

theorem trace_aux_eq : trace_aux R b = trace_aux R c :=
linear_map.ext $ λ f,
calc  matrix.trace ι R R (linear_map.to_matrix b b f)
    = matrix.trace ι R R (linear_map.to_matrix b b ((linear_map.id.comp f).comp linear_map.id)) :
  by rw [linear_map.id_comp, linear_map.comp_id]
... = matrix.trace ι R R (linear_map.to_matrix c b linear_map.id ⬝
        linear_map.to_matrix c c f ⬝
        linear_map.to_matrix b c linear_map.id) :
  by rw [linear_map.to_matrix_comp _ c, linear_map.to_matrix_comp _ c]
... = matrix.trace κ R R (linear_map.to_matrix c c f ⬝
        linear_map.to_matrix b c linear_map.id ⬝
        linear_map.to_matrix c b linear_map.id) :
  by rw [matrix.mul_assoc, matrix.trace_mul_comm]
... = matrix.trace κ R R (linear_map.to_matrix c c ((f.comp linear_map.id).comp linear_map.id)) :
  by rw [linear_map.to_matrix_comp _ b, linear_map.to_matrix_comp _ c]
... = matrix.trace κ R R (linear_map.to_matrix c c f) :
  by rw [linear_map.comp_id, linear_map.comp_id]

open_locale classical

theorem trace_aux_reindex_range [nontrivial R] : trace_aux R b.reindex_range = trace_aux R b :=
linear_map.ext $ λ f,
begin
  change ∑ i : set.range b, _ = ∑ i : ι, _, simp_rw [matrix.diag_apply], symmetry,
  convert (equiv.of_injective _ b.injective).sum_comp _, ext i,
  exact (linear_map.to_matrix_reindex_range b b f i i).symm
end

variables (R) (M)

/-- Trace of an endomorphism independent of basis. -/
def trace : (M →ₗ[R] M) →ₗ[R] R :=
if H : ∃ (s : set M) (b : basis (s : set M) R M), s.finite
then @trace_aux R _ _ _ _ _ _ (classical.choice H.some_spec.some_spec) H.some_spec.some
else 0

variables (R) {M}

/-- Auxiliary lemma for `trace_eq_matrix_trace`. -/
theorem trace_eq_matrix_trace_of_finite_set {s : set M} (b : basis s R M) (hs : fintype s)
  (f : M →ₗ[R] M) :
  trace R M f = matrix.trace s R R (linear_map.to_matrix b b f) :=
have ∃ (s : set M) (b : basis (s : set M) R M), s.finite,
from ⟨s, b, ⟨hs⟩⟩,
by { rw [trace, dif_pos this, ← trace_aux_def], congr' 1, apply trace_aux_eq }

theorem trace_eq_matrix_trace (f : M →ₗ[R] M) :
  trace R M f = matrix.trace ι R R (linear_map.to_matrix b b f) :=
if hR : nontrivial R
then by haveI := hR;
        rw [trace_eq_matrix_trace_of_finite_set R b.reindex_range (set.fintype_range b),
            ← trace_aux_def, ← trace_aux_def, trace_aux_reindex_range]
else @subsingleton.elim _ (not_nontrivial_iff_subsingleton.mp hR) _ _

theorem trace_mul_comm (f g : M →ₗ[R] M) :
  trace R M (f * g) = trace R M (g * f) :=
if H : ∃ (s : set M) (b : basis (s : set M) R M), s.finite then let ⟨s, b, hs⟩ := H in
by { haveI := classical.choice hs,
     simp_rw [trace_eq_matrix_trace R b, linear_map.to_matrix_mul], apply matrix.trace_mul_comm }
else by rw [trace, dif_neg H, linear_map.zero_apply, linear_map.zero_apply]

section finite_dimensional

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

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def alg_equiv_matrix' {R : Type v} [comm_ring R] {n : Type*} [fintype n] [decidable_eq n] :
  module.End R (n → R) ≃ₐ[R] matrix n n R :=
{ map_mul'  := linear_map.to_matrix'_comp,
  map_add'  := linear_map.to_matrix'.map_add,
  commutes' := λ r, by { change (r • (linear_map.id : module.End R _)).to_matrix' = r • 1,
                         rw ←linear_map.to_matrix'_id, refl, },
  ..linear_map.to_matrix' }

/-- A linear equivalence of two modules induces an equivalence of algebras of their
endomorphisms. -/
def linear_equiv.alg_conj {R : Type v} [comm_ring R] {M₁ M₂ : Type*}
  [add_comm_group M₁] [module R M₁] [add_comm_group M₂] [module R M₂] (e : M₁ ≃ₗ[R] M₂) :
  module.End R M₁ ≃ₐ[R] module.End R M₂ :=
{ map_mul'  := λ f g, by apply e.arrow_congr_comp,
  map_add'  := e.conj.map_add,
  commutes' := λ r, by { change e.conj (r • linear_map.id) = r • linear_map.id,
                         rw [linear_equiv.map_smul, linear_equiv.conj_id], },
  ..e.conj }

/-- A basis of a module induces an equivalence of algebras from the endomorphisms of the module to
square matrices. -/
def alg_equiv_matrix {R : Type v} {M : Type w} {n : Type*} [fintype n]
  [comm_ring R] [add_comm_group M] [module R M] [decidable_eq n] (h : basis n R M) :
  module.End R M ≃ₐ[R] matrix n n R :=
h.equiv_fun.alg_conj.trans alg_equiv_matrix'

section

variables {R : Type v} [semiring R] {n : Type w} [fintype n]

@[simp] lemma matrix.dot_product_std_basis_eq_mul [decidable_eq n] (v : n → R) (c : R) (i : n) :
  matrix.dot_product v (linear_map.std_basis R (λ _, R) i c) = v i * c :=
begin
  rw [matrix.dot_product, finset.sum_eq_single i, linear_map.std_basis_same],
  exact λ _ _ hb, by rw [linear_map.std_basis_ne _ _ _ _ hb, mul_zero],
  exact λ hi, false.elim (hi $ finset.mem_univ _)
end

@[simp] lemma matrix.dot_product_std_basis_one [decidable_eq n] (v : n → R) (i : n) :
  matrix.dot_product v (linear_map.std_basis R (λ _, R) i 1) = v i :=
by rw [matrix.dot_product_std_basis_eq_mul, mul_one]

lemma matrix.dot_product_eq
  (v w : n → R) (h : ∀ u, matrix.dot_product v u = matrix.dot_product w u) : v = w :=
begin
  funext x,
  classical,
  rw [← matrix.dot_product_std_basis_one v x, ← matrix.dot_product_std_basis_one w x, h],
end

lemma matrix.dot_product_eq_iff {v w : n → R} :
  (∀ u, matrix.dot_product v u = matrix.dot_product w u) ↔ v = w :=
⟨λ h, matrix.dot_product_eq v w h, λ h _, h ▸ rfl⟩

lemma matrix.dot_product_eq_zero (v : n → R) (h : ∀ w, matrix.dot_product v w = 0) : v = 0 :=
matrix.dot_product_eq _ _ $ λ u, (h u).symm ▸ (zero_dot_product u).symm

lemma matrix.dot_product_eq_zero_iff {v : n → R} : (∀ w, matrix.dot_product v w = 0) ↔ v = 0 :=
⟨λ h, matrix.dot_product_eq_zero v h, λ h w, h.symm ▸ zero_dot_product w⟩

end

namespace matrix

variables {m n : Type*} [decidable_eq n] [fintype n] [decidable_eq m] [fintype m]
variables {R : Type v} [comm_ring R]

lemma det_to_block (M : matrix m m R) (p : m → Prop) [decidable_pred p] :
  M.det = (matrix.from_blocks (to_block M p p) (to_block M p (λ j, ¬p j))
    (to_block M (λ j, ¬p j) p) (to_block M (λ j, ¬p j) (λ j, ¬p j))).det :=
begin
  rw ← matrix.det_reindex_self (equiv.sum_compl p).symm M,
  rw [det_apply', det_apply'],
  congr, ext σ, congr, ext,
  generalize hy : σ x = y,
  cases x; cases y;
  simp only [matrix.reindex_apply, to_block_apply, equiv.symm_symm,
    equiv.sum_compl_apply_inr, equiv.sum_compl_apply_inl,
    from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂,
    matrix.minor_apply],
end

lemma det_to_square_block (M : matrix m m R) {n : nat} (b : m → fin n) (k : fin n) :
  (to_square_block M b k).det = (to_square_block_prop M (λ i, b i = k)).det :=
by simp

lemma det_to_square_block' (M : matrix m m R) (b : m → ℕ) (k : ℕ) :
  (to_square_block' M b k).det = (to_square_block_prop M (λ i, b i = k)).det :=
by simp

lemma two_block_triangular_det (M : matrix m m R) (p : m → Prop) [decidable_pred p]
  (h : ∀ i (h1 : ¬p i) j (h2 : p j), M i j = 0) :
  M.det = (to_square_block_prop M p).det * (to_square_block_prop M (λ i, ¬p i)).det :=
begin
  rw det_to_block M p,
  convert upper_two_block_triangular_det (to_block M p p) (to_block M p (λ j, ¬p j))
    (to_block M (λ j, ¬p j) (λ j, ¬p j)),
  ext,
  exact h ↑i i.2 ↑j j.2
end

lemma equiv_block_det (M : matrix m m R) {p q : m → Prop} [decidable_pred p] [decidable_pred q]
  (e : ∀x, q x ↔ p x) : (to_square_block_prop M p).det = (to_square_block_prop M q).det :=
by convert matrix.det_reindex_self (equiv.subtype_equiv_right e) (to_square_block_prop M q)

lemma to_square_block_det'' (M : matrix m m R) {n : nat} (b : m → fin n) (k : fin n) :
  (to_square_block M b k).det = (to_square_block' M (λ i, ↑(b i)) ↑k).det :=
begin
  rw [to_square_block_def', to_square_block_def],
  apply equiv_block_det,
  intro x,
  apply (fin.ext_iff _ _).symm
end

/-- Let `b` map rows and columns of a square matrix `M` to `n` blocks. Then
  `block_triangular_matrix' M n b` says the matrix is block triangular. -/
def block_triangular_matrix' {o : Type*} [fintype o] (M : matrix o o R) {n : ℕ}
  (b : o → fin n) : Prop :=
∀ i j, b j < b i → M i j = 0

lemma upper_two_block_triangular' {m n : Type*} [fintype m] [fintype n]
  (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) :
  block_triangular_matrix' (from_blocks A B 0 D) (sum.elim (λ i, (0 : fin 2)) (λ j, 1)) :=
begin
  intros k1 k2 hk12,
  have h0 : ∀ (k : m ⊕ n), sum.elim (λ i, (0 : fin 2)) (λ j, 1) k = 0 → ∃ i, k = sum.inl i,
  { simp },
  have h1 : ∀ (k : m ⊕ n), sum.elim (λ i, (0 : fin 2)) (λ j, 1) k = 1 → ∃ j, k = sum.inr j,
  { simp },
  set mk1 := (sum.elim (λ i, (0 : fin 2)) (λ j, 1)) k1 with hmk1,
  set mk2 := (sum.elim (λ i, (0 : fin 2)) (λ j, 1)) k2 with hmk2,
  fin_cases mk1; fin_cases mk2; rw [h, h_1] at hk12,
  { exact absurd hk12 (nat.not_lt_zero 0) },
  { exact absurd hk12 (by norm_num) },
  { rw hmk1 at h,
    obtain ⟨i, hi⟩ := h1 k1 h,
    rw hmk2 at h_1,
    obtain ⟨j, hj⟩ := h0 k2 h_1,
    rw [hi, hj], simp },
  { exact absurd hk12 (irrefl 1) }
end

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `ℕ`s. Then
  `block_triangular_matrix M n b` says the matrix is block triangular. -/
def block_triangular_matrix {o : Type*} [fintype o] (M : matrix o o R) (b : o → ℕ) : Prop :=
∀ i j, b j < b i → M i j = 0

lemma upper_two_block_triangular {m n : Type*} [fintype m] [fintype n]
  (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) :
  block_triangular_matrix (from_blocks A B 0 D) (sum.elim (λ i, 0) (λ j, 1)) :=
begin
  intros k1 k2 hk12,
  have h01 : ∀ (k : m ⊕ n), sum.elim (λ i, 0) (λ j, 1) k = 0 ∨ sum.elim (λ i, 0) (λ j, 1) k = 1,
  { simp },
  have h0 : ∀ (k : m ⊕ n), sum.elim (λ i, 0) (λ j, 1) k = 0 → ∃ i, k = sum.inl i, { simp },
  have h1 : ∀ (k : m ⊕ n), sum.elim (λ i, 0) (λ j, 1) k = 1 → ∃ j, k = sum.inr j, { simp },
  cases (h01 k1) with hk1 hk1; cases (h01 k2) with hk2 hk2; rw [hk1, hk2] at hk12,
  { exact absurd hk12 (nat.not_lt_zero 0) },
  { exact absurd hk12 (nat.not_lt_zero 1) },
  { obtain ⟨i, hi⟩ := h1 k1 hk1,
    obtain ⟨j, hj⟩ := h0 k2 hk2,
    rw [hi, hj], simp },
  { exact absurd hk12 (irrefl 1) }
end

lemma det_of_block_triangular_matrix (M : matrix m m R) (b : m → ℕ)
  (h : block_triangular_matrix M b) :
  ∀ (n : ℕ) (hn : ∀ i, b i < n), M.det = ∏ k in finset.range n, (to_square_block' M b k).det :=
begin
  intros n hn,
  tactic.unfreeze_local_instances,
  induction n with n hi generalizing m M b,
  { rw finset.prod_range_zero,
    apply det_eq_one_of_card_eq_zero,
    apply fintype.card_eq_zero_iff.mpr,
    intro i,
    exact nat.not_lt_zero (b i) (hn i) },
  { rw [finset.prod_range_succ_comm],
    have h2 : (M.to_square_block_prop (λ (i : m), b i = n.succ)).det =
      (M.to_square_block' b n.succ).det,
    { dunfold to_square_block', dunfold to_square_block_prop, refl },
    rw two_block_triangular_det M (λ i, ¬(b i = n)),
    { rw mul_comm,
      apply congr (congr_arg has_mul.mul _),
      { let m' := {a // ¬b a = n },
        let b' := (λ (i : m'), b ↑i),
        have h' :
          block_triangular_matrix (M.to_square_block_prop (λ (i : m), ¬b i = n)) b',
        { intros i j, apply h ↑i ↑j },
        have hni : ∀ (i : {a // ¬b a = n}), b' i < n,
        { exact λ i, (ne.le_iff_lt i.property).mp (nat.lt_succ_iff.mp (hn ↑i)) },
        have h1 := hi (M.to_square_block_prop (λ (i : m), ¬b i = n)) b' h' hni,
        rw ←fin.prod_univ_eq_prod_range at h1 ⊢,
        convert h1,
        ext k,
        simp only [to_square_block_def', to_square_block_def],
        let he : {a // b' a = ↑k} ≃ {a // b a = ↑k},
        { have hc : ∀ (i : m), (λ a, b a = ↑k) i → (λ a, ¬b a = n) i,
          { intros i hbi, rw hbi, exact ne_of_lt (fin.is_lt k) },
          exact equiv.subtype_subtype_equiv_subtype hc },
        exact matrix.det_reindex_self he (λ (i j : {a // b' a = ↑k}), M ↑i ↑j) },
      { rw det_to_square_block' M b n,
        have hh : ∀ a, b a = n ↔ ¬(λ (i : m), ¬b i = n) a,
        { intro i, simp only [not_not] },
        exact equiv_block_det M hh }},
    { intros i hi j hj,
      apply (h i), simp only [not_not] at hi,
      rw hi,
      exact (ne.le_iff_lt hj).mp (nat.lt_succ_iff.mp (hn j)) }}
end

lemma det_of_block_triangular_matrix'' (M : matrix m m R) (b : m → ℕ)
  (h : block_triangular_matrix M b) :
  M.det = ∏ k in finset.image b finset.univ, (to_square_block' M b k).det :=
begin
  let n : ℕ := (Sup (finset.image b finset.univ : set ℕ)).succ,
  have hn : ∀ i, b i < n,
  { have hbi : ∀ i, b i ∈ finset.image b finset.univ, { simp },
    intro i,
    dsimp only [n],
    apply nat.lt_succ_iff.mpr,
    exact le_cSup (finset.bdd_above _) (hbi i) },
  rw det_of_block_triangular_matrix M b h n hn,
  refine (finset.prod_subset _ _).symm,
  { intros a ha, apply finset.mem_range.mpr,
    obtain ⟨i, ⟨hi, hbi⟩⟩ := finset.mem_image.mp ha,
    rw ←hbi,
    exact hn i },
  { intros k hk hbk,
    apply det_eq_one_of_card_eq_zero,
    apply fintype.card_eq_zero_iff.mpr,
    simp only [subtype.forall],
    intros a hba, apply hbk,
    apply finset.mem_image.mpr,
    use a,
    exact ⟨finset.mem_univ a, hba⟩ }
end

lemma det_of_block_triangular_matrix' (M : matrix m m R) {n : ℕ} (b : m → fin n)
  (h : block_triangular_matrix' M b) :
  M.det = ∏ (k : fin n), (to_square_block M b k).det :=
begin
  let b2 : m → ℕ := λ i, ↑(b i),
  simp_rw to_square_block_det'',
  rw fin.prod_univ_eq_prod_range (λ (k : ℕ), (M.to_square_block' b2 k).det) n,
  apply det_of_block_triangular_matrix,
  { intros i j hij, exact h i j (fin.coe_fin_lt.mp hij) },
  { intro i, exact fin.is_lt (b i) }
end

lemma det_of_upper_triangular {n : ℕ} (M : matrix (fin n) (fin n) R)
  (h : ∀ (i j : fin n), j < i → M i j = 0) :
  M.det = ∏ i : (fin n), M i i :=
begin
  convert det_of_block_triangular_matrix' M id h,
  ext i,
  have h2 : ∀ (j : {a // id a = i}), j = ⟨i, rfl⟩ :=
    λ (j : {a // id a = i}), subtype.ext j.property,
  haveI : unique {a // id a = i} := ⟨⟨⟨i, rfl⟩⟩, h2⟩,
  simp [h2 (default {a // id a = i})]
end

lemma det_of_lower_triangular {n : ℕ} (M : matrix (fin n) (fin n) R)
  (h : ∀ (i j : fin n), i < j → M i j = 0) :
  M.det = ∏ i : (fin n), M i i :=
begin
  rw ← det_transpose,
  exact det_of_upper_triangular _ (λ (i j : fin n) (hji : j < i), h j i hji)
end

end matrix
