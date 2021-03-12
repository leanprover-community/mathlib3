/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Patrick Massot, Casper Putz
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
 * `is_basis.to_matrix`: the matrix whose columns are a given family of vectors in a given basis
 * `is_basis.to_matrix_equiv`: given a basis, the linear equivalence between families of vectors
   and matrices arising from `is_basis.to_matrix`
 * `is_basis.det`: the determinant of a family of vectors with respect to a basis, as a multilinear
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
    apply (pi.is_basis_fun R n).ext,
    intro j, ext i,
    simp only [matrix.mul_vec_std_basis, matrix.mul_vec_lin_apply]
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
variables {v₁ : n → M₁} (hv₁ : is_basis R v₁) {v₂ : m → M₂} (hv₂ : is_basis R v₂)

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def linear_map.to_matrix : (M₁ →ₗ[R] M₂) ≃ₗ[R] matrix m n R :=
linear_equiv.trans (linear_equiv.arrow_congr hv₁.equiv_fun hv₂.equiv_fun) linear_map.to_matrix'

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between matrices over `R` indexed by the bases and linear maps `M₁ →ₗ M₂`. -/
def matrix.to_lin : matrix m n R ≃ₗ[R] (M₁ →ₗ[R] M₂) :=
(linear_map.to_matrix hv₁ hv₂).symm

@[simp] lemma linear_map.to_matrix_symm :
  (linear_map.to_matrix hv₁ hv₂).symm = matrix.to_lin hv₁ hv₂ :=
rfl

@[simp] lemma matrix.to_lin_symm :
  (matrix.to_lin hv₁ hv₂).symm = linear_map.to_matrix hv₁ hv₂ :=
rfl

@[simp] lemma matrix.to_lin_to_matrix (f : M₁ →ₗ[R] M₂) :
  matrix.to_lin hv₁ hv₂ (linear_map.to_matrix hv₁ hv₂ f) = f :=
by rw [← matrix.to_lin_symm, linear_equiv.apply_symm_apply]

@[simp] lemma linear_map.to_matrix_to_lin (M : matrix m n R) :
  linear_map.to_matrix hv₁ hv₂ (matrix.to_lin hv₁ hv₂ M) = M :=
by rw [← matrix.to_lin_symm, linear_equiv.symm_apply_apply]

lemma linear_map.to_matrix_apply (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
  linear_map.to_matrix hv₁ hv₂ f i j = hv₂.equiv_fun (f (v₁ j)) i :=
begin
  rw [linear_map.to_matrix, linear_equiv.trans_apply, linear_map.to_matrix'_apply,
      linear_equiv.arrow_congr_apply, is_basis.equiv_fun_symm_apply, finset.sum_eq_single j,
      if_pos rfl, one_smul],
  { intros j' _ hj',
    rw [if_neg hj', zero_smul] },
  { intro hj,
    have := finset.mem_univ j,
    contradiction }
end

lemma linear_map.to_matrix_transpose_apply (f : M₁ →ₗ[R] M₂) (j : n) :
  (linear_map.to_matrix hv₁ hv₂ f)ᵀ j = hv₂.equiv_fun (f (v₁ j)) :=
funext $ λ i, f.to_matrix_apply _ _ i j

lemma linear_map.to_matrix_apply' (f : M₁ →ₗ[R] M₂) (i : m) (j : n) :
  linear_map.to_matrix hv₁ hv₂ f i j = hv₂.repr (f (v₁ j)) i :=
linear_map.to_matrix_apply hv₁ hv₂ f i j

lemma linear_map.to_matrix_transpose_apply' (f : M₁ →ₗ[R] M₂) (j : n) :
  (linear_map.to_matrix hv₁ hv₂ f)ᵀ j = hv₂.repr (f (v₁ j)) :=
linear_map.to_matrix_transpose_apply hv₁ hv₂ f j

lemma matrix.to_lin_apply (M : matrix m n R) (v : M₁) :
  matrix.to_lin hv₁ hv₂ M v = ∑ j, M.mul_vec (hv₁.equiv_fun v) j • v₂ j :=
show hv₂.equiv_fun.symm (matrix.to_lin' M (hv₁.equiv_fun v)) = _,
by rw [matrix.to_lin'_apply, hv₂.equiv_fun_symm_apply]

@[simp] lemma matrix.to_lin_self (M : matrix m n R) (i : n) :
  matrix.to_lin hv₁ hv₂ M (v₁ i) = ∑ j, M j i • v₂ j :=
by simp only [matrix.to_lin_apply, matrix.mul_vec, dot_product, hv₁.equiv_fun_self, mul_boole,
  finset.sum_ite_eq, finset.mem_univ, if_true]

/-- This will be a special case of `linear_map.to_matrix_id_eq_basis_to_matrix`. -/
lemma linear_map.to_matrix_id : linear_map.to_matrix hv₁ hv₁ id = 1 :=
begin
  ext i j,
  simp [linear_map.to_matrix_apply, is_basis.equiv_fun, matrix.one_apply, finsupp.single, eq_comm]
end

lemma linear_map.to_matrix_one : linear_map.to_matrix hv₁ hv₁ 1 = 1 :=
linear_map.to_matrix_id hv₁

@[simp]
lemma matrix.to_lin_one : matrix.to_lin hv₁ hv₁ 1 = id :=
by rw [← linear_map.to_matrix_id hv₁, matrix.to_lin_to_matrix]

theorem linear_map.to_matrix_range [decidable_eq M₁] [decidable_eq M₂]
  (f : M₁ →ₗ[R] M₂) (k : m) (i : n) :
  linear_map.to_matrix hv₁.range hv₂.range f ⟨v₂ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_map.to_matrix hv₁ hv₂ f k i :=
by simp_rw [linear_map.to_matrix_apply, subtype.coe_mk, is_basis.equiv_fun_apply, hv₂.range_repr]

variables {M₃ : Type*} [add_comm_group M₃] [module R M₃] {v₃ : l → M₃} (hv₃ : is_basis R v₃)

lemma linear_map.to_matrix_comp [decidable_eq m] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
  linear_map.to_matrix hv₁ hv₃ (f.comp g) =
  linear_map.to_matrix hv₂ hv₃ f ⬝ linear_map.to_matrix hv₁ hv₂ g :=
by simp_rw [linear_map.to_matrix, linear_equiv.trans_apply,
            linear_equiv.arrow_congr_comp _ hv₂.equiv_fun, linear_map.to_matrix'_comp]

lemma linear_map.to_matrix_mul (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix hv₁ hv₁ (f * g) =
    linear_map.to_matrix hv₁ hv₁ f ⬝ linear_map.to_matrix hv₁ hv₁ g :=
by { rw [show (@has_mul.mul (M₁ →ₗ[R] M₁) _) = linear_map.comp, from rfl,
         linear_map.to_matrix_comp hv₁ hv₁ hv₁ f g] }

lemma matrix.to_lin_mul [decidable_eq m] (A : matrix l m R) (B : matrix m n R) :
  matrix.to_lin hv₁ hv₃ (A ⬝ B) =
  (matrix.to_lin hv₂ hv₃ A).comp (matrix.to_lin hv₁ hv₂ B) :=
begin
  apply (linear_map.to_matrix hv₁ hv₃).injective,
  haveI : decidable_eq l := λ _ _, classical.prop_decidable _,
  rw linear_map.to_matrix_comp hv₁ hv₂ hv₃,
  repeat { rw linear_map.to_matrix_to_lin },
end

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between linear maps `M₁ →ₗ M₁` and square matrices over `R` indexed by the basis. -/
def linear_map.to_matrix_alg_equiv :
  (M₁ →ₗ[R] M₁) ≃ₐ[R] matrix n n R :=
alg_equiv.of_linear_equiv (linear_map.to_matrix hv₁ hv₁) (linear_map.to_matrix_mul hv₁)
  (by simp [module.algebra_map_End_eq_smul_id, linear_map.to_matrix_id])

/-- Given a basis of a module `M₁` over a commutative ring `R`, we get an algebra
equivalence between square matrices over `R` indexed by the basis and linear maps `M₁ →ₗ M₁`. -/
def matrix.to_lin_alg_equiv : matrix n n R ≃ₐ[R] (M₁ →ₗ[R] M₁) :=
(linear_map.to_matrix_alg_equiv hv₁).symm

@[simp] lemma linear_map.to_matrix_alg_equiv_symm :
  (linear_map.to_matrix_alg_equiv hv₁).symm = matrix.to_lin_alg_equiv hv₁ :=
rfl

@[simp] lemma matrix.to_lin_alg_equiv_symm :
  (matrix.to_lin_alg_equiv hv₁).symm = linear_map.to_matrix_alg_equiv hv₁ :=
rfl

@[simp] lemma matrix.to_lin_alg_equiv_to_matrix_alg_equiv (f : M₁ →ₗ[R] M₁) :
  matrix.to_lin_alg_equiv hv₁ (linear_map.to_matrix_alg_equiv hv₁ f) = f :=
by rw [← matrix.to_lin_alg_equiv_symm, alg_equiv.apply_symm_apply]

@[simp] lemma linear_map.to_matrix_alg_equiv_to_lin_alg_equiv (M : matrix n n R) :
  linear_map.to_matrix_alg_equiv hv₁ (matrix.to_lin_alg_equiv hv₁ M) = M :=
by rw [← matrix.to_lin_alg_equiv_symm, alg_equiv.symm_apply_apply]

lemma linear_map.to_matrix_alg_equiv_apply (f : M₁ →ₗ[R] M₁) (i j : n) :
  linear_map.to_matrix_alg_equiv hv₁ f i j = hv₁.equiv_fun (f (v₁ j)) i :=
by simp [linear_map.to_matrix_alg_equiv, linear_map.to_matrix_apply]

lemma linear_map.to_matrix_alg_equiv_transpose_apply (f : M₁ →ₗ[R] M₁) (j : n) :
  (linear_map.to_matrix_alg_equiv hv₁ f)ᵀ j = hv₁.equiv_fun (f (v₁ j)) :=
funext $ λ i, f.to_matrix_apply _ _ i j

lemma linear_map.to_matrix_alg_equiv_apply' (f : M₁ →ₗ[R] M₁) (i j : n) :
  linear_map.to_matrix_alg_equiv hv₁ f i j = hv₁.repr (f (v₁ j)) i :=
linear_map.to_matrix_alg_equiv_apply hv₁ f i j

lemma linear_map.to_matrix_alg_equiv_transpose_apply' (f : M₁ →ₗ[R] M₁) (j : n) :
  (linear_map.to_matrix_alg_equiv hv₁ f)ᵀ j = hv₁.repr (f (v₁ j)) :=
linear_map.to_matrix_alg_equiv_transpose_apply hv₁ f j

lemma matrix.to_lin_alg_equiv_apply (M : matrix n n R) (v : M₁) :
  matrix.to_lin_alg_equiv hv₁ M v = ∑ j, M.mul_vec (hv₁.equiv_fun v) j • v₁ j :=
show hv₁.equiv_fun.symm (matrix.to_lin_alg_equiv' M (hv₁.equiv_fun v)) = _,
by rw [matrix.to_lin_alg_equiv'_apply, hv₁.equiv_fun_symm_apply]

@[simp] lemma matrix.to_lin_alg_equiv_self (M : matrix n n R) (i : n) :
  matrix.to_lin_alg_equiv hv₁ M (v₁ i) = ∑ j, M j i • v₁ j :=
by simp only [matrix.to_lin_alg_equiv_apply, matrix.mul_vec, dot_product, hv₁.equiv_fun_self,
  mul_boole, finset.sum_ite_eq, finset.mem_univ, if_true]

lemma linear_map.to_matrix_alg_equiv_id : linear_map.to_matrix_alg_equiv hv₁ id = 1 :=
by simp_rw [linear_map.to_matrix_alg_equiv, alg_equiv.of_linear_equiv_apply,
            linear_map.to_matrix_id]

@[simp]
lemma matrix.to_lin_alg_equiv_one : matrix.to_lin_alg_equiv hv₁ 1 = id :=
by rw [← linear_map.to_matrix_alg_equiv_id hv₁, matrix.to_lin_alg_equiv_to_matrix_alg_equiv]

theorem linear_map.to_matrix_alg_equiv_range [decidable_eq M₁]
  (f : M₁ →ₗ[R] M₁) (k i : n) :
  linear_map.to_matrix_alg_equiv hv₁.range f ⟨v₁ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_map.to_matrix_alg_equiv hv₁ f k i :=
by simp_rw [linear_map.to_matrix_alg_equiv_apply, subtype.coe_mk, is_basis.equiv_fun_apply,
            hv₁.range_repr]

lemma linear_map.to_matrix_alg_equiv_comp (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix_alg_equiv hv₁ (f.comp g) =
  linear_map.to_matrix_alg_equiv hv₁ f ⬝ linear_map.to_matrix_alg_equiv hv₁ g :=
by simp [linear_map.to_matrix_alg_equiv, linear_map.to_matrix_comp hv₁ hv₁ hv₁ f g]

lemma linear_map.to_matrix_alg_equiv_mul (f g : M₁ →ₗ[R] M₁) :
  linear_map.to_matrix_alg_equiv hv₁ (f * g) =
    linear_map.to_matrix_alg_equiv hv₁ f ⬝ linear_map.to_matrix_alg_equiv hv₁ g :=
by { rw [show (@has_mul.mul (M₁ →ₗ[R] M₁) _) = linear_map.comp, from rfl,
         linear_map.to_matrix_alg_equiv_comp hv₁ f g] }

lemma matrix.to_lin_alg_equiv_mul (A B : matrix n n R) :
  matrix.to_lin_alg_equiv hv₁ (A ⬝ B) =
  (matrix.to_lin_alg_equiv hv₁ A).comp (matrix.to_lin_alg_equiv hv₁ B) :=
by convert matrix.to_lin_mul hv₁ hv₁ hv₁ A B

end to_matrix

section is_basis_to_matrix

variables {ι ι' κ κ' : Type*} [fintype ι] [fintype ι'] [fintype κ] [fintype κ']
variables {R M : Type*} [comm_ring R] [add_comm_group M] [module R M]

open function matrix

/-- From a basis `e : ι → M` and a family of vectors `v : ι' → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def is_basis.to_matrix {e : ι → M} (he : is_basis R e) (v : ι' → M) : matrix ι ι' R :=
λ i j, he.equiv_fun (v j) i

variables {e : ι → M} (he : is_basis R e) (v : ι' → M) (i : ι) (j : ι')

namespace is_basis

lemma to_matrix_apply : he.to_matrix v i j = he.equiv_fun (v j) i :=
rfl

lemma to_matrix_transpose_apply : (he.to_matrix v)ᵀ j = he.repr (v j) :=
funext $ (λ _, rfl)

lemma to_matrix_eq_to_matrix_constr [decidable_eq ι] (v : ι → M) :
  he.to_matrix v = linear_map.to_matrix he he (he.constr v) :=
by { ext, simp [is_basis.to_matrix_apply, linear_map.to_matrix_apply] }

@[simp] lemma to_matrix_self [decidable_eq ι] : he.to_matrix e = 1 :=
begin
  rw is_basis.to_matrix,
  ext i j,
  simp [is_basis.equiv_fun, matrix.one_apply, finsupp.single, eq_comm]
end

lemma to_matrix_update [decidable_eq ι'] (x : M) :
  he.to_matrix (function.update v j x) = matrix.update_column (he.to_matrix v) j (he.repr x) :=
begin
  ext i' k,
  rw [is_basis.to_matrix, matrix.update_column_apply, he.to_matrix_apply],
  split_ifs,
  { rw [h, update_same j x v, he.equiv_fun_apply] },
  { rw update_noteq h },
end

@[simp] lemma sum_to_matrix_smul_self : ∑ (i : ι), he.to_matrix v i j • e i = v j :=
begin
  conv_rhs { rw ← he.total_repr (v j) },
  rw [finsupp.total_apply, finsupp.sum_fintype],
  { refl },
  simp
end

@[simp] lemma to_lin_to_matrix [decidable_eq ι'] (hv : is_basis R v) :
  matrix.to_lin hv he (he.to_matrix v) = id :=
hv.ext (λ i, by rw [to_lin_self, id_apply, he.sum_to_matrix_smul_self])

/-- From a basis `e : ι → M`, build a linear equivalence between families of vectors `v : ι → M`,
and matrices, making the matrix whose columns are the vectors `v i` written in the basis `e`. -/
def to_matrix_equiv {e : ι → M} (he : is_basis R e) : (ι → M) ≃ₗ[R] matrix ι ι R :=
{ to_fun := he.to_matrix,
  map_add' := λ v w, begin
    ext i j,
    change _ = _ + _,
    simp [he.to_matrix_apply]
  end,
  map_smul' := begin
    intros c v,
    ext i j,
    simp [he.to_matrix_apply]
  end,
  inv_fun := λ m j, ∑ i, (m i j) • e i,
  left_inv := begin
    intro v,
    ext j,
    simp [he.to_matrix_apply, he.equiv_fun_total (v j)]
  end,
  right_inv := begin
    intros x,
    ext k l,
    simp [he.to_matrix_apply, he.equiv_fun.map_sum, he.equiv_fun.map_smul,
          fintype.sum_apply k (λ i, x i l • he.equiv_fun (e i)),
          he.equiv_fun_self]
  end }

end is_basis

section mul_linear_map_to_matrix

variables {N : Type*} [add_comm_group N] [module R N]
variables {b : ι → M} {b' : ι' → M} {c : κ → N} {c' : κ' → N}
variables (hb : is_basis R b) (hb' : is_basis R b') (hc : is_basis R c) (hc' : is_basis R c')
variables (f : M →ₗ[R] N)

open linear_map

@[simp] lemma is_basis_to_matrix_mul_linear_map_to_matrix [decidable_eq ι'] :
  hc.to_matrix c' ⬝ linear_map.to_matrix hb' hc' f = linear_map.to_matrix hb' hc f :=
(matrix.to_lin hb' hc).injective
  (by haveI := classical.dec_eq κ';
      rw [to_lin_to_matrix, to_lin_mul hb' hc' hc, to_lin_to_matrix, hc.to_lin_to_matrix, id_comp])

@[simp] lemma linear_map_to_matrix_mul_is_basis_to_matrix [decidable_eq ι] [decidable_eq ι'] :
  linear_map.to_matrix hb' hc' f ⬝ hb'.to_matrix b = linear_map.to_matrix hb hc' f :=
(matrix.to_lin hb hc').injective
  (by rw [to_lin_to_matrix, to_lin_mul hb hb' hc', to_lin_to_matrix, hb'.to_lin_to_matrix, comp_id])

/-- A generalization of `linear_map.to_matrix_id`. -/
@[simp] lemma linear_map.to_matrix_id_eq_basis_to_matrix [decidable_eq ι] :
  linear_map.to_matrix hb hb' id = hb'.to_matrix b :=
by { haveI := classical.dec_eq ι',
      rw [← is_basis_to_matrix_mul_linear_map_to_matrix hb hb', to_matrix_id, matrix.mul_one] }

/-- A generalization of `is_basis.to_matrix_self`, in the opposite direction. -/
@[simp] lemma is_basis.to_matrix_mul_to_matrix
  {ι'' : Type*} [fintype ι''] {b'' : ι'' → M} (hb'' : is_basis R b'') :
  hb.to_matrix b' ⬝ hb'.to_matrix b'' = hb.to_matrix b'' :=
begin
  haveI := classical.dec_eq ι,
  haveI := classical.dec_eq ι',
  haveI := classical.dec_eq ι'',
  rw [← linear_map.to_matrix_id_eq_basis_to_matrix hb' hb,
      ← linear_map.to_matrix_id_eq_basis_to_matrix hb'' hb',
      ← to_matrix_comp, id_comp, linear_map.to_matrix_id_eq_basis_to_matrix],
end

end mul_linear_map_to_matrix

end is_basis_to_matrix

open_locale matrix

section det

open linear_map matrix

variables {R : Type*} [comm_ring R]
variables {M : Type*} [add_comm_group M] [module R M]
variables {M' : Type*} [add_comm_group M'] [module R M']
variables {ι : Type*} [decidable_eq ι] [fintype ι] {v : ι → M} {v' : ι → M'}

lemma linear_equiv.is_unit_det (f : M ≃ₗ[R] M') (hv : is_basis R v) (hv' : is_basis R v') :
  is_unit (linear_map.to_matrix hv hv' f).det :=
begin
  apply is_unit_det_of_left_inverse,
  simpa using (linear_map.to_matrix_comp hv hv' hv f.symm f).symm
end

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
def linear_equiv.of_is_unit_det {f : M →ₗ[R] M'} {hv : is_basis R v} {hv' : is_basis R v'}
  (h : is_unit (linear_map.to_matrix hv hv' f).det) : M ≃ₗ[R] M' :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := f.map_smul,
  inv_fun := to_lin hv' hv (to_matrix hv hv' f)⁻¹,
  left_inv := λ x,
    calc to_lin hv' hv (to_matrix hv hv' f)⁻¹ (f x)
        = to_lin hv hv ((to_matrix hv hv' f)⁻¹ ⬝ to_matrix hv hv' f) x :
      by { rw [to_lin_mul hv hv' hv, to_lin_to_matrix, linear_map.comp_apply] }
    ... = x : by simp [h],
  right_inv := λ x,
    calc f (to_lin hv' hv (to_matrix hv hv' f)⁻¹ x)
        = to_lin hv' hv' (to_matrix hv hv' f ⬝ (to_matrix hv hv' f)⁻¹) x :
      by { rw [to_lin_mul hv' hv hv', linear_map.comp_apply, to_lin_to_matrix hv hv'] }
    ... = x : by simp [h],
  }

variables {e : ι → M} (he : is_basis R e)

/-- The determinant of a family of vectors with respect to some basis, as an alternating
multilinear map. -/
def is_basis.det : alternating_map R M R ι :=
{ to_fun := λ v, det (he.to_matrix v),
  map_add' := begin
    intros v i x y,
    simp only [he.to_matrix_update, linear_map.map_add],
    apply det_update_column_add
  end,
  map_smul' := begin
    intros u i c x,
    simp only [he.to_matrix_update, algebra.id.smul_eq_mul, map_smul_of_tower],
    apply det_update_column_smul
  end,
  map_eq_zero_of_eq' := begin
    intros v i j h hij,
    rw [←function.update_eq_self i v, h, ←det_transpose, he.to_matrix_update,
        ←update_row_transpose, ←he.to_matrix_transpose_apply],
    apply det_zero_of_row_eq hij,
    rw [update_row_ne hij.symm, update_row_self],
  end }

lemma is_basis.det_apply (v : ι → M) : he.det v = det (he.to_matrix v) := rfl

lemma is_basis.det_self : he.det e = 1 :=
by simp [he.det_apply]

lemma is_basis.iff_det {v : ι → M} : is_basis R v ↔ is_unit (he.det v) :=
begin
  split,
  { intro hv,
    suffices :
      is_unit (linear_map.to_matrix he he (linear_equiv_of_is_basis he hv $ equiv.refl ι)).det,
    { rw [is_basis.det_apply, is_basis.to_matrix_eq_to_matrix_constr],
      exact this },
    apply linear_equiv.is_unit_det },
  { intro h,
    rw [is_basis.det_apply, is_basis.to_matrix_eq_to_matrix_constr] at h,
    convert linear_equiv.is_basis he (linear_equiv.of_is_unit_det h),
    ext i,
    exact (constr_basis he).symm },
end

end det

section transpose

variables {K V₁ V₂ ι₁ ι₂ : Type*} [field K]
          [add_comm_group V₁] [vector_space K V₁]
          [add_comm_group V₂] [vector_space K V₂]
          [fintype ι₁] [fintype ι₂] [decidable_eq ι₁] [decidable_eq ι₂]
          {B₁ : ι₁ → V₁} (h₁ : is_basis K B₁)
          {B₂ : ι₂ → V₂} (h₂ : is_basis K B₂)

@[simp] lemma linear_map.to_matrix_transpose (u : V₁ →ₗ[K] V₂) :
  linear_map.to_matrix h₂.dual_basis_is_basis h₁.dual_basis_is_basis (module.dual.transpose u) =
  (linear_map.to_matrix h₁ h₂ u)ᵀ :=
begin
  ext i j,
  simp only [linear_map.to_matrix_apply, module.dual.transpose_apply, h₁.dual_basis_equiv_fun,
             h₂.dual_basis_apply, matrix.transpose_apply, linear_map.comp_apply]
end

lemma linear_map.to_matrix_symm_transpose (M : matrix ι₁ ι₂ K) :
  (linear_map.to_matrix h₁.dual_basis_is_basis h₂.dual_basis_is_basis).symm Mᵀ =
  module.dual.transpose (matrix.to_lin h₂ h₁ M) :=
begin
  apply (linear_map.to_matrix h₁.dual_basis_is_basis h₂.dual_basis_is_basis).injective,
  rw [linear_equiv.apply_symm_apply],
  ext i j,
  simp only [linear_map.to_matrix_apply, module.dual.transpose_apply, h₂.dual_basis_equiv_fun,
    h₁.dual_basis_apply, matrix.transpose_apply, linear_map.comp_apply, if_true,
    matrix.to_lin_apply, linear_equiv.map_smul, mul_boole, algebra.id.smul_eq_mul,
    linear_equiv.map_sum, is_basis.equiv_fun_self, fintype.sum_apply, finset.sum_ite_eq',
    finset.sum_ite_eq, is_basis.equiv_fun_symm_apply, pi.smul_apply, matrix.to_lin_apply,
    matrix.mul_vec, matrix.dot_product, is_basis.equiv_fun_self, finset.mem_univ]
end

end transpose
namespace matrix

section trace

variables {m : Type*} [fintype m] (n : Type*) [fintype n]
variables (R : Type v) (M : Type w) [semiring R] [add_comm_monoid M] [semimodule R M]

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

/-- An invertible matrix yields a linear equivalence from the free module to itself. -/
def to_linear_equiv (P : matrix n n R) (h : is_unit P) : (n → R) ≃ₗ[R] (n → R) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
{ inv_fun   := P⁻¹.to_lin',
  left_inv  := λ v,
    show (P⁻¹.to_lin'.comp P.to_lin') v = v,
    by rw [← matrix.to_lin'_mul, P.nonsing_inv_mul h', matrix.to_lin'_one, linear_map.id_apply],
  right_inv := λ v,
    show (P.to_lin'.comp P⁻¹.to_lin') v = v,
    by rw [← matrix.to_lin'_mul, P.mul_nonsing_inv h', matrix.to_lin'_one, linear_map.id_apply],
  ..P.to_lin' }

@[simp] lemma to_linear_equiv_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv h) : module.End R (n → R)) = P.to_lin' := rfl

@[simp] lemma to_linear_equiv_symm_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv h).symm : module.End R (n → R)) = P⁻¹.to_lin' := rfl

end ring

section vector_space

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
  have h₁ := supr_range_std_basis_eq_infi_ker_proj K (λi:m, K) hd hu (finite.of_fintype _),
  have h₂ := @infi_ker_proj_equiv K _ _ (λi:m, K) _ _ _ _ (by simp; apply_instance) hd hu,
  rw [rank, range_diagonal, h₁, ←@dim_fun' K],
  apply linear_equiv.dim_eq,
  apply h₂,
end

variables {V : Type*} [add_comm_group V] [vector_space K V]
variables {v₁ : n → V} (hv₁ : is_basis K v₁)

lemma ker_to_lin_eq_bot [decidable_eq n] (M : matrix n n K) (hM : M.det ≠ 0) :
  (to_lin hv₁ hv₁ M).ker = ⊥ :=
begin
  rw submodule.eq_bot_iff,
  intros x hx,
  calc x = to_lin hv₁ hv₁ (M⁻¹ ⬝ M) x : by simp [nonsing_inv_mul M (is_unit.mk0 _ hM)]
     ... = to_lin hv₁ hv₁ M⁻¹ (to_lin hv₁ hv₁ M x) : by simp [to_lin_mul hv₁ hv₁ hv₁]
     ... = (to_lin hv₁ hv₁ M⁻¹) 0 : by rw mem_ker.mp hx
     ... = 0 : linear_map.map_zero _
end

lemma range_to_lin_eq_top [decidable_eq n] (M : matrix n n K) (hM : M.det ≠ 0) :
  (to_lin hv₁ hv₁ M).range = ⊤ :=
begin
  rw eq_top_iff,
  rintros x -,
  rw linear_map.mem_range,
  use to_lin hv₁ hv₁ M⁻¹ x,
  rw [← linear_map.comp_apply, ← to_lin_mul, mul_nonsing_inv _ (is_unit.mk0 _ hM),
      to_lin_one, linear_map.id_apply]
end


end vector_space

section finite_dimensional

variables {m n : Type*} [fintype m] [fintype n]
variables {R : Type v} [field R]

instance : finite_dimensional R (matrix m n R) :=
linear_equiv.finite_dimensional (linear_equiv.uncurry R m n).symm

/--
The dimension of the space of finite dimensional matrices
is the product of the number of rows and columns.
-/
@[simp] lemma findim_matrix :
  finite_dimensional.findim R (matrix m n R) = fintype.card m * fintype.card n :=
by rw [@linear_equiv.findim_eq R (matrix m n R) _ _ _ _ _ _ (linear_equiv.uncurry R m n),
       finite_dimensional.findim_fintype_fun_eq_card, fintype.card_prod]

end finite_dimensional

section reindexing

variables {l m n : Type*} [fintype l] [fintype m] [fintype n]
variables {l' m' n' : Type*} [fintype l'] [fintype m'] [fintype n']
variables {R : Type v}

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is an
equivalence. -/
def reindex (eₘ : m ≃ m') (eₙ : n ≃ n') : matrix m n R ≃ matrix m' n' R :=
{ to_fun    := λ M i j, M (eₘ.symm i) (eₙ.symm j),
  inv_fun   := λ M i j, M (eₘ i) (eₙ j),
  left_inv  := λ M, by simp,
  right_inv := λ M, by simp, }

@[simp] lemma reindex_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) :
  reindex eₘ eₙ M = λ i j, M (eₘ.symm i) (eₙ.symm j) :=
rfl

@[simp] lemma reindex_symm_apply (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m' n' R) :
  (reindex eₘ eₙ).symm M = λ i j, M (eₘ i) (eₙ j) :=
rfl

@[simp] lemma reindex_refl_refl (A : matrix m n R) :
  (reindex (equiv.refl _) (equiv.refl _) A) = A :=
by { ext, simp only [reindex_apply, equiv.refl_symm, equiv.refl_apply] }

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is a linear
equivalence. -/
def reindex_linear_equiv [semiring R] (eₘ : m ≃ m') (eₙ : n ≃ n') :
  matrix m n R ≃ₗ[R] matrix m' n' R :=
{ map_add'  := λ M N, rfl,
  map_smul' := λ M N, rfl,
..(reindex eₘ eₙ)}

@[simp] lemma coe_reindex_linear_equiv [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) :
  reindex_linear_equiv eₘ eₙ M = λ i j, M (eₘ.symm i) (eₙ.symm j) :=
rfl

lemma reindex_linear_equiv_apply [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) (i j) :
  reindex_linear_equiv eₘ eₙ M i j = M (eₘ.symm i) (eₙ.symm j) :=
rfl

@[simp] lemma coe_reindex_linear_equiv_symm [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m' n' R) :
  (reindex_linear_equiv eₘ eₙ).symm M = λ i j, M (eₘ i) (eₙ j) :=
rfl

lemma reindex_linear_equiv_symm_apply [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m' n' R) (i j) :
  (reindex_linear_equiv eₘ eₙ).symm M i j = M (eₘ i) (eₙ j) :=
rfl

@[simp] lemma reindex_linear_equiv_refl_refl [semiring R] (A : matrix m n R) :
  (reindex_linear_equiv (equiv.refl _) (equiv.refl _) A) = A :=
reindex_refl_refl A

lemma reindex_mul [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (eₗ : l ≃ l') (M : matrix m n R) (N : matrix n l R) :
  (reindex_linear_equiv eₘ eₙ M) ⬝ (reindex_linear_equiv eₙ eₗ N) =
  reindex_linear_equiv eₘ eₗ (M ⬝ N) :=
begin
  ext i j,
  dsimp only [matrix.mul, matrix.dot_product],
  rw [←finset.univ_map_equiv_to_embedding eₙ, finset.sum_map finset.univ eₙ.to_embedding],
  simp,
end

/-- For square matrices, the natural map that reindexes a matrix's rows and columns with equivalent
types is an equivalence of algebras. -/
def reindex_alg_equiv [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) : matrix m m R ≃ₐ[R] matrix n n R :=
{ map_mul'  := λ M N, by simp only [reindex_mul, linear_equiv.to_fun_eq_coe, mul_eq_mul],
  commutes' := λ r,
                 by { ext, simp [algebra_map, algebra.to_ring_hom], by_cases h : i = j; simp [h], },
..(reindex_linear_equiv e e) }

@[simp] lemma coe_reindex_alg_equiv [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix m m R) :
  reindex_alg_equiv e M = λ i j, M (e.symm i) (e.symm j) :=
rfl

@[simp] lemma reindex_alg_equiv_apply [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix m m R) (i j) :
  reindex_alg_equiv e M i j = M (e.symm i) (e.symm j) :=
rfl

@[simp] lemma coe_reindex_alg_equiv_symm [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix n n R) :
  (reindex_alg_equiv e).symm M = λ i j, M (e i) (e j) :=
rfl

@[simp] lemma reindex_alg_equiv_symm_apply [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix n n R) (i j):
  (reindex_alg_equiv e).symm M i j = M (e i) (e j) :=
rfl

@[simp] lemma reindex_alg_equiv_refl [comm_semiring R] [decidable_eq m]
  (A : matrix m m R) : (reindex_alg_equiv (equiv.refl m) A) = A :=
reindex_linear_equiv_refl_refl A

lemma reindex_transpose (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) :
  (reindex eₘ eₙ M)ᵀ = (reindex eₙ eₘ Mᵀ) :=
rfl

/-- `simp` version of `det_reindex_self`

`det_reindex_self` is not a good simp lemma because `reindex_apply` fires before.
So we have this lemma to continue from there. -/
@[simp]
lemma det_reindex_self' [decidable_eq m] [decidable_eq n] [comm_ring R]
  (e : m ≃ n) (A : matrix m m R) :
  det (λ i j, A (e.symm i) (e.symm j)) = det A :=
begin
  unfold det,
  apply finset.sum_bij' (λ σ _, equiv.perm_congr e.symm σ) _ _ (λ σ _, equiv.perm_congr e σ),
  { intros σ _, ext, simp only [equiv.symm_symm, equiv.perm_congr_apply, equiv.apply_symm_apply] },
  { intros σ _, ext, simp only [equiv.symm_symm, equiv.perm_congr_apply, equiv.symm_apply_apply] },
  { intros σ _, apply finset.mem_univ },
  { intros σ _, apply finset.mem_univ },
  intros σ _,
  simp_rw [equiv.perm_congr_apply, equiv.symm_symm],
  congr,
  { convert (equiv.perm.sign_perm_congr e.symm σ).symm },
  apply finset.prod_bij' (λ i _, e.symm i) _ _ (λ i _, e i),
  { intros, simp_rw equiv.apply_symm_apply },
  { intros, simp_rw equiv.symm_apply_apply },
  { intros, apply finset.mem_univ },
  { intros, apply finset.mem_univ },
  { intros, simp_rw equiv.apply_symm_apply },
end

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_reindex_self'`.
-/
lemma det_reindex_self [decidable_eq m] [decidable_eq n] [comm_ring R]
  (e : m ≃ n) (A : matrix m m R) :
  det (reindex e e A) = det A :=
det_reindex_self' e A

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_reindex_self'`.
-/
lemma det_reindex_linear_equiv_self [decidable_eq m] [decidable_eq n] [comm_ring R]
  (e : m ≃ n) (A : matrix m m R) :
  det (reindex_linear_equiv e e A) = det A :=
det_reindex_self' e A

/-- Reindexing both indices along the same equivalence preserves the determinant.

For the `simp` version of this lemma, see `det_reindex_self'`.
-/
lemma det_reindex_alg_equiv [decidable_eq m] [decidable_eq n] [comm_ring R]
  (e : m ≃ n) (A : matrix m m R) :
  det (reindex_alg_equiv e A) = det A :=
det_reindex_self' e A

end reindexing

section lmul

variables {R S T : Type*} [comm_ring R] [comm_ring S] [comm_ring T]
variables [algebra R S] [algebra S T] [algebra R T] [is_scalar_tower R S T]
variables {m n : Type*} [fintype m] [decidable_eq m] [fintype n] [decidable_eq n]
variables {b : m → S} (hb : is_basis R b) {c : n → T} (hc : is_basis S c)

open algebra

@[simp] lemma lmul_algebra_map (x : R) :
  lmul R S (algebra_map R S x) = algebra.lsmul R S x :=
linear_map.ext (λ s, by simp [smul_def''])

lemma to_matrix_lmul' (x : S) (i j) :
  linear_map.to_matrix hb hb (lmul R S x) i j = hb.repr (x * b j) i :=
by rw [linear_map.to_matrix_apply', lmul_apply]

@[simp] lemma to_matrix_lsmul (x : R) (i j) :
  linear_map.to_matrix hb hb (algebra.lsmul R S x) i j = if i = j then x else 0 :=
by { rw [linear_map.to_matrix_apply', algebra.lsmul_coe, linear_map.map_smul, finsupp.smul_apply,
         hb.repr_self_apply, smul_eq_mul, mul_boole],
     congr' 1; simp only [eq_comm] }

/-- `matrix.lmul hb x` is the matrix corresponding to the linear map `λ y, x * y`.

This definition is useful for doing (more) explicit computations with `algebra.lmul`,
such as the trace form or norm map for algebras.
-/
protected noncomputable def lmul : S →ₐ[R] matrix m m R :=
{ to_fun := λ x, linear_map.to_matrix hb hb (algebra.lmul R S x),
  map_zero' := by rw [alg_hom.map_zero, linear_equiv.map_zero],
  map_one' := by rw [alg_hom.map_one, linear_map.to_matrix_one],
  map_add' := λ x y, by rw [alg_hom.map_add, linear_equiv.map_add],
  map_mul' := λ x y, by rw [alg_hom.map_mul, linear_map.to_matrix_mul, matrix.mul_eq_mul],
  commutes' := λ r, by { ext, rw [lmul_algebra_map, to_matrix_lsmul,
                                  algebra_map_matrix_apply, id.map_eq_self] } }

lemma lmul_apply (x : S) (i j) :
  matrix.lmul hb x i j = linear_map.to_matrix hb hb (lmul R S x) i j := rfl

@[simp] lemma to_matrix_lmul_eq (x : S) :
  linear_map.to_matrix hb hb (lmul R S x) = matrix.lmul hb x :=
rfl

lemma lmul_injective : function.injective (matrix.lmul hb) :=
λ x x' h, calc x = algebra.lmul R S x 1 : (mul_one x).symm
             ... = algebra.lmul R S x' 1 : by rw (linear_map.to_matrix hb hb).injective h
             ... = x' : mul_one x'

lemma smul_lmul (x) (i j) (k k') :
  matrix.lmul (hb.smul hc) x (i, k) (j, k') = matrix.lmul hb (matrix.lmul hc x k k') i j :=
by simp only [matrix.lmul_apply, linear_map.to_matrix_apply, is_basis.equiv_fun_apply, mul_comm,
              is_basis.smul_repr, finsupp.smul_apply, algebra.lmul_apply, id.smul_eq_mul,
              linear_map.map_smul, mul_smul_comm]

lemma smul_lmul_algebra_map (x : S) :
  matrix.lmul (hb.smul hc) (algebra_map _ _ x) = block_diagonal (λ k, matrix.lmul hb x) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  rw [smul_lmul, alg_hom.commutes, block_diagonal_apply, algebra_map_matrix_apply],
  split_ifs with h; simp [h],
end

lemma smul_lmul_algebra_map_eq (x : S) (i j k) :
  matrix.lmul (hb.smul hc) (algebra_map _ _ x) (i, k) (j, k) = matrix.lmul hb x i j :=
by rw [smul_lmul_algebra_map, block_diagonal_apply_eq]

lemma smul_lmul_algebra_map_ne (x : S) (i j) {k k'}
  (h : k ≠ k') : matrix.lmul (hb.smul hc) (algebra_map _ _ x) (i, k) (j, k') = 0 :=
by rw [smul_lmul_algebra_map, block_diagonal_apply_ne _ _ _ h]

end lmul

end matrix

namespace linear_map

open_locale matrix

/-- The trace of an endomorphism given a basis. -/
def trace_aux (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) :
  (M →ₗ[R] M) →ₗ[R] R :=
(matrix.trace ι R R).comp $ linear_map.to_matrix hb hb

@[simp] lemma trace_aux_def (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) (f : M →ₗ[R] M) :
  trace_aux R hb f = matrix.trace ι R R (linear_map.to_matrix hb hb f) :=
rfl

theorem trace_aux_eq' (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b)
  {κ : Type w} [decidable_eq κ] [fintype κ] {c : κ → M} (hc : is_basis R c) :
  trace_aux R hb = trace_aux R hc :=
linear_map.ext $ λ f,
calc  matrix.trace ι R R (linear_map.to_matrix hb hb f)
    = matrix.trace ι R R (linear_map.to_matrix hb hb ((linear_map.id.comp f).comp linear_map.id)) :
  by rw [linear_map.id_comp, linear_map.comp_id]
... = matrix.trace ι R R (linear_map.to_matrix hc hb linear_map.id ⬝
        linear_map.to_matrix hc hc f ⬝
        linear_map.to_matrix hb hc linear_map.id) :
  by rw [linear_map.to_matrix_comp _ hc, linear_map.to_matrix_comp _ hc]
... = matrix.trace κ R R (linear_map.to_matrix hc hc f ⬝
        linear_map.to_matrix hb hc linear_map.id ⬝
        linear_map.to_matrix hc hb linear_map.id) :
  by rw [matrix.mul_assoc, matrix.trace_mul_comm]
... = matrix.trace κ R R (linear_map.to_matrix hc hc ((f.comp linear_map.id).comp linear_map.id)) :
  by rw [linear_map.to_matrix_comp _ hb, linear_map.to_matrix_comp _ hc]
... = matrix.trace κ R R (linear_map.to_matrix hc hc f) :
  by rw [linear_map.comp_id, linear_map.comp_id]

open_locale classical

theorem trace_aux_range (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) :
  trace_aux R hb.range = trace_aux R hb :=
linear_map.ext $ λ f, if H : 0 = 1 then eq_of_zero_eq_one H _ _ else
begin
  haveI : nontrivial R := ⟨⟨0, 1, H⟩⟩,
  change ∑ i : set.range b, _ = ∑ i : ι, _, simp_rw [matrix.diag_apply], symmetry,
  convert (equiv.of_injective _ hb.injective).sum_comp _, ext i,
  exact (linear_map.to_matrix_range hb hb f i i).symm
end

/-- where `ι` and `κ` can reside in different universes -/
theorem trace_aux_eq (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type*} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b)
  {κ : Type*} [decidable_eq κ] [fintype κ] {c : κ → M} (hc : is_basis R c) :
  trace_aux R hb = trace_aux R hc :=
calc  trace_aux R hb
    = trace_aux R hb.range : by rw trace_aux_range R hb
... = trace_aux R hc.range : trace_aux_eq' _ _ _
... = trace_aux R hc : by rw trace_aux_range R hc

/-- Trace of an endomorphism independent of basis. -/
def trace (R : Type u) [comm_ring R] (M : Type v) [add_comm_group M] [module R M] :
  (M →ₗ[R] M) →ₗ[R] R :=
if H : ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M)
then trace_aux R (classical.some_spec H)
else 0

theorem trace_eq_matrix_trace (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [fintype ι] [decidable_eq ι] {b : ι → M} (hb : is_basis R b) (f : M →ₗ[R] M) :
  trace R M f = matrix.trace ι R R (linear_map.to_matrix hb hb f) :=
have ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M),
from ⟨finset.univ.image b,
  by { rw [finset.coe_image, finset.coe_univ, set.image_univ], exact hb.range }⟩,
by { rw [trace, dif_pos this, ← trace_aux_def], congr' 1, apply trace_aux_eq }

theorem trace_mul_comm (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  (f g : M →ₗ[R] M) : trace R M (f * g) = trace R M (g * f) :=
if H : ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M) then let ⟨s, hb⟩ := H in
by { simp_rw [trace_eq_matrix_trace R hb, linear_map.to_matrix_mul], apply matrix.trace_mul_comm }
else by rw [trace, dif_neg H, linear_map.zero_apply, linear_map.zero_apply]

section finite_dimensional

variables {K : Type*} [field K]
variables {V : Type*} [add_comm_group V] [vector_space K V] [finite_dimensional K V]
variables {W : Type*} [add_comm_group W] [vector_space K W] [finite_dimensional K W]

instance : finite_dimensional K (V →ₗ[K] W) :=
begin
  classical,
  cases finite_dimensional.exists_is_basis_finset K V with bV hbV,
  cases finite_dimensional.exists_is_basis_finset K W with bW hbW,
  apply linear_equiv.finite_dimensional (linear_map.to_matrix hbV hbW).symm,
end

/--
The dimension of the space of linear transformations is the product of the dimensions of the
domain and codomain.
-/
@[simp] lemma findim_linear_map :
  finite_dimensional.findim K (V →ₗ[K] W) =
  (finite_dimensional.findim K V) * (finite_dimensional.findim K W) :=
begin
  classical,
  cases finite_dimensional.exists_is_basis_finset K V with bV hbV,
  cases finite_dimensional.exists_is_basis_finset K W with bW hbW,
  rw [linear_equiv.findim_eq (linear_map.to_matrix hbV hbW), matrix.findim_matrix,
    finite_dimensional.findim_eq_card_basis hbV, finite_dimensional.findim_eq_card_basis hbW,
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
  [comm_ring R] [add_comm_group M] [module R M] [decidable_eq n] {b : n → M} (h : is_basis R b) :
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
  unfold det,
  congr, ext σ, congr, ext,
  generalize hy : σ x = y,
  cases x; cases y;
  simp only [matrix.reindex_apply, to_block_apply, equiv.symm_symm,
    equiv.sum_compl_apply_inr, equiv.sum_compl_apply_inl,
    from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂],
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
  { exact absurd hk12 (nat.not_lt_zero 1) },
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
  { rw finset.prod_range_succ,
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
