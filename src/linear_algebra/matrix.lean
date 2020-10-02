/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl, Patrick Massot, Casper Putz
-/
import linear_algebra.finite_dimensional
import linear_algebra.nonsingular_inverse
import linear_algebra.multilinear
import linear_algebra.dual

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

## Main definitions

In the list below, and in all this file, `R` is a commutative ring (semiring
is sometimes enough), `M` and its variations are `R`-modules, `ι`, `κ`, `n` and `m` are finite
types used for indexing.

* `to_lin`: the `R`-linear map from `matrix m n R` to `R`-linear maps from `n → R` to `m → R`
* `to_matrix`: the map in the other direction
* `linear_equiv_matrix`: given bases `v₁ : ι → M₁` and `v₂ : κ → M₂`, the `R`-linear equivalence
  from `M₁ →ₗ[R] M₂` to `matrix κ ι R`
* `linear_equiv_matrix'`: the same thing but with `M₁ = n → R` and `M₂ = m → R`, using their
  standard bases
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

open set submodule
open_locale big_operators

universes u v w
variables {l m n : Type*} [fintype l] [fintype m] [fintype n]

namespace matrix

variables {R : Type v} [comm_ring R]
instance [decidable_eq m] [decidable_eq n] (R) [fintype R] : fintype (matrix m n R) :=
by unfold matrix; apply_instance

/-- Evaluation of matrices gives a linear map from `matrix m n R` to
linear maps `(n → R) →ₗ[R] (m → R)`. -/
def eval : (matrix m n R) →ₗ[R] ((n → R) →ₗ[R] (m → R)) :=
begin
  refine linear_map.mk₂ R mul_vec _ _ _ _,
  { assume M N v, funext x,
    change ∑ y : n, (M x y + N x y) * v y = _,
    simp only [_root_.add_mul, finset.sum_add_distrib],
    refl },
  { assume c M v, funext x,
    change ∑ y : n, (c * M x y) * v y = _,
    simp only [_root_.mul_assoc, finset.mul_sum.symm],
    refl },
  { assume M v w, funext x,
    change ∑ y : n, M x y * (v y + w y) = _,
    simp [_root_.mul_add, finset.sum_add_distrib],
    refl },
  { assume c M v, funext x,
    change ∑ y : n, M x y * (c * v y) = _,
    rw [show (λy:n, M x y * (c * v y)) = (λy:n, c * (M x y * v y)), { funext n, ac_refl },
      ← finset.mul_sum],
    refl }
end

/-- Evaluation of matrices gives a map from `matrix m n R` to
linear maps `(n → R) →ₗ[R] (m → R)`. -/
def to_lin : matrix m n R → (n → R) →ₗ[R] (m → R) := eval.to_fun

theorem to_lin_of_equiv {p q : Type*} [fintype p] [fintype q] (e₁ : m ≃ p) (e₂ : n ≃ q)
  (f : matrix p q R) : to_lin (λ i j, f (e₁ i) (e₂ j) : matrix m n R) =
    linear_equiv.arrow_congr
      (linear_map.fun_congr_left R R e₂)
      (linear_map.fun_congr_left R R e₁)
      (to_lin f) :=
linear_map.ext $ λ v, funext $ λ i,
calc  ∑ j : n, f (e₁ i) (e₂ j) * v j
    = ∑ j : n, f (e₁ i) (e₂ j) * v (e₂.symm (e₂ j)) : by simp_rw e₂.symm_apply_apply
... = ∑ k : q, f (e₁ i) k * v (e₂.symm k) : e₂.sum_comp (λ k, f (e₁ i) k * v (e₂.symm k))

lemma to_lin_add (M N : matrix m n R) : (M + N).to_lin = M.to_lin + N.to_lin :=
matrix.eval.map_add M N

@[simp] lemma to_lin_zero : (0 : matrix m n R).to_lin = 0 :=
matrix.eval.map_zero

@[simp] lemma to_lin_neg (M : matrix m n R) : (-M).to_lin = -M.to_lin :=
@linear_map.map_neg _ _ ((n → R) →ₗ[R] m → R) _ _ _ _ _ matrix.eval M

instance to_lin.is_add_monoid_hom :
  @is_add_monoid_hom (matrix m n R) ((n → R) →ₗ[R] (m → R)) _ _ to_lin :=
{ map_zero := to_lin_zero, map_add := to_lin_add }

@[simp] lemma to_lin_apply (M : matrix m n R) (v : n → R) :
  (M.to_lin : (n → R) → (m → R)) v = mul_vec M v := rfl

lemma mul_to_lin (M : matrix m n R) (N : matrix n l R) :
  (M.mul N).to_lin = M.to_lin.comp N.to_lin :=
by { ext, simp }

@[simp] lemma to_lin_one [decidable_eq n] : (1 : matrix n n R).to_lin = linear_map.id :=
by { ext, simp }

end matrix

namespace linear_map

variables {R : Type v} [comm_ring R]

/-- The linear map from linear maps `(n → R) →ₗ[R] (m → R)` to `matrix m n R`. -/
def to_matrixₗ [decidable_eq n] : ((n → R) →ₗ[R] (m → R)) →ₗ[R] matrix m n R :=
begin
  refine linear_map.mk (λ f i j, f (λ n, ite (j = n) 1 0) i) _ _,
  { assume f g, simp only [add_apply], refl },
  { assume f g, simp only [smul_apply], refl }
end

/-- The map from linear maps `(n → R) →ₗ[R] (m → R)` to `matrix m n R`. -/
def to_matrix [decidable_eq n] : ((n → R) →ₗ[R] (m → R)) → matrix m n R := to_matrixₗ.to_fun

@[simp] lemma to_matrix_id [decidable_eq n] :
  (@linear_map.id _ (n → R) _ _ _).to_matrix = 1 :=
by { ext, simp [to_matrix, to_matrixₗ, matrix.one_apply, eq_comm] }

theorem to_matrix_of_equiv {p q : Type*} [decidable_eq n] [decidable_eq q] [fintype p] [fintype q]
  (e₁ : m ≃ p) (e₂ : n ≃ q) (f : (q → R) →ₗ[R] (p → R)) (i j) :
  to_matrix f (e₁ i) (e₂ j) = to_matrix (linear_equiv.arrow_congr
      (linear_map.fun_congr_left R R e₂)
      (linear_map.fun_congr_left R R e₁) f) i j :=
show f (λ k : q, ite (e₂ j = k) 1 0) (e₁ i) = f (λ k : q, ite (j = e₂.symm k) 1 0) (e₁ i),
by { rcongr, rw equiv.eq_symm_apply }

end linear_map

section linear_equiv_matrix

variables {R : Type v} [comm_ring R] [decidable_eq n]

open finsupp matrix linear_map

/-- `to_lin` is the left inverse of `to_matrix`. -/
lemma to_matrix_to_lin {f : (n → R) →ₗ[R] (m → R)} :
  to_lin (to_matrix f) = f :=
begin
  ext : 1,
  -- Show that the two sides are equal by showing that they are equal on a basis
  convert linear_eq_on (set.range _) _ (is_basis.mem_span (@pi.is_basis_fun R n _ _) _),
  assume e he,
  rw [@std_basis_eq_single R _ _ _ 1] at he,
  cases (set.mem_range.mp he) with i h,
  ext j,
  change ∑ k, (f (λ l, ite (k = l) 1 0)) j * (e k) = _,
  rw [←h],
  conv_lhs { congr, skip, funext,
    rw [mul_comm, ←smul_eq_mul, ←pi.smul_apply, ←linear_map.map_smul],
    rw [show _ = ite (i = k) (1:R) 0, by convert single_apply],
    rw [show f (ite (i = k) (1:R) 0 • (λ l, ite (k = l) 1 0)) = ite (i = k) (f _) 0,
      { split_ifs, { rw [one_smul] }, { rw [zero_smul], exact linear_map.map_zero f } }] },
  convert finset.sum_eq_single i _ _,
  { rw [if_pos rfl], convert rfl, ext, congr },
  { assume _ _ hbi, rw [if_neg $ ne.symm hbi], refl },
  { assume hi, exact false.elim (hi $ finset.mem_univ i) }
end

/-- `to_lin` is the right inverse of `to_matrix`. -/
lemma to_lin_to_matrix {M : matrix m n R} : to_matrix (to_lin M) = M :=
begin
  ext,
  change ∑ y, M i y * ite (j = y) 1 0 = M i j,
  have h1 : (λ y, M i y * ite (j = y) 1 0) = (λ y, ite (j = y) (M i y) 0),
    { ext, split_ifs, exact mul_one _, exact mul_zero _ },
  have h2 : ∑ y, ite (j = y) (M i y) 0 = ∑ y in {j}, ite (j = y) (M i y) 0,
    { refine (finset.sum_subset _ _).symm,
      { intros _ H, rwa finset.mem_singleton.1 H, exact finset.mem_univ _ },
      { exact λ _ _ H, if_neg (mt (finset.mem_singleton.2 ∘ eq.symm) H) } },
  rw [h1, h2, finset.sum_singleton],
  exact if_pos rfl
end

/-- Linear maps `(n → R) →ₗ[R] (m → R)` are linearly equivalent to `matrix m n R`. -/
def linear_equiv_matrix' : ((n → R) →ₗ[R] (m → R)) ≃ₗ[R] matrix m n R :=
{ to_fun := to_matrix,
  inv_fun := to_lin,
  right_inv := λ _, to_lin_to_matrix,
  left_inv := λ _, to_matrix_to_lin,
  map_add' := to_matrixₗ.map_add,
  map_smul' := to_matrixₗ.map_smul }

@[simp] lemma linear_equiv_matrix'_apply (f : (n → R) →ₗ[R] (m → R)) :
  linear_equiv_matrix' f = to_matrix f := rfl

@[simp] lemma linear_equiv_matrix'_symm_apply (M : matrix m n R) :
  linear_equiv_matrix'.symm M = M.to_lin := rfl

variables {ι κ M₁ M₂ : Type*}
  [add_comm_group M₁] [module R M₁]
  [add_comm_group M₂] [module R M₂]
  [fintype ι] [decidable_eq ι] [fintype κ]
  {v₁ : ι → M₁} {v₂ : κ → M₂}

/-- Given bases of two modules `M₁` and `M₂` over a commutative ring `R`, we get a linear
equivalence between linear maps `M₁ →ₗ M₂` and matrices over `R` indexed by the bases. -/
def linear_equiv_matrix (hv₁ : is_basis R v₁) (hv₂ : is_basis R v₂) :
  (M₁ →ₗ[R] M₂) ≃ₗ[R] matrix κ ι R :=
linear_equiv.trans (linear_equiv.arrow_congr hv₁.equiv_fun hv₂.equiv_fun) linear_equiv_matrix'

variables (hv₁ : is_basis R v₁) (hv₂ : is_basis R v₂)

lemma linear_equiv_matrix_apply (f : M₁ →ₗ[R] M₂) (i : κ) (j : ι) :
  linear_equiv_matrix hv₁ hv₂ f i j = hv₂.equiv_fun (f (v₁ j)) i :=
by simp only [linear_equiv_matrix, to_matrix, to_matrixₗ, ite_smul,
  linear_equiv.trans_apply, linear_equiv.arrow_congr_apply,
  linear_equiv.coe_coe, linear_equiv_matrix'_apply, finset.mem_univ, if_true,
  one_smul, zero_smul, finset.sum_ite_eq, hv₁.equiv_fun_symm_apply]

lemma linear_equiv_matrix_symm_apply (m : matrix κ ι R) (x : M₁) :
  (linear_equiv_matrix hv₁ hv₂).symm m x = hv₂.equiv_fun.symm (m.to_lin $ hv₁.equiv_fun x) :=
by simp only [linear_equiv_matrix, linear_equiv.arrow_congr_symm_apply,
    linear_equiv_matrix'_symm_apply, linear_equiv.symm_trans_apply]

lemma linear_equiv_matrix_apply' (f : M₁ →ₗ[R] M₂) (i : κ) (j : ι) :
  linear_equiv_matrix hv₁ hv₂ f i j = hv₂.repr (f (v₁ j)) i :=
linear_equiv_matrix_apply hv₁ hv₂ f i j

@[simp]
lemma linear_equiv_matrix_id : linear_equiv_matrix hv₁ hv₁ id = 1 :=
begin
  ext i j,
  simp [linear_equiv_matrix_apply, is_basis.equiv_fun, matrix.one_apply, finsupp.single, eq_comm]
end

@[simp] lemma linear_equiv_matrix_symm_one : (linear_equiv_matrix hv₁ hv₁).symm 1 = id :=
begin
  rw [← linear_equiv_matrix_id hv₁, ← linear_equiv.trans_apply],
  simp
end

open_locale classical

theorem linear_equiv_matrix_range (f : M₁ →ₗ[R] M₂) (k : κ) (i : ι) :
  linear_equiv_matrix hv₁.range hv₂.range f ⟨v₂ k, mem_range_self k⟩ ⟨v₁ i, mem_range_self i⟩ =
    linear_equiv_matrix hv₁ hv₂ f k i :=
if H : (0 : R) = 1 then eq_of_zero_eq_one H _ _ else
begin
  haveI : nontrivial R := ⟨⟨0, 1, H⟩⟩,
  simp_rw [linear_equiv_matrix, linear_equiv.trans_apply, linear_equiv_matrix'_apply,
    ← equiv.of_injective_apply _ hv₁.injective, ← equiv.of_injective_apply _ hv₂.injective,
    to_matrix_of_equiv, ← linear_equiv.trans_apply, linear_equiv.arrow_congr_trans], congr' 3;
  refine function.left_inverse.injective linear_equiv.symm_symm _; ext x;
  simp_rw [linear_equiv.symm_trans_apply, is_basis.equiv_fun_symm_apply, fun_congr_left_symm,
    fun_congr_left_apply, fun_left_apply],
  convert ((equiv.of_injective _ hv₁.injective).sum_comp _).symm,
  simp_rw [equiv.symm_apply_apply, equiv.of_injective_apply, subtype.coe_mk],
  convert ((equiv.of_injective _ hv₂.injective).sum_comp _).symm,
  simp_rw [equiv.symm_apply_apply, equiv.of_injective_apply, subtype.coe_mk]
end

end linear_equiv_matrix

namespace matrix
open_locale matrix

lemma comp_to_matrix_mul {R : Type v} [comm_ring R] [decidable_eq l] [decidable_eq m]
  (f : (m → R) →ₗ[R] (n → R)) (g : (l → R) →ₗ[R] (m → R)) :
  (f.comp g).to_matrix = f.to_matrix ⬝ g.to_matrix :=
suffices (f.comp g) = (f.to_matrix ⬝ g.to_matrix).to_lin, by rw [this, to_lin_to_matrix],
by rw [mul_to_lin, to_matrix_to_lin, to_matrix_to_lin]

section comp

variables {R ι κ μ M₁ M₂ M₃ : Type*} [comm_ring R]
  [add_comm_group M₁] [module R M₁]
  [add_comm_group M₂] [module R M₂]
  [add_comm_group M₃] [module R M₃]
  [fintype ι] [decidable_eq κ] [fintype κ] [fintype μ]
  {v₁ : ι → M₁} {v₂ : κ → M₂} {v₃ : μ → M₃}
  (hv₁ : is_basis R v₁) (hv₂ : is_basis R v₂) (hv₃ : is_basis R v₃)

lemma linear_equiv_matrix_comp [decidable_eq ι] (f : M₂ →ₗ[R] M₃) (g : M₁ →ₗ[R] M₂) :
  linear_equiv_matrix hv₁ hv₃ (f.comp g) =
  linear_equiv_matrix hv₂ hv₃ f ⬝ linear_equiv_matrix hv₁ hv₂ g :=
by simp_rw [linear_equiv_matrix, linear_equiv.trans_apply, linear_equiv_matrix'_apply,
    linear_equiv.arrow_congr_comp _ hv₂.equiv_fun, comp_to_matrix_mul]

lemma linear_equiv_matrix_mul [decidable_eq ι] (f g : M₁ →ₗ[R] M₁) :
  linear_equiv_matrix hv₁ hv₁ (f * g) = linear_equiv_matrix hv₁ hv₁ f * linear_equiv_matrix hv₁ hv₁ g :=
linear_equiv_matrix_comp hv₁ hv₁ hv₁ f g

lemma linear_equiv_matrix_symm_mul [decidable_eq μ] (A : matrix ι κ R) (B : matrix κ μ R) :
  (linear_equiv_matrix hv₃ hv₁).symm (A ⬝ B) =
  ((linear_equiv_matrix hv₂ hv₁).symm A).comp ((linear_equiv_matrix hv₃ hv₂).symm B) :=
begin
  suffices :  A ⬝ B = (linear_equiv_matrix hv₃ hv₁)
     (((linear_equiv_matrix hv₂ hv₁).symm A).comp $ (linear_equiv_matrix hv₃ hv₂).symm B),
    by rw [this, ← linear_equiv.trans_apply, linear_equiv.trans_symm, linear_equiv.refl_apply],
  rw [linear_equiv_matrix_comp hv₃ hv₂ hv₁,
      linear_equiv.apply_symm_apply, linear_equiv.apply_symm_apply]
end

end comp

end matrix

section is_basis_to_matrix

variables {ι ι' R M : Type*} [fintype ι] [decidable_eq ι]
          [comm_ring R] [add_comm_group M] [module R M]

open function matrix

/-- From a basis `e : ι → M` and a family of vectors `v : ι → M`, make the matrix whose columns
are the vectors `v i` written in the basis `e`. -/
def is_basis.to_matrix {e : ι → M} (he : is_basis R e) (v : ι → M) : matrix ι ι R :=
linear_equiv_matrix he he (he.constr v)

variables {e : ι → M} (he : is_basis R e) (v : ι → M) (i j : ι)

namespace is_basis

lemma to_matrix_apply : he.to_matrix v i j = he.equiv_fun (v j) i :=
by simp [is_basis.to_matrix, linear_equiv_matrix_apply]

@[simp] lemma to_matrix_self : he.to_matrix e = 1 :=
begin
  rw is_basis.to_matrix,
  ext i j,
  simp [linear_equiv_matrix_apply, is_basis.equiv_fun, matrix.one_apply, finsupp.single, eq_comm]
end

lemma to_matrix_update (x : M) :
  he.to_matrix (function.update v i x) = matrix.update_column (he.to_matrix v) i (he.repr x) :=
begin
  ext j k,
  rw [is_basis.to_matrix, linear_equiv_matrix_apply' he he (he.constr (update v i x)),
      matrix.update_column_apply, constr_basis, he.to_matrix_apply],
  split_ifs,
  { rw [h, update_same i x v] },
  { rw [update_noteq h, he.equiv_fun_apply] },
end

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

end is_basis_to_matrix

open_locale matrix

section det
open matrix
variables {R ι M M' : Type*} [comm_ring R]
  [add_comm_group M] [module R M]
  [add_comm_group M'] [module R M']
  [decidable_eq ι] [fintype ι]
  {v : ι → M} {v' : ι → M'}

lemma linear_equiv.is_unit_det (f : M ≃ₗ[R] M') (hv : is_basis R v) (hv' : is_basis R v') :
  is_unit (linear_equiv_matrix hv hv' f).det :=
begin
  apply is_unit_det_of_left_inverse,
  simpa using (linear_equiv_matrix_comp hv hv' hv f.symm f).symm
end

/-- Builds a linear equivalence from a linear map whose determinant in some bases is a unit. -/
def linear_equiv.of_is_unit_det {f : M →ₗ[R] M'} {hv : is_basis R v} {hv' : is_basis R v'}
  (h : is_unit (linear_equiv_matrix hv hv' f).det) : M ≃ₗ[R] M' :=
{ to_fun := f,
  map_add' := f.map_add,
  map_smul' := f.map_smul,
  inv_fun := (linear_equiv_matrix hv' hv).symm (linear_equiv_matrix hv hv' f)⁻¹,
  left_inv := begin
    rw function.left_inverse_iff_comp,
    have : f = (linear_equiv_matrix hv hv').symm (linear_equiv_matrix hv hv' f),
    { rw ← linear_equiv.trans_apply,
      simp },
    conv_lhs { congr, skip, rw this },
    rw [linear_map.comp_coe, ← linear_equiv_matrix_symm_mul],
    simp [h]
  end,
  right_inv := begin
    rw function.right_inverse_iff_comp,
    have : f = (linear_equiv_matrix hv hv').symm (linear_equiv_matrix hv hv' f),
    { change f = (linear_equiv_matrix hv hv').trans (linear_equiv_matrix hv hv').symm f,
      simp },
    conv_lhs { congr, rw this },
    rw [linear_map.comp_coe, ← linear_equiv_matrix_symm_mul],
    simp [h]
  end }

variables {e : ι → M} (he : is_basis R e)

/-- The determinant of a family of vectors with respect to some basis, as a multilinear map. -/
def is_basis.det : multilinear_map R (λ i : ι, M) R :=
{ to_fun := λ v, det (he.to_matrix v),
  map_add' := begin
    intros v i x y,
    simp only [he.to_matrix_update, linear_map.map_add],
    apply det_update_column_add
  end,
  map_smul' := begin
    intros u i c x,
    simp only [he.to_matrix_update, algebra.id.smul_eq_mul, map_smul_eq_smul_map],
    apply det_update_column_smul
  end }

lemma is_basis.det_apply (v : ι → M) : he.det v = det (he.to_matrix v) := rfl

lemma is_basis.det_self : he.det e = 1 :=
by simp [he.det_apply]

lemma is_basis.iff_det {v : ι → M} : is_basis R v ↔ is_unit (he.det v) :=
begin
  split,
  { intro hv,
    change is_unit (linear_equiv_matrix he he (equiv_of_is_basis he hv $ equiv.refl ι)).det,
    apply linear_equiv.is_unit_det },
  { intro h,
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

@[simp] lemma linear_equiv_matrix_transpose (u : V₁ →ₗ[K] V₂) :
  linear_equiv_matrix h₂.dual_basis_is_basis h₁.dual_basis_is_basis (module.dual.transpose u) =
  (linear_equiv_matrix h₁ h₂ u)ᵀ :=
begin
  ext i j,
  simp only [linear_equiv_matrix_apply, module.dual.transpose_apply, h₁.dual_basis_equiv_fun,
             h₂.dual_basis_apply, matrix.transpose_apply, linear_map.comp_apply]
end

lemma linear_equiv_matrix_symm_transpose (M : matrix ι₁ ι₂ K) :
  (linear_equiv_matrix h₁.dual_basis_is_basis h₂.dual_basis_is_basis).symm Mᵀ =
  module.dual.transpose ((linear_equiv_matrix h₂ h₁).symm M) :=
begin
  apply (linear_equiv_matrix h₁.dual_basis_is_basis h₂.dual_basis_is_basis).injective,
  rw [linear_equiv.apply_symm_apply],
  ext i j,
  simp only [linear_equiv_matrix_apply, module.dual.transpose_apply, h₂.dual_basis_equiv_fun,
    h₁.dual_basis_apply, matrix.transpose_apply, linear_map.comp_apply, if_true,
    linear_equiv_matrix_symm_apply, linear_equiv.map_smul, mul_boole, algebra.id.smul_eq_mul,
    linear_equiv.map_sum, is_basis.equiv_fun_self, fintype.sum_apply, finset.sum_ite_eq',
    finset.sum_ite_eq, is_basis.equiv_fun_symm_apply, pi.smul_apply, matrix.to_lin_apply,
    matrix.mul_vec, matrix.dot_product, is_basis.equiv_fun_self, finset.mem_univ]
end

end transpose
namespace matrix

section trace

variables (n) (R : Type v) (M : Type w) [semiring R] [add_comm_monoid M] [semimodule R M]

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

variables {R : Type v} [comm_ring R] [decidable_eq n]
open linear_map matrix

lemma proj_diagonal (i : n) (w : n → R) :
  (proj i).comp (to_lin (diagonal w)) = (w i) • proj i :=
by ext j; simp [mul_vec_diagonal]

lemma diagonal_comp_std_basis (w : n → R) (i : n) :
  (diagonal w).to_lin.comp (std_basis R (λ_:n, R) i) = (w i) • std_basis R (λ_:n, R) i :=
begin
  ext a j,
  simp_rw [linear_map.comp_apply, to_lin_apply, mul_vec_diagonal, linear_map.smul_apply,
    pi.smul_apply, algebra.id.smul_eq_mul],
  by_cases i = j,
  { subst h },
  { rw [std_basis_ne R (λ_:n, R) _ _ (ne.symm h), _root_.mul_zero, _root_.mul_zero] }
end

lemma diagonal_to_lin (w : n → R) :
  (diagonal w).to_lin = linear_map.pi (λi, w i • linear_map.proj i) :=
by ext v j; simp [mul_vec_diagonal]

/-- An invertible matrix yields a linear equivalence from the free module to itself. -/
def to_linear_equiv (P : matrix n n R) (h : is_unit P) : (n → R) ≃ₗ[R] (n → R) :=
have h' : is_unit P.det := P.is_unit_iff_is_unit_det.mp h,
{ inv_fun   := P⁻¹.to_lin,
  left_inv  := λ v,
    show (P⁻¹.to_lin.comp P.to_lin) v = v,
    by rw [←matrix.mul_to_lin, P.nonsing_inv_mul h', matrix.to_lin_one, linear_map.id_apply],
  right_inv := λ v,
    show (P.to_lin.comp P⁻¹.to_lin) v = v,
    by rw [←matrix.mul_to_lin, P.mul_nonsing_inv h', matrix.to_lin_one, linear_map.id_apply],
  ..P.to_lin }

@[simp] lemma to_linear_equiv_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv h) : module.End R (n → R)) = P.to_lin := rfl

@[simp] lemma to_linear_equiv_symm_apply (P : matrix n n R) (h : is_unit P) :
  (↑(P.to_linear_equiv h).symm : module.End R (n → R)) = P⁻¹.to_lin := rfl

end ring

section vector_space

variables {K : Type u} [field K] -- maybe try to relax the universe constraint

open linear_map matrix

set_option pp.all true

lemma rank_vec_mul_vec {m n : Type u} [fintype m] [fintype n]
  (w : m → K) (v : n → K) :
  rank (vec_mul_vec w v).to_lin ≤ 1 :=
begin
  rw [vec_mul_vec_eq, mul_to_lin],
  refine le_trans (rank_comp_le1 _ _) _,
  refine le_trans (rank_le_domain _) _,
  rw [dim_fun', ← cardinal.lift_eq_nat_iff.mpr (cardinal.fintype_card unit), cardinal.mk_unit],
  exact le_of_eq (cardinal.lift_one)
end

lemma ker_diagonal_to_lin [decidable_eq m] (w : m → K) :
  ker (diagonal w).to_lin = (⨆i∈{i | w i = 0 }, range (std_basis K (λi, K) i)) :=
begin
  rw [← comap_bot, ← infi_ker_proj],
  simp only [comap_infi, (ker_comp _ _).symm, proj_diagonal, ker_smul'],
  have : univ ⊆ {i : m | w i = 0} ∪ {i : m | w i = 0}ᶜ, { rw set.union_compl_self },
  exact (supr_range_std_basis_eq_infi_ker_proj K (λi:m, K)
    (disjoint_compl_right {i | w i = 0}) this (finite.of_fintype _)).symm
end

lemma range_diagonal [decidable_eq m] (w : m → K) :
  (diagonal w).to_lin.range = (⨆ i ∈ {i | w i ≠ 0}, (std_basis K (λi, K) i).range) :=
begin
  dsimp only [mem_set_of_eq],
  rw [← map_top, ← supr_range_std_basis, map_supr],
  congr, funext i,
  rw [← linear_map.range_comp, diagonal_comp_std_basis, ← range_smul']
end

lemma rank_diagonal [decidable_eq m] [decidable_eq K] (w : m → K) :
  rank (diagonal w).to_lin = fintype.card { i // w i ≠ 0 } :=
begin
  have hu : univ ⊆ {i : m | w i = 0}ᶜ ∪ {i : m | w i = 0}, { rw set.compl_union_self },
  have hd : disjoint {i : m | w i ≠ 0} {i : m | w i = 0} := (disjoint_compl_right {i | w i = 0}).symm,
  have h₁ := supr_range_std_basis_eq_infi_ker_proj K (λi:m, K) hd hu (finite.of_fintype _),
  have h₂ := @infi_ker_proj_equiv K _ _ (λi:m, K) _ _ _ _ (by simp; apply_instance) hd hu,
  rw [rank, range_diagonal, h₁, ←@dim_fun' K],
  apply linear_equiv.dim_eq,
  apply h₂,
end

end vector_space

section finite_dimensional

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

/-- The natural map that reindexes a matrix's rows and columns with equivalent types is a linear
equivalence. -/
def reindex_linear_equiv [semiring R] (eₘ : m ≃ m') (eₙ : n ≃ n') :
  matrix m n R ≃ₗ[R] matrix m' n' R :=
{ map_add'  := λ M N, rfl,
  map_smul' := λ M N, rfl,
..(reindex eₘ eₙ)}

@[simp] lemma reindex_linear_equiv_apply [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) :
  reindex_linear_equiv eₘ eₙ M = λ i j, M (eₘ.symm i) (eₙ.symm j) :=
rfl

@[simp] lemma reindex_linear_equiv_symm_apply [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m' n' R) :
  (reindex_linear_equiv eₘ eₙ).symm M = λ i j, M (eₘ i) (eₙ j) :=
rfl

lemma reindex_mul [semiring R]
  (eₘ : m ≃ m') (eₙ : n ≃ n') (eₗ : l ≃ l') (M : matrix m n R) (N : matrix n l R) :
  (reindex_linear_equiv eₘ eₙ M) ⬝ (reindex_linear_equiv eₙ eₗ N) = reindex_linear_equiv eₘ eₗ (M ⬝ N) :=
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
{ map_mul'  := λ M N, by simp only [reindex_mul, linear_equiv.to_fun_apply, mul_eq_mul],
  commutes' := λ r, by { ext, simp [algebra_map, algebra.to_ring_hom], by_cases h : i = j; simp [h], },
..(reindex_linear_equiv e e) }

@[simp] lemma reindex_alg_equiv_apply [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix m m R) :
  reindex_alg_equiv e M = λ i j, M (e.symm i) (e.symm j) :=
rfl

@[simp] lemma reindex_alg_equiv_symm_apply [comm_semiring R] [decidable_eq m] [decidable_eq n]
  (e : m ≃ n) (M : matrix n n R) :
  (reindex_alg_equiv e).symm M = λ i j, M (e i) (e j) :=
rfl

lemma reindex_transpose (eₘ : m ≃ m') (eₙ : n ≃ n') (M : matrix m n R) :
  (reindex eₘ eₙ M)ᵀ = (reindex eₙ eₘ Mᵀ) :=
rfl

end reindexing

end matrix

namespace linear_map

open_locale matrix

/-- The trace of an endomorphism given a basis. -/
def trace_aux (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) :
  (M →ₗ[R] M) →ₗ[R] R :=
(matrix.trace ι R R).comp $ linear_equiv_matrix hb hb

@[simp] lemma trace_aux_def (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b) (f : M →ₗ[R] M) :
  trace_aux R hb f = matrix.trace ι R R (linear_equiv_matrix hb hb f) :=
rfl

theorem trace_aux_eq' (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b)
  {κ : Type w} [decidable_eq κ] [fintype κ] {c : κ → M} (hc : is_basis R c) :
  trace_aux R hb = trace_aux R hc :=
linear_map.ext $ λ f,
calc  matrix.trace ι R R (linear_equiv_matrix hb hb f)
    = matrix.trace ι R R (linear_equiv_matrix hb hb ((linear_map.id.comp f).comp linear_map.id)) :
  by rw [linear_map.id_comp, linear_map.comp_id]
... = matrix.trace ι R R (linear_equiv_matrix hc hb linear_map.id ⬝
        linear_equiv_matrix hc hc f ⬝
        linear_equiv_matrix hb hc linear_map.id) :
  by rw [matrix.linear_equiv_matrix_comp _ hc, matrix.linear_equiv_matrix_comp _ hc]
... = matrix.trace κ R R (linear_equiv_matrix hc hc f ⬝
        linear_equiv_matrix hb hc linear_map.id ⬝
        linear_equiv_matrix hc hb linear_map.id) :
  by rw [matrix.mul_assoc, matrix.trace_mul_comm]
... = matrix.trace κ R R (linear_equiv_matrix hc hc ((f.comp linear_map.id).comp linear_map.id)) :
  by rw [matrix.linear_equiv_matrix_comp _ hb, matrix.linear_equiv_matrix_comp _ hc]
... = matrix.trace κ R R (linear_equiv_matrix hc hc f) :
  by rw [linear_map.comp_id, linear_map.comp_id]

open_locale classical

theorem trace_aux_range (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [fintype ι] {b : ι → M} (hb : is_basis R b) :
  trace_aux R hb.range = trace_aux R hb :=
linear_map.ext $ λ f, if H : 0 = 1 then eq_of_zero_eq_one H _ _ else
begin
  haveI : nontrivial R := ⟨⟨0, 1, H⟩⟩,
  change ∑ i : set.range b, _ = ∑ i : ι, _, simp_rw [matrix.diag_apply], symmetry,
  convert (equiv.of_injective _ hb.injective).sum_comp _, ext i,
  exact (linear_equiv_matrix_range hb hb f i i).symm
end

/-- where `ι` and `κ` can reside in different universes -/
theorem trace_aux_eq (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type*} [decidable_eq ι] [fintype ι] {b : ι → M} (hb : is_basis R b)
  {κ : Type*} [decidable_eq κ] [fintype κ] {c : κ → M} (hc : is_basis R c) :
  trace_aux R hb = trace_aux R hc :=
calc  trace_aux R hb
    = trace_aux R hb.range : by { rw trace_aux_range R hb, congr }
... = trace_aux R hc.range : trace_aux_eq' _ _ _
... = trace_aux R hc : by { rw trace_aux_range R hc, congr }

/-- Trace of an endomorphism independent of basis. -/
def trace (R : Type u) [comm_ring R] (M : Type v) [add_comm_group M] [module R M] :
  (M →ₗ[R] M) →ₗ[R] R :=
if H : ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M)
then trace_aux R (classical.some_spec H)
else 0

theorem trace_eq_matrix_trace (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  {ι : Type w} [fintype ι] {b : ι → M} (hb : is_basis R b) (f : M →ₗ[R] M) :
  trace R M f = matrix.trace ι R R (linear_equiv_matrix hb hb f) :=
have ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M),
from ⟨finset.univ.image b,
  by { rw [finset.coe_image, finset.coe_univ, set.image_univ], exact hb.range }⟩,
by { rw [trace, dif_pos this, ← trace_aux_def], congr' 1, apply trace_aux_eq }

theorem trace_mul_comm (R : Type u) [comm_ring R] {M : Type v} [add_comm_group M] [module R M]
  (f g : M →ₗ[R] M) : trace R M (f * g) = trace R M (g * f) :=
if H : ∃ s : finset M, is_basis R (λ x, x : (↑s : set M) → M) then let ⟨s, hb⟩ := H in
by { simp_rw [trace_eq_matrix_trace R hb, matrix.linear_equiv_matrix_mul], apply matrix.trace_mul_comm }
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
  apply linear_equiv.finite_dimensional (linear_equiv_matrix hbV hbW).symm,
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
  rw [linear_equiv.findim_eq (linear_equiv_matrix hbV hbW), matrix.findim_matrix,
    finite_dimensional.findim_eq_card_basis hbV, finite_dimensional.findim_eq_card_basis hbW,
    mul_comm],
end

end finite_dimensional
end linear_map

/-- The natural equivalence between linear endomorphisms of finite free modules and square matrices
is compatible with the algebra structures. -/
def alg_equiv_matrix' {R : Type v} [comm_ring R] [decidable_eq n] :
  module.End R (n → R) ≃ₐ[R] matrix n n R :=
{ map_mul'  := matrix.comp_to_matrix_mul,
  map_add'  := linear_equiv_matrix'.map_add,
  commutes' := λ r, by { change (r • (linear_map.id : module.End R _)).to_matrix = r • 1,
                         rw ←linear_map.to_matrix_id, refl, },
  ..linear_equiv_matrix' }

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
def alg_equiv_matrix {R : Type v} {M : Type w}
  [comm_ring R] [add_comm_group M] [module R M] [decidable_eq n] {b : n → M} (h : is_basis R b) :
  module.End R M ≃ₐ[R] matrix n n R :=
h.equiv_fun.alg_conj.trans alg_equiv_matrix'
