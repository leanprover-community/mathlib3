/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.matrix_algebra
import data.polynomial.algebra_map

/-!
# Algebra isomorphism between matrices of polynomials and polynomials of matrices

Given `[comm_ring R] [ring A] [algebra R A]`
we show `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`.
Combining this with the isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)` proved earlier
in `ring_theory.matrix_algebra`, we obtain the algebra isomorphism
```
def mat_poly_equiv :
  matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R)
```
which is characterized by
```
coeff (mat_poly_equiv m) k i j = coeff (m i j) k
```

We will use this algebra isomorphism to prove the Cayley-Hamilton theorem.
-/

universes u v w

open_locale tensor_product

open polynomial
open tensor_product
open algebra.tensor_product (alg_hom_of_linear_map_tensor_product include_left)

noncomputable theory

variables (R A : Type*)
variables [comm_semiring R]
variables [semiring A] [algebra R A]

namespace poly_equiv_tensor

/--
(Implementation detail).
The bare function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`, on pure tensors.
-/
def to_fun (a : A) (p : polynomial R) : polynomial A :=
p.sum (λ n r, monomial n (a * algebra_map R A r))

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a linear map in the second factor.
-/
def to_fun_linear_right (a : A) : polynomial R →ₗ[R] polynomial A :=
{ to_fun := to_fun R A a,
  map_smul' := λ r p,
  begin
    dsimp [to_fun],
    rw finsupp.sum_smul_index,
    { dsimp [finsupp.sum],
      rw finset.smul_sum,
      apply finset.sum_congr rfl,
      intros k hk,
      rw [monomial_eq_smul_X, monomial_eq_smul_X, algebra.smul_def, ← C_mul', ← C_mul',
          ← mul_assoc],
      congr' 1,
      rw [← algebra.commutes, ← algebra.commutes],
      simp only [ring_hom.map_mul, polynomial.algebra_map_apply, mul_assoc], },
    { intro i, simp only [ring_hom.map_zero, mul_zero, monomial_zero_right] },
  end,
  map_add' := λ p q,
  begin
    simp only [to_fun],
    rw finsupp.sum_add_index,
    { simp only [monomial_zero_right, forall_const, ring_hom.map_zero, mul_zero], },
    { intros i r s, simp only [ring_hom.map_add, mul_add, monomial_add], },
  end, }

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a bilinear function of two arguments.
-/
def to_fun_bilinear : A →ₗ[R] polynomial R →ₗ[R] polynomial A :=
{ to_fun := to_fun_linear_right R A,
  map_smul' := by {
    intros, unfold to_fun_linear_right,
    congr, simp only [linear_map.coe_mk],
    unfold to_fun finsupp.sum monomial,
    simp_rw [finset.smul_sum, finsupp.smul_single,  ← algebra.smul_mul_assoc],
    refl },
  map_add' := by {
    intros, unfold to_fun_linear_right,
    congr, simp only [linear_map.coe_mk],
    unfold to_fun finsupp.sum monomial,
    simp_rw [← finset.sum_add_distrib, ← finsupp.single_add, ← add_mul],
    refl } }

/--
(Implementation detail).
The function underlying `A ⊗[R] polynomial R →ₐ[R] polynomial A`,
as a linear map.
-/
def to_fun_linear : A ⊗[R] polynomial R →ₗ[R] polynomial A :=
tensor_product.lift (to_fun_bilinear R A)

-- We apparently need to provide the decidable instance here
-- in order to successfully rewrite by this lemma.
lemma to_fun_linear_mul_tmul_mul_aux_1
  (p : polynomial R) (k : ℕ) (h : decidable (¬p.coeff k = 0)) (a : A) :
  ite (¬coeff p k = 0) (a * (algebra_map R A) (coeff p k)) 0 = a * (algebra_map R A) (coeff p k) :=
by { classical, split_ifs; simp *, }

lemma to_fun_linear_mul_tmul_mul_aux_2 (k : ℕ) (a₁ a₂ : A) (p₁ p₂ : polynomial R) :
  a₁ * a₂ * (algebra_map R A) ((p₁ * p₂).coeff k) =
    (finset.nat.antidiagonal k).sum
      (λ x, a₁ * (algebra_map R A) (coeff p₁ x.1) * (a₂ * (algebra_map R A) (coeff p₂ x.2))) :=
begin
  simp_rw [mul_assoc, algebra.commutes, ←finset.mul_sum, mul_assoc, ←finset.mul_sum],
  congr,
  simp_rw [algebra.commutes (coeff p₂ _), coeff_mul, ring_hom.map_sum, ring_hom.map_mul],
end

lemma to_fun_linear_mul_tmul_mul (a₁ a₂ : A) (p₁ p₂ : polynomial R) :
  (to_fun_linear R A) ((a₁ * a₂) ⊗ₜ[R] p₁ * p₂) =
    (to_fun_linear R A) (a₁ ⊗ₜ[R] p₁) * (to_fun_linear R A) (a₂ ⊗ₜ[R] p₂) :=
begin
  dsimp [to_fun_linear],
  simp only [lift.tmul],
  dsimp [to_fun_bilinear, to_fun_linear_right, to_fun],
  ext k,
  -- TODO This is a bit annoying: the polynomial API is breaking down.
  have apply_eq_coeff : ∀ {p : ℕ →₀ R} {n : ℕ}, p n = coeff p n := by { intros, refl },
  simp_rw [coeff_sum, coeff_monomial, finsupp.sum, finset.sum_ite_eq', finsupp.mem_support_iff,
    ne.def, coeff_mul, finset_sum_coeff, coeff_monomial,
    finset.sum_ite_eq', finsupp.mem_support_iff, ne.def,
    mul_ite, mul_zero, ite_mul, zero_mul, apply_eq_coeff],
  simp_rw [ite_mul_zero_left (¬coeff p₁ _ = 0) (a₁ * (algebra_map R A) (coeff p₁ _))],
  simp_rw [ite_mul_zero_right (¬coeff p₂ _ = 0) _ (_ * _)],
  simp_rw [to_fun_linear_mul_tmul_mul_aux_1, to_fun_linear_mul_tmul_mul_aux_2],
end

lemma to_fun_linear_algebra_map_tmul_one (r : R) :
  (to_fun_linear R A) ((algebra_map R A) r ⊗ₜ[R] 1) = (algebra_map R (polynomial A)) r :=
begin
  dsimp [to_fun_linear],
  simp only [lift.tmul],
  dsimp [to_fun_bilinear, to_fun_linear_right, to_fun],
  rw [← C_1, ←monomial_zero_left, monomial, finsupp.sum_single_index],
  { simp, refl, },
  { simp, },
end

/--
(Implementation detail).
The algebra homomorphism `A ⊗[R] polynomial R →ₐ[R] polynomial A`.
-/
def to_fun_alg_hom : A ⊗[R] polynomial R →ₐ[R] polynomial A :=
alg_hom_of_linear_map_tensor_product
  (to_fun_linear R A)
  (to_fun_linear_mul_tmul_mul R A)
  (to_fun_linear_algebra_map_tmul_one R A)

@[simp] lemma to_fun_alg_hom_apply_tmul (a : A) (p : polynomial R) :
  to_fun_alg_hom R A (a ⊗ₜ[R] p) = p.sum (λ n r, monomial n (a * (algebra_map R A) r)) :=
by simp [to_fun_alg_hom, to_fun_linear, to_fun_bilinear, to_fun_linear_right, to_fun]

/--
(Implementation detail.)

The bare function `polynomial A → A ⊗[R] polynomial R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def inv_fun (p : polynomial A) : A ⊗[R] polynomial R :=
p.eval₂
  (include_left : A →ₐ[R] A ⊗[R] polynomial R)
  ((1 : A) ⊗ₜ[R] (X : polynomial R))

@[simp]
lemma inv_fun_add {p q} : inv_fun R A (p + q) = inv_fun R A p + inv_fun R A q :=
by simp only [inv_fun, eval₂_add]

lemma left_inv (x : A ⊗ polynomial R) :
  inv_fun R A ((to_fun_alg_hom R A) x) = x :=
begin
  apply tensor_product.induction_on x,
  { simp [inv_fun], },
  { intros a p, dsimp only [inv_fun],
    rw [to_fun_alg_hom_apply_tmul, eval₂_sum],
    simp_rw [eval₂_monomial, alg_hom.coe_to_ring_hom, algebra.tensor_product.tmul_pow, one_pow,
      algebra.tensor_product.include_left_apply, algebra.tensor_product.tmul_mul_tmul,
      mul_one, one_mul, ←algebra.commutes, ←algebra.smul_def'', smul_tmul],
    rw [finsupp.sum, ←tmul_sum],
    conv_rhs { rw [←sum_C_mul_X_eq p], },
    simp only [algebra.smul_def''],
    refl, },
  { intros p q hp hq,
    simp only [alg_hom.map_add, inv_fun_add, hp, hq], },
end

lemma right_inv (x : polynomial A) :
  (to_fun_alg_hom R A) (inv_fun R A x) = x :=
begin
  apply polynomial.induction_on' x,
  { intros p q hp hq, simp only [inv_fun_add, alg_hom.map_add, hp, hq], },
  { intros n a,
    rw [inv_fun, eval₂_monomial, alg_hom.coe_to_ring_hom, algebra.tensor_product.include_left_apply,
      algebra.tensor_product.tmul_pow, one_pow, algebra.tensor_product.tmul_mul_tmul,
      mul_one, one_mul, to_fun_alg_hom_apply_tmul, ←monomial_one_eq_X_pow],
    dsimp [monomial],
    rw [finsupp.sum_single_index]; simp, }
end

/--
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] polynomial R) ≃ polynomial A`.
-/
def equiv : (A ⊗[R] polynomial R) ≃ polynomial A :=
{ to_fun := to_fun_alg_hom R A,
  inv_fun := inv_fun R A,
  left_inv := left_inv R A,
  right_inv := right_inv R A, }

end poly_equiv_tensor

open poly_equiv_tensor

/--
The `R`-algebra isomorphism `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`.
-/
def poly_equiv_tensor : polynomial A ≃ₐ[R] (A ⊗[R] polynomial R) :=
alg_equiv.symm
{ ..(poly_equiv_tensor.to_fun_alg_hom R A), ..(poly_equiv_tensor.equiv R A) }

@[simp]
lemma poly_equiv_tensor_apply (p : polynomial A) :
  poly_equiv_tensor R A p =
    p.eval₂ (include_left : A →ₐ[R] A ⊗[R] polynomial R) ((1 : A) ⊗ₜ[R] (X : polynomial R)) :=
rfl

@[simp]
lemma poly_equiv_tensor_symm_apply_tmul (a : A) (p : polynomial R) :
  (poly_equiv_tensor R A).symm (a ⊗ₜ p) = p.sum (λ n r, monomial n (a * algebra_map R A r)) :=
begin
  simp [poly_equiv_tensor, to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear],
  refl,
end

open matrix
open_locale big_operators

variables {R}
variables {n : Type w} [fintype n] [decidable_eq n]

/--
The algebra isomorphism stating "matrices of polynomials are the same as polynomials of matrices".

(You probably shouldn't attempt to use this underlying definition ---
it's an algebra equivalence, and characterised extensionally by the lemma
`mat_poly_equiv_coeff_apply` below.)
-/
noncomputable def mat_poly_equiv :
  matrix n n (polynomial R) ≃ₐ[R] polynomial (matrix n n R) :=
(((matrix_equiv_tensor R (polynomial R) n)).trans
  (algebra.tensor_product.comm R _ _)).trans
  (poly_equiv_tensor R (matrix n n R)).symm

open finset

lemma mat_poly_equiv_coeff_apply_aux_1 (i j : n) (k : ℕ) (x : R) :
  mat_poly_equiv (std_basis_matrix i j $ monomial k x) =
    monomial k (std_basis_matrix i j x) :=
begin
  simp only [mat_poly_equiv, alg_equiv.trans_apply,
    matrix_equiv_tensor_apply_std_basis],
  apply (poly_equiv_tensor R (matrix n n R)).injective,
  simp only [alg_equiv.apply_symm_apply],
  convert algebra.tensor_product.comm_tmul _ _ _ _ _,
  simp only [poly_equiv_tensor_apply],
  convert eval₂_monomial _ _,
  simp only [algebra.tensor_product.tmul_mul_tmul, one_pow, one_mul, matrix.mul_one,
    algebra.tensor_product.tmul_pow, algebra.tensor_product.include_left_apply, mul_eq_mul],
  rw [monomial_eq_smul_X, ← tensor_product.smul_tmul],
  congr, ext, simp, dsimp, simp,
end

lemma mat_poly_equiv_coeff_apply_aux_2
  (i j : n) (p : polynomial R) (k : ℕ) :
  coeff (mat_poly_equiv (std_basis_matrix i j p)) k =
    std_basis_matrix i j (coeff p k) :=
begin
  apply polynomial.induction_on' p,
  { intros p q hp hq, ext,
    simp [hp, hq, coeff_add, add_val, std_basis_matrix_add], },
  { intros k x,
    simp only [mat_poly_equiv_coeff_apply_aux_1, coeff_monomial],
    split_ifs; { funext, simp, }, }
end

@[simp] lemma mat_poly_equiv_coeff_apply
  (m : matrix n n (polynomial R)) (k : ℕ) (i j : n) :
  coeff (mat_poly_equiv m) k i j = coeff (m i j) k :=
begin
  apply matrix.induction_on' m,
  { simp, },
  { intros p q hp hq, simp [hp, hq], },
  { intros i' j' x,
    erw mat_poly_equiv_coeff_apply_aux_2,
    dsimp [std_basis_matrix],
    split_ifs,
    { rcases h with ⟨rfl, rfl⟩, simp [std_basis_matrix], },
    { simp [std_basis_matrix, h], }, },
end

@[simp] lemma mat_poly_equiv_symm_apply_coeff
  (p : polynomial (matrix n n R)) (i j : n) (k : ℕ) :
  coeff (mat_poly_equiv.symm p i j) k = coeff p k i j :=
begin
  have t : p = mat_poly_equiv
    (mat_poly_equiv.symm p) := by simp,
  conv_rhs { rw t, },
  simp only [mat_poly_equiv_coeff_apply],
end

lemma mat_poly_equiv_smul_one (p : polynomial R) :
  mat_poly_equiv (p • 1) = p.map (algebra_map R (matrix n n R)) :=
begin
  ext m i j,
  simp only [coeff_map, one_val, algebra_map_matrix_val, mul_boole,
    smul_val, mat_poly_equiv_coeff_apply],
  split_ifs; simp,
end
