/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison, Eric Wieser
-/
import data.matrix.basis
import ring_theory.tensor_product

/-!
> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/

universes u v w

open_locale tensor_product
open_locale big_operators

open tensor_product
open algebra.tensor_product
open matrix

variables {R : Type u} [comm_semiring R]
variables {A : Type v} [semiring A] [algebra R A]
variables {n : Type w}


variables (R A n)
namespace matrix_equiv_tensor

/--
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-bilinear map.
-/
def to_fun_bilinear : A →ₗ[R] matrix n n R →ₗ[R] matrix n n A :=
(algebra.lsmul R (matrix n n A)).to_linear_map.compl₂ (algebra.linear_map R A).map_matrix

@[simp] lemma to_fun_bilinear_apply (a : A) (m : matrix n n R) :
  to_fun_bilinear R A n a m = a • m.map (algebra_map R A) := rfl

/--
(Implementation detail).
The function underlying `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`,
as an `R`-linear map.
-/
def to_fun_linear : A ⊗[R] matrix n n R →ₗ[R] matrix n n A :=
tensor_product.lift (to_fun_bilinear R A n)

variables [decidable_eq n] [fintype n]

/--
The function `(A ⊗[R] matrix n n R) →ₐ[R] matrix n n A`, as an algebra homomorphism.
-/
def to_fun_alg_hom : (A ⊗[R] matrix n n R) →ₐ[R] matrix n n A :=
alg_hom_of_linear_map_tensor_product
(to_fun_linear R A n)
begin
  intros,
  simp_rw [to_fun_linear, lift.tmul, to_fun_bilinear_apply, mul_eq_mul, matrix.map_mul],
  ext,
  dsimp,
  simp_rw [matrix.mul_apply, pi.smul_apply, matrix.map_apply, smul_eq_mul, finset.mul_sum,
    _root_.mul_assoc, algebra.left_comm],
end
begin
  intros,
  simp_rw [to_fun_linear, lift.tmul, to_fun_bilinear_apply,
    matrix.map_one (algebra_map R A) (map_zero _) (map_one _), algebra_map_smul,
    algebra.algebra_map_eq_smul_one],
end

@[simp] lemma to_fun_alg_hom_apply (a : A) (m : matrix n n R) :
  to_fun_alg_hom R A n (a ⊗ₜ m) = a • m.map (algebra_map R A) :=
by simp [to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear]

/--
(Implementation detail.)

The bare function `matrix n n A → A ⊗[R] matrix n n R`.
(We don't need to show that it's an algebra map, thankfully --- just that it's an inverse.)
-/
def inv_fun (M : matrix n n A) : A ⊗[R] matrix n n R :=
∑ (p : n × n), M p.1 p.2 ⊗ₜ (std_basis_matrix p.1 p.2 1)

@[simp] lemma inv_fun_zero : inv_fun R A n 0 = 0 :=
by simp [inv_fun]

@[simp] lemma inv_fun_add (M N : matrix n n A) :
  inv_fun R A n (M + N) = inv_fun R A n M + inv_fun R A n N :=
by simp [inv_fun, add_tmul, finset.sum_add_distrib]

@[simp] lemma inv_fun_smul (a : A) (M : matrix n n A) :
  inv_fun R A n (a • M) = (a ⊗ₜ 1) * inv_fun R A n M :=
by simp [inv_fun,finset.mul_sum]

@[simp] lemma inv_fun_algebra_map (M : matrix n n R) :
  inv_fun R A n (M.map (algebra_map R A)) = 1 ⊗ₜ M :=
begin
  dsimp [inv_fun],
  simp only [algebra.algebra_map_eq_smul_one, smul_tmul, ←tmul_sum, mul_boole],
  congr,
  conv_rhs {rw matrix_eq_sum_std_basis M},
  convert finset.sum_product, simp,
end

lemma right_inv (M : matrix n n A) : (to_fun_alg_hom R A n) (inv_fun R A n M) = M :=
begin
  simp only [inv_fun, alg_hom.map_sum, std_basis_matrix, apply_ite ⇑(algebra_map R A), smul_eq_mul,
    mul_boole, to_fun_alg_hom_apply, ring_hom.map_zero, ring_hom.map_one, matrix.map_apply,
    pi.smul_def],
  convert finset.sum_product, apply matrix_eq_sum_std_basis,
end

lemma left_inv (M : A ⊗[R] matrix n n R) : inv_fun R A n (to_fun_alg_hom R A n M) = M :=
begin
  induction M using tensor_product.induction_on with a m x y hx hy,
  { simp, },
  { simp, },
  { simp [alg_hom.map_sum, hx, hy], },
end

/--
(Implementation detail)

The equivalence, ignoring the algebra structure, `(A ⊗[R] matrix n n R) ≃ matrix n n A`.
-/
def equiv : (A ⊗[R] matrix n n R) ≃ matrix n n A :=
{ to_fun := to_fun_alg_hom R A n,
  inv_fun := inv_fun R A n,
  left_inv := left_inv R A n,
  right_inv := right_inv R A n, }

end matrix_equiv_tensor

variables [fintype n] [decidable_eq n]

/--
The `R`-algebra isomorphism `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/
def matrix_equiv_tensor : matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R) :=
alg_equiv.symm { ..(matrix_equiv_tensor.to_fun_alg_hom R A n), ..(matrix_equiv_tensor.equiv R A n) }

open matrix_equiv_tensor

@[simp] lemma matrix_equiv_tensor_apply (M : matrix n n A) :
  matrix_equiv_tensor R A n M =
    ∑ (p : n × n), M p.1 p.2 ⊗ₜ (std_basis_matrix p.1 p.2 1) :=
rfl

@[simp] lemma matrix_equiv_tensor_apply_std_basis (i j : n) (x : A):
  matrix_equiv_tensor R A n (std_basis_matrix i j x) =
    x ⊗ₜ (std_basis_matrix i j 1) :=
begin
  have t : ∀ (p : n × n), (i = p.1 ∧ j = p.2) ↔ (p = (i, j)) := by tidy,
  simp [ite_tmul, t, std_basis_matrix],
end

@[simp] lemma matrix_equiv_tensor_apply_symm (a : A) (M : matrix n n R) :
  (matrix_equiv_tensor R A n).symm (a ⊗ₜ M) =
    M.map (λ x, a * algebra_map R A x) :=
begin
  simp [matrix_equiv_tensor, to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear],
  refl,
end
