/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.tensor_product
import data.polynomial

/-!
We show `polynomial A ≃ₐ[R] (A ⊗[R] polynomial R)`.
-/

universes u v

open_locale tensor_product

open polynomial
open tensor_product
open algebra.tensor_product

noncomputable theory

variables (R : Type u) [comm_ring R]
variables (A : Type v) [ring A] [algebra R A]

-- TODO move this back to `polynomial.lean`?
instance turkle : algebra R (polynomial A) := add_monoid_algebra.algebra

namespace polynomial_equiv_tensor

def to_fun (a : A) (p : polynomial R) : polynomial A :=
p.sum (λ n r, monomial n (a * algebra_map R A r))

def to_fun_linear_right (a : A) : polynomial R →ₗ[R] polynomial A :=
{ to_fun := to_fun R A a,
  map_smul' := sorry,
  map_add' := sorry, }

def to_fun_bilinear : A →ₗ[R] polynomial R →ₗ[R] polynomial A :=
{ to_fun := to_fun_linear_right R A,
  map_smul' := sorry,
  map_add' := sorry, }

def to_fun_linear : A ⊗[R] polynomial R →ₗ[R] polynomial A :=
tensor_product.lift (to_fun_bilinear R A)

def to_fun_alg_hom : A ⊗[R] polynomial R →ₐ[R] polynomial A :=
alg_hom_of_linear_map_tensor_product (to_fun_linear R A) sorry sorry

def inv_fun (p : polynomial A) : A ⊗[R] polynomial R :=
p.eval₂ include_left ((1 : A) ⊗ₜ[R] (X : polynomial R))

def equiv : (A ⊗[R] polynomial R) ≃ polynomial A :=
{ to_fun := to_fun_alg_hom R A,
  inv_fun := inv_fun R A,
  left_inv := sorry,
  right_inv := sorry, }

end polynomial_equiv_tensor

open polynomial_equiv_tensor

def polynomial_equiv_tensor : polynomial A ≃ₐ[R] (A ⊗[R] polynomial R) :=
alg_equiv.symm { ..(polynomial_equiv_tensor.to_fun_alg_hom R A), ..(polynomial_equiv_tensor.equiv R A) }

-- TODO update these if the definitions get changed above!

@[simp]
lemma polynomial_equiv_tensor_apply (p : polynomial A) :
  polynomial_equiv_tensor R A p = p.eval₂ include_left ((1 : A) ⊗ₜ[R] (X : polynomial R)) :=
rfl

@[simp]
lemma polynomial_equiv_tensor_symm_apply_tmul (a : A) (p : polynomial R) :
  (polynomial_equiv_tensor R A).symm (a ⊗ₜ p) = p.sum (λ n r, monomial n (a * algebra_map R A r)) :=
begin
  simp [polynomial_equiv_tensor, to_fun_alg_hom, alg_hom_of_linear_map_tensor_product, to_fun_linear],
  refl,
end
