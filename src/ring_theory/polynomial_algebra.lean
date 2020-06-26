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

variables {R : Type u} [comm_ring R]
variables {A : Type v} [ring A] [algebra R A]

instance : module R (polynomial A) := module.restrict_scalars' R A (polynomial A)
def f : algebra R (polynomial R) := by apply_instance
#print polynomial.polynomial
def to_fun (a : A) (p : polynomial R) : polynomial A :=
p.sum (λ n r, monomial n (a * algebra_map R A r))

def to_fun_linear_right (a : A) : polynomial R →ₗ[R] polynomial A :=
{ to_fun := to_fun a,
  map_smul' := sorry,
  map_add' := sorry, }

def to_fun_bilinear : A →ₗ[R] polynomial R →ₗ[R] polynomial A :=
{ to_fun := to_fun_linear_right,
  map_smul' := sorry,
  map_add' := sorry, }

def to_fun_linear : A ⊗[R] polynomial R →ₗ[R] polynomial A :=
tensor_product.lift to_fun_bilinear

def to_fun_alg_hom : A ⊗[R] polynomial R →ₐ[R] polynomial A :=
alg_hom_of_linear_map_tensor_product to_fun_linear sorry sorry

def inv_fun (p : polynomial A) : A ⊗[R] polynomial R :=
p.eval₂ include_left ((1 : A) ⊗ₜ[R] (X : polynomial R))

def bar2 : polynomial A →ₗ[R] A ⊗[R] polynomial R :=
{ to_fun := bar, }

def bar3 : polynomial A →ₐ[R] A ⊗[R] polynomial R :=
{ to_fun := bar, }

def polynomial_equiv_tensor : polynomial A ≃ₐ[R] (A ⊗[R] polynomial R) :=
sorry
