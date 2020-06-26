/-
Copyright (c) 2020 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.tensor_product
import data.matrix.basic

/-!
We provide the `R`-algebra structure on `matrix n n A` when `A` is an `R`-algebra,
and show `matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R)`.
-/

universes u v w

open_locale tensor_product
open tensor_product
open algebra.tensor_product

variables {R : Type u} [comm_ring R]
variables {A : Type v} [comm_ring A] [algebra R A]
variables {n : Type w} [fintype n] [decidable_eq n]

instance : algebra R (matrix n n A) :=
{ commutes' := λ r x, begin ext, simp [matrix.scalar], end,
  smul_def' := λ r x, begin ext, simp [matrix.scalar, algebra.smul_def'' r], end,
  ..((matrix.scalar n).comp (algebra_map R A)) }

lemma algebra_matrix_matrix_val {r : R} {i j : n} :
  algebra_map R (matrix n n A) r i j = if i = j then algebra_map R A r else 0 :=
begin
  dsimp [algebra_map, algebra.to_ring_hom, matrix.scalar],
  split_ifs with h; simp [h, matrix.one_val_ne],
end

variables (R A n)

def foo (a : A) (m : matrix n n R) : matrix n n A :=
λ i j, a * algebra_map R A (m i j)

def foo2 (a : A) : matrix n n R →ₗ[R] matrix n n A :=
{ to_fun := foo R A n a,
  map_add' := λ x y, begin dsimp only [foo], ext, simp [mul_add], end,
  map_smul' := λ r x, begin dsimp only [foo], ext, simp, rw algebra.smul_def r, rw mul_left_comm, end, }

def foo3 : A →ₗ[R] matrix n n R →ₗ[R] matrix n n A :=
{ to_fun := foo2 R A n,
  map_add' := λ x y, begin dsimp only [foo2], ext, dsimp [foo], simp [add_mul], end,
  map_smul' := λ r x, begin dsimp only [foo2], ext, dsimp [foo], simp, end, }

def foo4 : A ⊗[R] matrix n n R →ₗ[R] matrix n n A :=
tensor_product.lift (foo3 R A n)

def foo5 : (A ⊗[R] matrix n n R) →ₐ[R] matrix n n A :=
alg_hom_of_linear_map_tensor_product (foo4 R A n)
begin
  intros, ext, simp [foo4, foo3, foo2, foo], simp [ring_hom.map_matrix_mul],
  rw [←_root_.mul_assoc, mul_comm a₁ a₂],
end
begin
  intros, ext, simp [foo4, foo3, foo2, foo],
  simp [matrix.one_val, algebra_matrix_matrix_val],
  split_ifs; simp,
end

@[simp] lemma foo5_apply (a : A) (m : matrix n n R) :
  foo5 R A n (a ⊗ₜ m) = λ i j, a * algebra_map R A (m i j) :=
begin
  dsimp [foo5, alg_hom_of_linear_map_tensor_product, foo4],
  simp,
  refl,
end

open_locale big_operators

def bar (M : matrix n n A) : A ⊗[R] matrix n n R :=
∑ (p : n × n), M p.1 p.2 ⊗ₜ (λ i' j', if (i', j') = p then 1 else 0)

@[simp] lemma bar_zero : bar R A n 0 = 0 :=
by simp [bar]

@[simp] lemma bar_add (M N : matrix n n A) : bar R A n (M + N) = bar R A n M + bar R A n N :=
begin
  dsimp [bar],
  simp [add_tmul],
  simp [finset.sum_add_distrib],
end

@[simp] lemma bar_smul (a : A) (M : matrix n n A) :
  bar R A n (λ i j, a * M i j) = (a ⊗ₜ 1) * bar R A n M :=
begin
  dsimp [bar],
  simp [finset.mul_sum],
end

lemma blah (r : R) : algebra_map R A r = r • 1 :=
calc algebra_map R A r = algebra_map R A r * 1 : by simp
    ... = r • 1 : (algebra.smul_def r 1).symm


@[simp] lemma bar_algebra_map (M : matrix n n R) :
  bar R A n (λ i j, algebra_map R A (M i j)) = 1 ⊗ₜ M :=
begin
  dsimp [bar],
  simp only [blah],
  simp only [smul_tmul],
  simp only [←tmul_sum],
  dsimp [(•)],
  simp,
  congr,
  ext,
  calc
    (∑ (x : n × n), λ (i i_1 : n), ite ((i, i_1) = x) (M x.fst x.snd) 0) i j
      = (∑ (x : n × n), λ (i_1 : n), ite ((i, i_1) = x) (M x.fst x.snd) 0) j : _
     ... = (∑ (x : n × n), ite ((i, j) = x) (M x.fst x.snd) 0) : _
     ... = M i j : _,
  { apply congr_fun,
  dsimp,
    simp, },
  { simp, },
  { simp, },
end


-- How is this not in mathlib?!
lemma apply_ite {α β : Type*} (f : α → β) (P : Prop) [decidable P] (x y : α) :
  f (ite P x y) = ite P (f x) (f y) :=
by split_ifs; refl

lemma foobar (M : matrix n n A) : (foo5 R A n) (bar R A n M) = M :=
begin
  dsimp [bar],
  simp only [alg_hom.map_sum],
  simp [apply_ite (algebra_map R A)],
  ext,
  simp,
end.

lemma barfoo (M : A ⊗[R] matrix n n R) : bar R A n (foo5 R A n M) = M :=
begin
  apply tensor_product.induction_on _ _ M,
  { simp, },
  { intros a m, simp, },
  { intros x y hx hy, simp [alg_hom.map_sum, hx, hy], },
end

def e : (A ⊗[R] matrix n n R) ≃ matrix n n A :=
{ to_fun := foo5 R A n,
  inv_fun := bar R A n,
  left_inv := barfoo R A n,
  right_inv := foobar R A n, }

def matrix_equiv_tensor : matrix n n A ≃ₐ[R] (A ⊗[R] matrix n n R) :=
alg_equiv.symm { ..(foo5 R A n), ..(e R A n) }
