/-
Copyright (c) 2020 Jujian Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jujian Zhang
-/

import data.polynomial
import analysis.calculus.deriv

/-!
TODO
-/

theorem polynomial.aeval_nat_cast'
  {R A : Type*} [comm_semiring R] [nontrivially_normed_field A] [algebra R A]
  (f : polynomial R) (k : ℕ) :
  polynomial.aeval (k:A) f = algebra_map _ _ (polynomial.eval (k : R) f) :=
begin
  rw [polynomial.aeval_def, polynomial.eval₂_eq_eval_map, polynomial.eval_nat_cast_map],
end

theorem polynomial.eval₂_deriv
  {R S : Type*} [semiring R] [nontrivially_normed_field S] (f : R →+* S) (p : polynomial R) :
  (deriv (λ x : S, (p.eval₂ f x))) = (λ x, polynomial.eval₂ f x p.derivative) :=
begin
  ext y,
  simp_rw [polynomial.eval₂_eq_eval_map, polynomial.deriv, polynomial.derivative_map],
end

theorem polynomial.aeval_deriv
  {R A : Type*} [comm_semiring R] [nontrivially_normed_field A] [algebra R A]
  (f : polynomial R) (a : A) :
  (deriv (λ x : A, polynomial.aeval x f)) a = polynomial.aeval a (f.derivative) :=
begin
  simp_rw [polynomial.aeval_def, polynomial.eval₂_deriv],
end

open_locale big_operators
open_locale polynomial
open polynomial

lemma differentiable_aeval (f : ℤ[X]) :
  differentiable ℝ (λ (x : ℝ), (aeval x) (f)) :=
begin
  simp only [aeval_def, eval₂_eq_eval_map],
  apply polynomial.differentiable,
end

lemma aeval_eq_sum_support {R A : Type*} [comm_semiring R] [comm_semiring A] [algebra R A]
  (x : A) (f : R[X]) :
  aeval x f = ∑ i in f.support, (f.coeff i) • x ^ i:=
begin
  simp_rw [aeval_def, eval₂_eq_sum, polynomial.sum, algebra.smul_def],
end
