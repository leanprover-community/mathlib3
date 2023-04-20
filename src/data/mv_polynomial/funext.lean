/-
Copyright (c) 2020 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin
-/
import data.polynomial.ring_division
import data.mv_polynomial.rename
import ring_theory.polynomial.basic
import data.mv_polynomial.polynomial

/-!
## Function extensionality for multivariate polynomials

In this file we show that two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables.

# Main declaration

* `mv_polynomial.funext`: two polynomials `φ ψ : mv_polynomial σ R`
  over an infinite integral domain `R` are equal if `eval x φ = eval x ψ` for all `x : σ → R`.

-/

namespace mv_polynomial

variables {R : Type*} [comm_ring R] [is_domain R] [infinite R]

private lemma funext_fin {n : ℕ} {p : mv_polynomial (fin n) R}
  (h : ∀ x : fin n → R, eval x p = 0) : p = 0 :=
begin
  induction n with n ih,
  { apply (mv_polynomial.is_empty_ring_equiv R (fin 0)).injective,
    rw [ring_equiv.map_zero],
    convert h _, },
  { apply (fin_succ_equiv R n).injective,
    simp only [alg_equiv.map_zero],
    refine polynomial.funext (λ q, _),
    rw [polynomial.eval_zero],
    apply ih (λ x, _),
    calc _ = _ : eval_polynomial_eval_fin_succ_equiv p _ _
       ... = 0 : h _, }
end

/-- Two multivariate polynomials over an infinite integral domain are equal
if they are equal upon evaluating them on an arbitrary assignment of the variables. -/
lemma funext {σ : Type*} {p q : mv_polynomial σ R}
  (h : ∀ x : σ → R, eval x p = eval x q) : p = q :=
begin
  suffices : ∀ p, (∀ (x : σ → R), eval x p = 0) → p = 0,
  { rw [← sub_eq_zero, this (p - q)], simp only [h, ring_hom.map_sub, forall_const, sub_self] },
  clear h p q,
  intros p h,
  obtain ⟨n, f, hf, p, rfl⟩ := exists_fin_rename p,
  suffices : p = 0, { rw [this, alg_hom.map_zero] },
  apply funext_fin,
  intro x,
  classical,
  convert h (function.extend f x 0),
  simp only [eval, eval₂_hom_rename, function.extend_comp hf]
end

lemma funext_iff {σ : Type*} {p q : mv_polynomial σ R} :
  p = q ↔ (∀ x : σ → R, eval x p = eval x q) :=
⟨by rintro rfl; simp only [forall_const, eq_self_iff_true], funext⟩

end mv_polynomial
