/-
Copyright (c) 2023 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import data.mv_polynomial.equiv
import data.polynomial.eval

/-!
# Some lemmas relating polynomials and multivariable polynomials.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

namespace mv_polynomial

variables {R S : Type*} [comm_semiring R] [comm_semiring S] {σ : Type*}

theorem polynomial_eval_eval₂
    (f : R →+* polynomial S) (g : σ → polynomial S) (p : mv_polynomial σ R) (x : S) :
    polynomial.eval x (mv_polynomial.eval₂ f g p) =
      mv_polynomial.eval₂ ((polynomial.eval_ring_hom x).comp f) (λ s, polynomial.eval x (g s)) p :=
begin
  apply mv_polynomial.induction_on p,
  { simp },
  { intros p q hp hq,
    simp [hp, hq], },
  { intros p n hp,
    simp [hp], },
end

theorem eval_polynomial_eval_fin_succ_equiv {n : ℕ}
  (f : mv_polynomial (fin (n + 1)) R) (q : mv_polynomial (fin n) R) (x : fin n → R) :
  (eval x) (polynomial.eval q (fin_succ_equiv R n f)) =
    eval (show fin (n+1) → R, from @fin.cases _ (λ _, R) (eval x q) x) f :=
begin
  simp only [fin_succ_equiv_apply, coe_eval₂_hom, eval_eval₂, polynomial_eval_eval₂],
  have : (eval x).comp ((polynomial.eval_ring_hom q).comp (polynomial.C.comp C)) = ring_hom.id _,
  { ext, simp, },
  simp only [this, eval₂_id],
  congr,
  funext i,
  refine fin.cases (by simp) (by simp) i,
end

end mv_polynomial
