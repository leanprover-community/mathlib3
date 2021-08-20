/-
Copyright (c) 2018 Chris Hughes. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Hughes, Johannes Hölzl, Scott Morrison, Jens Wagemaker
-/
import data.polynomial.derivative
import tactic.ring_exp

/-!
# Theory of univariate polynomials

The main def is `binom_expansion`.
-/

noncomputable theory

namespace polynomial
universes u v w x y z
variables {R : Type u} {S : Type v} {T : Type w} {ι : Type x} {k : Type y} {A : Type z}
  {a b : R} {m n : ℕ}

section identities

/- @TODO: pow_add_expansion and pow_sub_pow_factor are not specific to polynomials.
  These belong somewhere else. But not in group_power because they depend on tactic.ring_exp

Maybe use data.nat.choose to prove it.
 -/

def pow_add_expansion {R : Type*} [comm_semiring R] (x y : R) : ∀ (n : ℕ),
  {k // (x + y)^n = x^n + n*x^(n-1)*y + k * y^2}
| 0 := ⟨0, by simp⟩
| 1 := ⟨0, by simp⟩
| (n+2) :=
  begin
    cases pow_add_expansion (n+1) with z hz,
    existsi x*z + (n+1)*x^n+z*y,
    calc (x + y) ^ (n + 2) = (x + y) * (x + y) ^ (n + 1) : by ring_exp
    ... = (x + y) * (x ^ (n + 1) + ↑(n + 1) * x ^ (n + 1 - 1) * y + z * y ^ 2) : by rw hz
    ... = x ^ (n + 2) + ↑(n + 2) * x ^ (n + 1) * y + (x*z + (n+1)*x^n+z*y) * y ^ 2 :
      by { push_cast, ring_exp! }
  end

variables [comm_ring R]

private def poly_binom_aux1 (x y : R) (e : ℕ) (a : R) :
  {k : R // a * (x + y)^e = a * (x^e + e*x^(e-1)*y + k*y^2)} :=
begin
  existsi (pow_add_expansion x y e).val,
  congr,
  apply (pow_add_expansion _ _ _).property
end

private lemma poly_binom_aux2 (f : polynomial R) (x y : R) :
  f.eval (x + y) = f.sum (λ e a, a * (x^e + e*x^(e-1)*y + (poly_binom_aux1 x y e a).val*y^2)) :=
begin
  unfold eval eval₂, congr' with n z,
  apply (poly_binom_aux1 x y _ _).property
end

private lemma poly_binom_aux3 (f : polynomial R) (x y : R) : f.eval (x + y) =
  f.sum (λ e a, a * x^e) +
  f.sum (λ e a, (a * e * x^(e-1)) * y) +
  f.sum (λ e a, (a *(poly_binom_aux1 x y e a).val)*y^2) :=
by { rw poly_binom_aux2, simp [left_distrib, sum_add, mul_assoc] }

def binom_expansion (f : polynomial R) (x y : R) :
  {k : R // f.eval (x + y) = f.eval x + (f.derivative.eval x) * y + k * y^2} :=
begin
  existsi f.sum (λ e a, a *((poly_binom_aux1 x y e a).val)),
  rw poly_binom_aux3,
  congr,
  { rw [←eval_eq_sum], },
  { rw derivative_eval, exact finset.sum_mul.symm },
  { exact finset.sum_mul.symm }
end

def pow_sub_pow_factor (x y : R) : Π (i : ℕ), {z : R // x^i - y^i = z * (x - y)}
| 0 := ⟨0, by simp⟩
| 1 := ⟨1, by simp⟩
| (k+2) :=
  begin
    cases @pow_sub_pow_factor (k+1) with z hz,
    existsi z*x + y^(k+1),
    calc x ^ (k + 2) - y ^ (k + 2)
        = x * (x ^ (k + 1) - y ^ (k + 1)) + (x * y ^ (k + 1) - y ^ (k + 2)) : by ring_exp
    ... = x * (z * (x - y)) + (x * y ^ (k + 1) - y ^ (k + 2)) : by rw hz
    ... = (z * x + y ^ (k + 1)) * (x - y) : by ring_exp
  end

def eval_sub_factor (f : polynomial R) (x y : R) :
  {z : R // f.eval x - f.eval y = z * (x - y)} :=
begin
  refine ⟨f.sum (λ i r, r * (pow_sub_pow_factor x y i).val), _⟩,
  delta eval eval₂,
  simp only [sum, ← finset.sum_sub_distrib, finset.sum_mul],
  dsimp,
  congr' with i r,
  rw [mul_assoc, ←(pow_sub_pow_factor x y _).prop, mul_sub],
end

end identities

end polynomial
