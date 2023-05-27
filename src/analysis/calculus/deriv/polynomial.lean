/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Eric Wieser
-/
import analysis.calculus.deriv.pow
import analysis.calculus.deriv.add
import data.polynomial.algebra_map
import data.polynomial.derivative

/-!
# Derivatives of polynomials

In this file we prove that derivatives of polynomials in the analysis sense agree with their
derivatives in the algebraic sense.

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## TODO

* Add results about multivariable polynomials.
* Generalize some (most?) results to an algebra over the base field.

## Keywords

derivative, polynomial
-/

universes u v w
open_locale classical topology big_operators filter ennreal polynomial
open filter asymptotics set
open continuous_linear_map (smul_right smul_right_one_eq_iff)


variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]
variables {F : Type v} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_add_comm_group E] [normed_space 𝕜 E]

variables {f f₀ f₁ g : 𝕜 → F}
variables {f' f₀' f₁' g' : F}
variables {x : 𝕜}
variables {s t : set 𝕜}
variables {L L₁ L₂ : filter 𝕜}

namespace polynomial
/-! ### Derivative of a polynomial -/

variables {R : Type*} [comm_semiring R] [algebra R 𝕜]
variables (p : 𝕜[X]) (q : R[X])

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected lemma has_strict_deriv_at (x : 𝕜) :
  has_strict_deriv_at (λx, p.eval x) (p.derivative.eval x) x :=
begin
  induction p using polynomial.induction_on',
  case h_add : p q hp hq { simpa using hp.add hq },
  case h_monomial : n a { simpa [mul_assoc] using (has_strict_deriv_at_pow n x).const_mul a }
end

protected lemma has_strict_deriv_at_aeval (x : 𝕜) :
  has_strict_deriv_at (λx, aeval x q) (aeval x q.derivative) x :=
by simpa only [aeval_def, eval₂_eq_eval_map, derivative_map]
  using (q.map (algebra_map R 𝕜)).has_strict_deriv_at x

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected lemma has_deriv_at (x : 𝕜) : has_deriv_at (λx, p.eval x) (p.derivative.eval x) x :=
(p.has_strict_deriv_at x).has_deriv_at

protected lemma has_deriv_at_aeval (x : 𝕜) :
  has_deriv_at (λx, aeval x q) (aeval x q.derivative) x :=
(q.has_strict_deriv_at_aeval x).has_deriv_at

protected theorem has_deriv_within_at (x : 𝕜) (s : set 𝕜) :
  has_deriv_within_at (λx, p.eval x) (p.derivative.eval x) s x :=
(p.has_deriv_at x).has_deriv_within_at

protected theorem has_deriv_within_at_aeval (x : 𝕜) (s : set 𝕜) :
  has_deriv_within_at (λx, aeval x q) (aeval x q.derivative) s x :=
(q.has_deriv_at_aeval x).has_deriv_within_at

protected lemma differentiable_at : differentiable_at 𝕜 (λx, p.eval x) x :=
(p.has_deriv_at x).differentiable_at

protected lemma differentiable_at_aeval : differentiable_at 𝕜 (λx, aeval x q) x :=
(q.has_deriv_at_aeval x).differentiable_at

protected lemma differentiable_within_at : differentiable_within_at 𝕜 (λx, p.eval x) s x :=
p.differentiable_at.differentiable_within_at

protected lemma differentiable_within_at_aeval : differentiable_within_at 𝕜 (λx, aeval x q) s x :=
q.differentiable_at_aeval.differentiable_within_at

protected lemma differentiable : differentiable 𝕜 (λx, p.eval x) :=
λx, p.differentiable_at

protected lemma differentiable_aeval : differentiable 𝕜 (λ x : 𝕜, aeval x q) :=
λx, q.differentiable_at_aeval

protected lemma differentiable_on : differentiable_on 𝕜 (λx, p.eval x) s :=
p.differentiable.differentiable_on

protected lemma differentiable_on_aeval : differentiable_on 𝕜 (λx, aeval x q) s :=
q.differentiable_aeval.differentiable_on

@[simp] protected lemma deriv : deriv (λx, p.eval x) x = p.derivative.eval x :=
(p.has_deriv_at x).deriv

@[simp] protected lemma deriv_aeval : deriv (λx, aeval x q) x = aeval x q.derivative :=
(q.has_deriv_at_aeval x).deriv

protected lemma deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, p.eval x) s x = p.derivative.eval x :=
begin
  rw differentiable_at.deriv_within p.differentiable_at hxs,
  exact p.deriv
end

protected lemma deriv_within_aeval (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, aeval x q) s x = aeval x q.derivative :=
by simpa only [aeval_def, eval₂_eq_eval_map, derivative_map]
  using (q.map (algebra_map R 𝕜)).deriv_within hxs

protected lemma has_fderiv_at (x : 𝕜) :
  has_fderiv_at (λx, p.eval x) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) x :=
p.has_deriv_at x

protected lemma has_fderiv_at_aeval (x : 𝕜) :
  has_fderiv_at (λx, aeval x q) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (aeval x q.derivative)) x :=
q.has_deriv_at_aeval x

protected lemma has_fderiv_within_at (x : 𝕜) :
  has_fderiv_within_at (λx, p.eval x) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x)) s x :=
(p.has_fderiv_at x).has_fderiv_within_at

protected lemma has_fderiv_within_at_aeval (x : 𝕜) :
  has_fderiv_within_at (λx, aeval x q) (smul_right (1 : 𝕜 →L[𝕜] 𝕜) (aeval x q.derivative)) s x :=
(q.has_fderiv_at_aeval x).has_fderiv_within_at

@[simp] protected lemma fderiv :
  fderiv 𝕜 (λx, p.eval x) x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
(p.has_fderiv_at x).fderiv

@[simp] protected lemma fderiv_aeval :
  fderiv 𝕜 (λx, aeval x q) x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (aeval x q.derivative) :=
(q.has_fderiv_at_aeval x).fderiv

protected lemma fderiv_within (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx, p.eval x) s x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (p.derivative.eval x) :=
(p.has_fderiv_within_at x).fderiv_within hxs

protected lemma fderiv_within_aeval (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λx, aeval x q) s x = smul_right (1 : 𝕜 →L[𝕜] 𝕜) (aeval x q.derivative) :=
(q.has_fderiv_within_at_aeval x).fderiv_within hxs

end polynomial

