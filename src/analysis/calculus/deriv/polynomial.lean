import analysis.calculus.deriv

namespace polynomial
/-! ### Derivative of a polynomial -/

variables {R : Type*} [comm_semiring R] [algebra R 𝕜]
variables (p : 𝕜[X]) (q : R[X]) {x : 𝕜} {s : set 𝕜}

/-- The derivative (in the analysis sense) of a polynomial `p` is given by `p.derivative`. -/
protected lemma has_strict_deriv_at (x : 𝕜) :
  has_strict_deriv_at (λx, p.eval x) (p.derivative.eval x) x :=
begin
  apply p.induction_on,
  { simp [has_strict_deriv_at_const] },
  { assume p q hp hq,
    convert hp.add hq;
    simp },
  { assume n a h,
    convert h.mul (has_strict_deriv_at_id x),
    { ext y, simp [pow_add, mul_assoc] },
    { simp only [pow_add, pow_one, derivative_mul, derivative_C, zero_mul, derivative_X_pow,
      derivative_X, mul_one, zero_add, eval_mul, eval_C, eval_add, eval_nat_cast, eval_pow, eval_X,
      id.def], ring } }
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

