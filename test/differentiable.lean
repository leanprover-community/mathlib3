import analysis.special_functions.trigonometric.deriv
import analysis.special_functions.log.deriv

namespace real

example : differentiable ℝ (λ (x : ℝ), exp x) :=
by simv

example : differentiable ℝ (λ (x : ℝ), exp ((sin x)^2) - exp (exp (cos (x - 3)))) :=
by simv

example (x : ℝ) : deriv (λ (x : ℝ), (cos x)^2 + 1 + (sin x)^2) x = 0 :=
by { simv, ring }

example (x : ℝ) : deriv (λ (x : ℝ), (1+x)^3 - x^3 - 3 * x^2 - 3 * x - 4) x = 0 :=
by { simv, ring }

example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simv, ring }

example (x : ℝ) : differentiable_at ℝ (λ x, (cos x, x)) x := by simv

example (x : ℝ) (h : 1 + sin x ≠ 0) : deriv (λ x, exp (cos x) / (1 + sin x)) x =
  (-(exp (cos x) * sin x * (1 + sin x)) - exp (cos x) * cos x) / (1 + sin x) ^ 2 :=
by simv [h]

example (x : ℝ) : differentiable_at ℝ (λ x, (sin x) / (exp x)) x :=
by simv [exp_ne_zero]

example : differentiable ℝ (λ x, (sin x) / (exp x)) :=
by simv [exp_ne_zero]

example (x : ℝ) (h : x ≠ 0) : deriv (λ x, x * (log x - 1)) x = log x :=
by simv [h]

end real

namespace complex

example : differentiable ℂ  (λ (x : ℂ), exp x) :=
by simv

example : differentiable ℂ (λ (x : ℂ), exp ((sin x)^2) - exp (exp (cos (x - 3)))) :=
by simv

example (x : ℂ) : deriv (λ (x : ℂ), (cos x)^2 + I + (sin x)^2) x = 0 :=
by { simv, ring }

example (x : ℂ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simv, ring }

example (x : ℂ) : differentiable_at ℂ (λ x, (cos x, x)) x := by simv

example (x : ℂ) (h : 1 + sin x ≠ 0) : deriv (λ x, exp (cos x) / (1 + sin x)) x =
  (-(exp (cos x) * sin x * (1 + sin x)) - exp (cos x) * cos x) / (1 + sin x) ^ 2 :=
by simv [h]

example (x : ℂ) : differentiable_at ℂ (λ x, (sin x) / (exp x)) x :=
by simv [exp_ne_zero]

example : differentiable ℂ (λ x, (sin x) / (exp x)) :=
by simv [exp_ne_zero]

end complex

namespace polynomial
open_locale polynomial

variables {R : Type*} [comm_semiring R]

example : (2 : R[X]).derivative = 0 :=
by conv_lhs { simv }

example : (3 + X : R[X]).derivative = 1 :=
by conv_lhs { simv }

example : (2 * X ^ 2 : R[X]).derivative = 4 * X :=
by conv_lhs { simv, ring_nf, }

example : (X ^ 2 : R[X]).derivative = 2 * X :=
by conv_lhs { simv }

example : ((C 2 * X ^ 3).derivative : R[X]) = 6 * X ^ 2 :=
by conv_lhs { simv, ring_nf, }

end polynomial
