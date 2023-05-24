
section pow
/-! ### Derivative of `x ↦ x^n` for `n : ℕ` -/
variables {x : 𝕜} {s : set 𝕜} {c : 𝕜 → 𝕜} {c' : 𝕜}
variable (n : ℕ)

lemma has_strict_deriv_at_pow (n : ℕ) (x : 𝕜) :
  has_strict_deriv_at (λx, x^n) ((n : 𝕜) * x^(n-1)) x :=
begin
  convert (polynomial.C (1 : 𝕜) * (polynomial.X)^n).has_strict_deriv_at x,
  { simp },
  { rw [polynomial.derivative_C_mul_X_pow], simp }
end

lemma has_deriv_at_pow (n : ℕ) (x : 𝕜) : has_deriv_at (λx, x^n) ((n : 𝕜) * x^(n-1)) x :=
(has_strict_deriv_at_pow n x).has_deriv_at

theorem has_deriv_within_at_pow (n : ℕ) (x : 𝕜) (s : set 𝕜) :
  has_deriv_within_at (λx, x^n) ((n : 𝕜) * x^(n-1)) s x :=
(has_deriv_at_pow n x).has_deriv_within_at

lemma differentiable_at_pow : differentiable_at 𝕜 (λx, x^n) x :=
(has_deriv_at_pow n x).differentiable_at

lemma differentiable_within_at_pow : differentiable_within_at 𝕜 (λx, x^n) s x :=
(differentiable_at_pow n).differentiable_within_at

lemma differentiable_pow : differentiable 𝕜 (λx:𝕜, x^n) :=
λ x, differentiable_at_pow n

lemma differentiable_on_pow : differentiable_on 𝕜 (λx, x^n) s :=
(differentiable_pow n).differentiable_on

lemma deriv_pow : deriv (λ x, x^n) x = (n : 𝕜) * x^(n-1) :=
(has_deriv_at_pow n x).deriv

@[simp] lemma deriv_pow' : deriv (λ x, x^n) = λ x, (n : 𝕜) * x^(n-1) :=
funext $ λ x, deriv_pow n

lemma deriv_within_pow (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, x^n) s x = (n : 𝕜) * x^(n-1) :=
(has_deriv_within_at_pow n x s).deriv_within hxs

lemma has_deriv_within_at.pow (hc : has_deriv_within_at c c' s x) :
  has_deriv_within_at (λ y, (c y)^n) ((n : 𝕜) * (c x)^(n-1) * c') s x :=
(has_deriv_at_pow n (c x)).comp_has_deriv_within_at x hc

lemma has_deriv_at.pow (hc : has_deriv_at c c' x) :
  has_deriv_at (λ y, (c y)^n) ((n : 𝕜) * (c x)^(n-1) * c') x :=
by { rw ← has_deriv_within_at_univ at *, exact hc.pow n }

lemma deriv_within_pow' (hc : differentiable_within_at 𝕜 c s x)
  (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λx, (c x)^n) s x = (n : 𝕜) * (c x)^(n-1) * (deriv_within c s x) :=
(hc.has_deriv_within_at.pow n).deriv_within hxs

@[simp] lemma deriv_pow'' (hc : differentiable_at 𝕜 c x) :
  deriv (λx, (c x)^n) x = (n : 𝕜) * (c x)^(n-1) * (deriv c x) :=
(hc.has_deriv_at.pow n).deriv

end pow

