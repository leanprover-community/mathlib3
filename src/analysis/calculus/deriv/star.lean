import analysis.calculus.deriv

section star
/-! ### Derivative of `x ↦ star x` -/

variables [star_ring 𝕜] [has_trivial_star 𝕜] [star_add_monoid F] [has_continuous_star F]
variable [star_module 𝕜 F]

protected theorem has_deriv_at_filter.star (h : has_deriv_at_filter f f' x L) :
  has_deriv_at_filter (λ x, star (f x)) (star f') x L :=
by simpa using h.star.has_deriv_at_filter

protected theorem has_deriv_within_at.star (h : has_deriv_within_at f f' s x) :
  has_deriv_within_at (λ x, star (f x)) (star f') s x :=
h.star

protected theorem has_deriv_at.star (h : has_deriv_at f f' x) :
  has_deriv_at (λ x, star (f x)) (star f') x :=
h.star

protected theorem has_strict_deriv_at.star (h : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (λ x, star (f x)) (star f') x :=
by simpa using h.star.has_strict_deriv_at

protected lemma deriv_within.star (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (λ y, star (f y)) s x = star (deriv_within f s x) :=
fun_like.congr_fun (fderiv_within_star hxs) _

protected lemma deriv.star : deriv (λ y, star (f y)) x = star (deriv f x) :=
fun_like.congr_fun fderiv_star _

@[simp] protected lemma deriv.star' : deriv (λ y, star (f y)) = (λ x, star (deriv f x)) :=
funext $ λ x, deriv.star

end star

