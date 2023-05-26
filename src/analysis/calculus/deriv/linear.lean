import analysis.calculus.deriv.basic
import analysis.calculus.fderiv.linear

universes u v w

open_locale topology filter
open filter asymptotics set

variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]
variables {F : Type v} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {x : 𝕜}
variables {s : set 𝕜}
variables {L : filter 𝕜}

section continuous_linear_map
/-! ### Derivative of continuous linear maps -/
variables (e : 𝕜 →L[𝕜] F)

protected lemma continuous_linear_map.has_deriv_at_filter : has_deriv_at_filter e (e 1) x L :=
e.has_fderiv_at_filter.has_deriv_at_filter

protected lemma continuous_linear_map.has_strict_deriv_at : has_strict_deriv_at e (e 1) x :=
e.has_strict_fderiv_at.has_strict_deriv_at

protected lemma continuous_linear_map.has_deriv_at : has_deriv_at e (e 1) x :=
e.has_deriv_at_filter

protected lemma continuous_linear_map.has_deriv_within_at : has_deriv_within_at e (e 1) s x :=
e.has_deriv_at_filter

@[simp] protected lemma continuous_linear_map.deriv : deriv e x = e 1 :=
e.has_deriv_at.deriv

protected lemma continuous_linear_map.deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within e s x = e 1 :=
e.has_deriv_within_at.deriv_within hxs

end continuous_linear_map

section linear_map
/-! ### Derivative of bundled linear maps -/
variables (e : 𝕜 →ₗ[𝕜] F)

protected lemma linear_map.has_deriv_at_filter : has_deriv_at_filter e (e 1) x L :=
e.to_continuous_linear_map₁.has_deriv_at_filter

protected lemma linear_map.has_strict_deriv_at : has_strict_deriv_at e (e 1) x :=
e.to_continuous_linear_map₁.has_strict_deriv_at

protected lemma linear_map.has_deriv_at : has_deriv_at e (e 1) x :=
e.has_deriv_at_filter

protected lemma linear_map.has_deriv_within_at : has_deriv_within_at e (e 1) s x :=
e.has_deriv_at_filter

@[simp] protected lemma linear_map.deriv : deriv e x = e 1 :=
e.has_deriv_at.deriv

protected lemma linear_map.deriv_within (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within e s x = e 1 :=
e.has_deriv_within_at.deriv_within hxs

end linear_map

