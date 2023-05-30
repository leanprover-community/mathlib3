/-
Copyright (c) 2023 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import analysis.calculus.deriv.basic
import analysis.calculus.fderiv.star

/-!
# Star operations on derivatives

This file contains the usual formulas (and existence assertions) for the derivative of the star
operation. Note that these only apply when the field that the derivative is respect to has a trivial
star operation; which as should be expected rules out `𝕜 = ℂ`.
-/

universes u v w
noncomputable theory
open_locale classical topology big_operators filter ennreal
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
