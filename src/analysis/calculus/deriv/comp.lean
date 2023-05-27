/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel, Yury Kudryashov, Yuyang Zhao
-/
import analysis.calculus.deriv.basic
import analysis.calculus.fderiv.comp
import analysis.calculus.fderiv.restrict_scalars

/-!
# One-dimensional derivatives of compositions of functions

In this file we prove the chain rule for the following cases:

* `has_deriv_at.comp` etc: `f : 𝕜' → 𝕜'` composed with `g : 𝕜 → 𝕜'`;
* `has_deriv_at.scomp` etc: `f : 𝕜' → E` composed with `g : 𝕜 → 𝕜'`;
* `has_fderiv_at.comp_has_deriv_at` etc: `f : E → F` composed with `g : 𝕜 → E`;

Here `𝕜` is the base normed field, `E` and `F` are normed spaces over `𝕜` and `𝕜'` is an algebra
over `𝕜` (e.g., `𝕜'=𝕜` or `𝕜=ℝ`, `𝕜'=ℂ`).

For a more detailed overview of one-dimensional derivatives in mathlib, see the module docstring of
`analysis/calculus/deriv/basic`.

## Keywords

derivative, chain rule
-/

universes u v w
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

section composition
/-!
### Derivative of the composition of a vector function and a scalar function

We use `scomp` in lemmas on composition of vector valued and scalar valued functions, and `comp`
in lemmas on composition of scalar valued functions, in analogy for `smul` and `mul` (and also
because the `comp` version with the shorter name will show up much more often in applications).
The formula for the derivative involves `smul` in `scomp` lemmas, which can be reduced to
usual multiplication in `comp` lemmas.
-/

/- For composition lemmas, we put x explicit to help the elaborator, as otherwise Lean tends to
get confused since there are too many possibilities for composition -/
variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {s' t' : set 𝕜'}
  {h : 𝕜 → 𝕜'} {h₁ : 𝕜 → 𝕜} {h₂ : 𝕜' → 𝕜'} {h' h₂' : 𝕜'} {h₁' : 𝕜}
  {g₁ : 𝕜' → F} {g₁' : F} {L' : filter 𝕜'} (x)

theorem has_deriv_at_filter.scomp
  (hg : has_deriv_at_filter g₁ g₁' (h x) L')
  (hh : has_deriv_at_filter h h' x L) (hL : tendsto h L L'):
  has_deriv_at_filter (g₁ ∘ h) (h' • g₁') x L :=
by simpa using ((hg.restrict_scalars 𝕜).comp x hh hL).has_deriv_at_filter

theorem has_deriv_within_at.scomp_has_deriv_at
  (hg : has_deriv_within_at g₁ g₁' s' (h x))
  (hh : has_deriv_at h h' x) (hs : ∀ x, h x ∈ s') :
  has_deriv_at (g₁ ∘ h) (h' • g₁') x :=
hg.scomp x hh $ tendsto_inf.2 ⟨hh.continuous_at, tendsto_principal.2 $ eventually_of_forall hs⟩

theorem has_deriv_within_at.scomp
  (hg : has_deriv_within_at g₁ g₁' t' (h x))
  (hh : has_deriv_within_at h h' s x) (hst : maps_to h s t') :
  has_deriv_within_at (g₁ ∘ h) (h' • g₁') s x :=
hg.scomp x hh $ hh.continuous_within_at.tendsto_nhds_within hst

/-- The chain rule. -/
theorem has_deriv_at.scomp
  (hg : has_deriv_at g₁ g₁' (h x)) (hh : has_deriv_at h h' x) :
  has_deriv_at (g₁ ∘ h) (h' • g₁') x :=
hg.scomp x hh hh.continuous_at

theorem has_strict_deriv_at.scomp
  (hg : has_strict_deriv_at g₁ g₁' (h x)) (hh : has_strict_deriv_at h h' x) :
  has_strict_deriv_at (g₁ ∘ h) (h' • g₁') x :=
by simpa using ((hg.restrict_scalars 𝕜).comp x hh).has_strict_deriv_at

theorem has_deriv_at.scomp_has_deriv_within_at
  (hg : has_deriv_at g₁ g₁' (h x)) (hh : has_deriv_within_at h h' s x) :
  has_deriv_within_at (g₁ ∘ h) (h' • g₁') s x :=
has_deriv_within_at.scomp x hg.has_deriv_within_at hh (maps_to_univ _ _)

lemma deriv_within.scomp
  (hg : differentiable_within_at 𝕜' g₁ t' (h x)) (hh : differentiable_within_at 𝕜 h s x)
  (hs : maps_to h s t') (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (g₁ ∘ h) s x = deriv_within h s x • deriv_within g₁ t' (h x) :=
(has_deriv_within_at.scomp x hg.has_deriv_within_at hh.has_deriv_within_at hs).deriv_within hxs

lemma deriv.scomp
  (hg : differentiable_at 𝕜' g₁ (h x)) (hh : differentiable_at 𝕜 h x) :
  deriv (g₁ ∘ h) x = deriv h x • deriv g₁ (h x) :=
(has_deriv_at.scomp x hg.has_deriv_at hh.has_deriv_at).deriv

/-! ### Derivative of the composition of a scalar and vector functions -/

theorem has_deriv_at_filter.comp_has_fderiv_at_filter {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
  {L'' : filter E} (hh₂ : has_deriv_at_filter h₂ h₂' (f x) L')
  (hf : has_fderiv_at_filter f f' x L'') (hL : tendsto f L'' L') :
  has_fderiv_at_filter (h₂ ∘ f) (h₂' • f') x L'' :=
by { convert (hh₂.restrict_scalars 𝕜).comp x hf hL, ext x, simp [mul_comm] }

theorem has_strict_deriv_at.comp_has_strict_fderiv_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
  (hh : has_strict_deriv_at h₂ h₂' (f x)) (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (h₂ ∘ f) (h₂' • f') x :=
begin
  rw has_strict_deriv_at at hh,
  convert (hh.restrict_scalars 𝕜).comp x hf,
  ext x,
  simp [mul_comm]
end

theorem has_deriv_at.comp_has_fderiv_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} (x)
  (hh : has_deriv_at h₂ h₂' (f x)) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (h₂ ∘ f) (h₂' • f') x :=
hh.comp_has_fderiv_at_filter x hf hf.continuous_at

theorem has_deriv_at.comp_has_fderiv_within_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s} (x)
  (hh : has_deriv_at h₂ h₂' (f x)) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (h₂ ∘ f) (h₂' • f') s x :=
hh.comp_has_fderiv_at_filter x hf hf.continuous_within_at

theorem has_deriv_within_at.comp_has_fderiv_within_at {f : E → 𝕜'} {f' : E →L[𝕜] 𝕜'} {s t} (x)
  (hh : has_deriv_within_at h₂ h₂' t (f x)) (hf : has_fderiv_within_at f f' s x)
  (hst : maps_to f s t) :
  has_fderiv_within_at (h₂ ∘ f) (h₂' • f') s x :=
hh.comp_has_fderiv_at_filter x hf $ hf.continuous_within_at.tendsto_nhds_within hst

/-! ### Derivative of the composition of two scalar functions -/

theorem has_deriv_at_filter.comp
  (hh₂ : has_deriv_at_filter h₂ h₂' (h x) L')
  (hh : has_deriv_at_filter h h' x L) (hL : tendsto h L L') :
  has_deriv_at_filter (h₂ ∘ h) (h₂' * h') x L :=
by { rw mul_comm, exact hh₂.scomp x hh hL }

theorem has_deriv_within_at.comp
  (hh₂ : has_deriv_within_at h₂ h₂' s' (h x))
  (hh : has_deriv_within_at h h' s x) (hst : maps_to h s s') :
  has_deriv_within_at (h₂ ∘ h) (h₂' * h') s x :=
by { rw mul_comm, exact hh₂.scomp x hh hst, }

/-- The chain rule. -/
theorem has_deriv_at.comp
  (hh₂ : has_deriv_at h₂ h₂' (h x)) (hh : has_deriv_at h h' x) :
  has_deriv_at (h₂ ∘ h) (h₂' * h') x :=
hh₂.comp x hh hh.continuous_at

theorem has_strict_deriv_at.comp
  (hh₂ : has_strict_deriv_at h₂ h₂' (h x)) (hh : has_strict_deriv_at h h' x) :
  has_strict_deriv_at (h₂ ∘ h) (h₂' * h') x :=
by { rw mul_comm, exact hh₂.scomp x hh }

theorem has_deriv_at.comp_has_deriv_within_at
  (hh₂ : has_deriv_at h₂ h₂' (h x)) (hh : has_deriv_within_at h h' s x) :
  has_deriv_within_at (h₂ ∘ h) (h₂' * h') s x :=
hh₂.has_deriv_within_at.comp x hh (maps_to_univ _ _)

lemma deriv_within.comp
  (hh₂ : differentiable_within_at 𝕜' h₂ s' (h x)) (hh : differentiable_within_at 𝕜 h s x)
  (hs : maps_to h s s') (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (h₂ ∘ h) s x = deriv_within h₂ s' (h x) * deriv_within h s x :=
(hh₂.has_deriv_within_at.comp x hh.has_deriv_within_at hs).deriv_within hxs

lemma deriv.comp
  (hh₂ : differentiable_at 𝕜' h₂ (h x)) (hh : differentiable_at 𝕜 h x) :
  deriv (h₂ ∘ h) x = deriv h₂ (h x) * deriv h x :=
(hh₂.has_deriv_at.comp x hh.has_deriv_at).deriv

protected lemma has_deriv_at_filter.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_at_filter f f' x L) (hL : tendsto f L L) (hx : f x = x) (n : ℕ) :
  has_deriv_at_filter (f^[n]) (f'^n) x L :=
begin
  have := hf.iterate hL hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_deriv_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_deriv_at (f^[n]) (f'^n) x :=
begin
  have := has_fderiv_at.iterate hf hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_deriv_within_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_deriv_within_at f f' s x) (hx : f x = x) (hs : maps_to f s s) (n : ℕ) :
  has_deriv_within_at (f^[n]) (f'^n) s x :=
begin
  have := has_fderiv_within_at.iterate hf hx hs n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

protected lemma has_strict_deriv_at.iterate {f : 𝕜 → 𝕜} {f' : 𝕜}
  (hf : has_strict_deriv_at f f' x) (hx : f x = x) (n : ℕ) :
  has_strict_deriv_at (f^[n]) (f'^n) x :=
begin
  have := hf.iterate hx n,
  rwa [continuous_linear_map.smul_right_one_pow] at this
end

end composition

section composition_vector
/-! ### Derivative of the composition of a function between vector spaces and a function on `𝕜` -/

open continuous_linear_map

variables {l : F → E} {l' : F →L[𝕜] E}
variable (x)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative within a set
equal to the Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_within_at.comp_has_deriv_within_at {t : set F}
  (hl : has_fderiv_within_at l l' t (f x)) (hf : has_deriv_within_at f f' s x)
  (hst : maps_to f s t) :
  has_deriv_within_at (l ∘ f) (l' f') s x :=
by simpa only [one_apply, one_smul, smul_right_apply, coe_comp', (∘)]
  using (hl.comp x hf.has_fderiv_within_at hst).has_deriv_within_at

theorem has_fderiv_at.comp_has_deriv_within_at
  (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_within_at f f' s x) :
  has_deriv_within_at (l ∘ f) (l' f') s x :=
hl.has_fderiv_within_at.comp_has_deriv_within_at x hf (maps_to_univ _ _)

/-- The composition `l ∘ f` where `l : F → E` and `f : 𝕜 → F`, has a derivative equal to the
Fréchet derivative of `l` applied to the derivative of `f`. -/
theorem has_fderiv_at.comp_has_deriv_at (hl : has_fderiv_at l l' (f x)) (hf : has_deriv_at f f' x) :
  has_deriv_at (l ∘ f) (l' f') x :=
has_deriv_within_at_univ.mp $ hl.comp_has_deriv_within_at x hf.has_deriv_within_at

theorem has_strict_fderiv_at.comp_has_strict_deriv_at
  (hl : has_strict_fderiv_at l l' (f x)) (hf : has_strict_deriv_at f f' x) :
  has_strict_deriv_at (l ∘ f) (l' f') x :=
by simpa only [one_apply, one_smul, smul_right_apply, coe_comp', (∘)]
  using (hl.comp x hf.has_strict_fderiv_at).has_strict_deriv_at

lemma fderiv_within.comp_deriv_within {t : set F}
  (hl : differentiable_within_at 𝕜 l t (f x)) (hf : differentiable_within_at 𝕜 f s x)
  (hs : maps_to f s t) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within (l ∘ f) s x = (fderiv_within 𝕜 l t (f x) : F → E) (deriv_within f s x) :=
(hl.has_fderiv_within_at.comp_has_deriv_within_at x hf.has_deriv_within_at hs).deriv_within hxs

lemma fderiv.comp_deriv
  (hl : differentiable_at 𝕜 l (f x)) (hf : differentiable_at 𝕜 f x) :
  deriv (l ∘ f) x = (fderiv 𝕜 l (f x) : F → E) (deriv f x) :=
(hl.has_fderiv_at.comp_has_deriv_at x hf.has_deriv_at).deriv

end composition_vector

