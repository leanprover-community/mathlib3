/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.fderiv.basic

open filter asymptotics continuous_linear_map set metric
open_locale topology classical nnreal filter asymptotics ennreal

noncomputable theory

section restrict_scalars
/-!
### Restricting from `ℂ` to `ℝ`, or generally from `𝕜'` to `𝕜`

If a function is differentiable over `ℂ`, then it is differentiable over `ℝ`. In this paragraph,
we give variants of this statement, in the general situation where `ℂ` and `ℝ` are replaced
respectively by `𝕜'` and `𝕜` where `𝕜'` is a normed algebra over `𝕜`.
-/

variables (𝕜 : Type*) [nontrivially_normed_field 𝕜]
variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E] [normed_space 𝕜' E]
variables [is_scalar_tower 𝕜 𝕜' E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F] [normed_space 𝕜' F]
variables [is_scalar_tower 𝕜 𝕜' F]
variables {f : E → F} {f' : E →L[𝕜'] F} {s : set E} {x : E}

lemma has_strict_fderiv_at.restrict_scalars (h : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at f (f'.restrict_scalars 𝕜) x := h

lemma has_fderiv_at_filter.restrict_scalars {L} (h : has_fderiv_at_filter f f' x L) :
  has_fderiv_at_filter f (f'.restrict_scalars 𝕜) x L := h

lemma has_fderiv_at.restrict_scalars (h : has_fderiv_at f f' x) :
  has_fderiv_at f (f'.restrict_scalars 𝕜) x := h

lemma has_fderiv_within_at.restrict_scalars (h : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at f (f'.restrict_scalars 𝕜) s x := h

lemma differentiable_at.restrict_scalars (h : differentiable_at 𝕜' f x) :
  differentiable_at 𝕜 f x :=
(h.has_fderiv_at.restrict_scalars 𝕜).differentiable_at

lemma differentiable_within_at.restrict_scalars (h : differentiable_within_at 𝕜' f s x) :
  differentiable_within_at 𝕜 f s x :=
(h.has_fderiv_within_at.restrict_scalars 𝕜).differentiable_within_at

lemma differentiable_on.restrict_scalars (h : differentiable_on 𝕜' f s) :
  differentiable_on 𝕜 f s :=
λx hx, (h x hx).restrict_scalars 𝕜

lemma differentiable.restrict_scalars (h : differentiable 𝕜' f) :
  differentiable 𝕜 f :=
λx, (h x).restrict_scalars 𝕜

lemma has_fderiv_within_at_of_restrict_scalars
  {g' : E →L[𝕜] F} (h : has_fderiv_within_at f g' s x)
  (H : f'.restrict_scalars 𝕜 = g') : has_fderiv_within_at f f' s x :=
by { rw ← H at h, exact h }

lemma has_fderiv_at_of_restrict_scalars {g' : E →L[𝕜] F} (h : has_fderiv_at f g' x)
  (H : f'.restrict_scalars 𝕜 = g') : has_fderiv_at f f' x :=
by { rw ← H at h, exact h }

lemma differentiable_at.fderiv_restrict_scalars (h : differentiable_at 𝕜' f x) :
  fderiv 𝕜 f x = (fderiv 𝕜' f x).restrict_scalars 𝕜 :=
(h.has_fderiv_at.restrict_scalars 𝕜).fderiv

lemma differentiable_within_at_iff_restrict_scalars
  (hf : differentiable_within_at 𝕜 f s x) (hs : unique_diff_within_at 𝕜 s x) :
  differentiable_within_at 𝕜' f s x ↔
  ∃ (g' : E →L[𝕜'] F), g'.restrict_scalars 𝕜 = fderiv_within 𝕜 f s x :=
begin
  split,
  { rintros ⟨g', hg'⟩,
    exact ⟨g', hs.eq (hg'.restrict_scalars 𝕜) hf.has_fderiv_within_at⟩, },
  { rintros ⟨f', hf'⟩,
    exact ⟨f', has_fderiv_within_at_of_restrict_scalars 𝕜 hf.has_fderiv_within_at hf'⟩, },
end

lemma differentiable_at_iff_restrict_scalars (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜' f x ↔ ∃ (g' : E →L[𝕜'] F), g'.restrict_scalars 𝕜 = fderiv 𝕜 f x :=
begin
  rw [← differentiable_within_at_univ, ← fderiv_within_univ],
  exact differentiable_within_at_iff_restrict_scalars 𝕜
    hf.differentiable_within_at unique_diff_within_at_univ,
end

end restrict_scalars
