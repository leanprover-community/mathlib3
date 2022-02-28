/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.calculus.fderiv

/-!
-/

open set filter
open_locale topological_space

variables (𝕜 : Type*) {E F G : Type*} [nondiscrete_normed_field 𝕜] [normed_group E]
  [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] [normed_group G] [normed_space 𝕜 G]
  {f g : E → F} {s t : set E} {x : E}

@[protect_proj] structure diff_on_int_cont (f : E → F) (s : set E) : Prop :=
(differentiable_on : differentiable_on 𝕜 f (interior s))
(continuous_on : continuous_on f s)

variable {𝕜}

lemma differentiable_on.diff_on_int_cont (h : differentiable_on 𝕜 f s) :
  diff_on_int_cont 𝕜 f s :=
⟨h.mono interior_subset, h.continuous_on⟩

lemma differentiable.diff_on_int_cont (h : differentiable 𝕜 f) : diff_on_int_cont 𝕜 f s :=
h.differentiable_on.diff_on_int_cont

lemma diff_on_int_cont_open (hs : is_open s) :
  diff_on_int_cont 𝕜 f s ↔ differentiable_on 𝕜 f s :=
⟨λ h, hs.interior_eq ▸ h.differentiable_on, λ h, h.diff_on_int_cont⟩

lemma diff_on_int_cont_univ : diff_on_int_cont 𝕜 f univ ↔ differentiable 𝕜 f :=
(diff_on_int_cont_open is_open_univ).trans differentiable_on_univ

lemma diff_on_int_cont_const {c : F} :
  diff_on_int_cont 𝕜 (λ x : E, c) s :=
⟨differentiable_on_const c, continuous_on_const⟩

namespace diff_on_int_cont

protected lemma differentiable_at (h : diff_on_int_cont 𝕜 f s) (hx : x ∈ interior s) :
  differentiable_at 𝕜 f x :=
h.differentiable_on.differentiable_at $ is_open_interior.mem_nhds hx

lemma differentiable_at' (h : diff_on_int_cont 𝕜 f s) (hx : s ∈ 𝓝 x) :
  differentiable_at 𝕜 f x :=
h.differentiable_at (mem_interior_iff_mem_nhds.2 hx)

protected lemma mono (h : diff_on_int_cont 𝕜 f s) (ht : t ⊆ s) : diff_on_int_cont 𝕜 f t :=
⟨h.differentiable_on.mono (interior_mono ht), h.continuous_on.mono ht⟩

lemma add (hf : diff_on_int_cont 𝕜 f s) (hg : diff_on_int_cont 𝕜 g s) :
  diff_on_int_cont 𝕜 (f + g) s :=
⟨hf.1.add hg.1, hf.2.add hg.2⟩

lemma add_const (hf : diff_on_int_cont 𝕜 f s) (c : F) :
  diff_on_int_cont 𝕜 (λ x, f x + c) s :=
hf.add diff_on_int_cont_const

lemma const_add (hf : diff_on_int_cont 𝕜 f s) (c : F) :
  diff_on_int_cont 𝕜 (λ x, c + f x) s :=
diff_on_int_cont_const.add hf

lemma neg (hf : diff_on_int_cont 𝕜 f s) : diff_on_int_cont 𝕜 (-f) s := ⟨hf.1.neg, hf.2.neg⟩

lemma sub (hf : diff_on_int_cont 𝕜 f s) (hg : diff_on_int_cont 𝕜 g s) :
  diff_on_int_cont 𝕜 (f - g) s :=
⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

lemma sub_const (hf : diff_on_int_cont 𝕜 f s) (c : F) : diff_on_int_cont 𝕜 (λ x, f x - c) s :=
hf.sub diff_on_int_cont_const

lemma const_sub (hf : diff_on_int_cont 𝕜 f s) (c : F) : diff_on_int_cont 𝕜 (λ x, c - f x) s :=
diff_on_int_cont_const.sub hf

lemma const_smul {R : Type*} [semiring R] [module R F] [smul_comm_class 𝕜 R F]
  [has_continuous_const_smul R F] (hf : diff_on_int_cont 𝕜 f s) (c : R) :
  diff_on_int_cont 𝕜 (c • f) s :=
⟨hf.1.const_smul c, hf.2.const_smul c⟩

lemma smul {𝕜' : Type*} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {c : E → 𝕜'} {f : E → F} {s : set E}
  (hc : diff_on_int_cont 𝕜 c s) (hf : diff_on_int_cont 𝕜 f s) :
  diff_on_int_cont 𝕜 (λ x, c x • f x) s :=
⟨hc.1.smul hf.1, hc.2.smul hf.2⟩

lemma smul_const {𝕜' : Type*} [nondiscrete_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {c : E → 𝕜'} {f : E → F} {s : set E}
  (hc : diff_on_int_cont 𝕜 c s) (y : F) :
  diff_on_int_cont 𝕜 (λ x, c x • y) s :=
hc.smul diff_on_int_cont_const

end diff_on_int_cont
