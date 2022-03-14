/-
Copyright (c) 2022 Yury G. Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury G. Kudryashov
-/
import analysis.calculus.deriv

/-!
# Functions continuous on a domain and differentiable on its interior

Many theorems in complex analysis assume that a function is continuous on a domain and is complex
differentiable on its interior. In this file we define a predicate `diff_on_int_cont` that expresses
this property and prove basic facts about this predicate.
-/

open set filter metric
open_locale topological_space

variables (𝕜 : Type*) {E F G : Type*} [nondiscrete_normed_field 𝕜] [normed_group E]
  [normed_group F] [normed_space 𝕜 E] [normed_space 𝕜 F] [normed_group G] [normed_space 𝕜 G]
  {f g : E → F} {s t : set E} {x : E}

/-- A predicate saying that a function is continuous on a set and is differentiable on its interior.
This assumption naturally appears in many theorems in complex analysis. -/
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

lemma differentiable_on.comp_diff_on_int_cont {g : G → E} {t : set G}
  (hf : differentiable_on 𝕜 f s) (hg : diff_on_int_cont 𝕜 g t) (h : maps_to g t s) :
  diff_on_int_cont 𝕜 (f ∘ g) t :=
⟨hf.comp hg.differentiable_on $ h.mono_left interior_subset, hf.continuous_on.comp hg.2 h⟩

lemma differentiable.comp_diff_on_int_cont {g : G → E} {t : set G}
  (hf : differentiable 𝕜 f) (hg : diff_on_int_cont 𝕜 g t) :
  diff_on_int_cont 𝕜 (f ∘ g) t :=
hf.differentiable_on.comp_diff_on_int_cont hg (maps_to_image _ _)

namespace diff_on_int_cont

lemma comp {g : G → E} {t : set G} (hf : diff_on_int_cont 𝕜 f s) (hg : diff_on_int_cont 𝕜 g t)
  (h : maps_to g t s) (h' : maps_to g (interior t) (interior s)) :
  diff_on_int_cont 𝕜 (f ∘ g) t :=
⟨hf.1.comp hg.1 h', hf.2.comp hg.2 h⟩

lemma differentiable_on_ball {x : E} {r : ℝ} (h : diff_on_int_cont 𝕜 f (closed_ball x r)) :
  differentiable_on 𝕜 f (ball x r) :=
h.differentiable_on.mono ball_subset_interior_closed_ball

lemma mk_ball [normed_space ℝ E] {x : E} {r : ℝ} (hd : differentiable_on 𝕜 f (ball x r))
  (hc : continuous_on f (closed_ball x r)) : diff_on_int_cont 𝕜 f (closed_ball x r) :=
begin
  refine ⟨_, hc⟩,
  rcases eq_or_ne r 0 with rfl|hr,
  { rw [closed_ball_zero],
    exact (subsingleton_singleton.mono interior_subset).differentiable_on },
  { rwa interior_closed_ball x hr }
end

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
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F] {c : E → 𝕜'} {s : set E}
  (hc : diff_on_int_cont 𝕜 c s) (y : F) :
  diff_on_int_cont 𝕜 (λ x, c x • y) s :=
hc.smul diff_on_int_cont_const

lemma inv {f : E → 𝕜} (hf : diff_on_int_cont 𝕜 f s) (h₀ : ∀ x ∈ s, f x ≠ 0) :
  diff_on_int_cont 𝕜 f⁻¹ s :=
⟨differentiable_on_inv.comp hf.1 $ λ x hx, h₀ _ (interior_subset hx), hf.2.inv₀ h₀⟩

end diff_on_int_cont
