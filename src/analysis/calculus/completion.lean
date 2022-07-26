import analysis.calculus.cont_diff
import analysis.calculus.diff_on_int_cont
import analysis.asymptotics.completion
import analysis.normed_space.completion

/-!
# Derivatives and completion of a normed space
-/

variables {𝕜 E F : Type*} [nontrivially_normed_field 𝕜] [normed_add_comm_group E] [normed_space 𝕜 E]
  [normed_add_comm_group F] [normed_space 𝕜 F]

local postfix `̂`:100 := uniform_space.completion

open asymptotics uniform_space.completion

section fderiv

variables {f : E → F} {x : E} {f' : E →L[𝕜] F} {s : set E} {L : filter E}
  {p : E → formal_multilinear_series 𝕜 E F} {n : with_top ℕ}

@[simp, norm_cast] lemma has_fderiv_at_filter_coe_completion :
  has_fderiv_at_filter (λ x, f x : E → F̂) (to_complL.comp f') x L ↔
    has_fderiv_at_filter f f' x L :=
by simp only [has_fderiv_at_filter, continuous_linear_map.comp_apply, coe_to_complL, ← coe_sub,
  is_o_completion_left]

@[simp, norm_cast] lemma has_fderiv_within_at_coe_completion :
  has_fderiv_within_at (λ x, f x : E → F̂) (to_complL.comp f') s x ↔ has_fderiv_within_at f f' s x :=
has_fderiv_at_filter_coe_completion

@[simp, norm_cast] lemma has_fderiv_at_coe_completion :
  has_fderiv_at (λ x, f x : E → F̂) (to_complL.comp f') x ↔ has_fderiv_at f f' x :=
has_fderiv_at_filter_coe_completion

alias has_fderiv_at_filter_coe_completion ↔ _ has_fderiv_at_filter.coe_completion
alias has_fderiv_within_at_coe_completion ↔ _ has_fderiv_within_at.coe_completion
alias has_fderiv_at_coe_completion ↔ _ has_fderiv_at.coe_completion

lemma differentiable_within_at.coe_completion (h : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λ x, f x : E → F̂) s x :=
h.has_fderiv_within_at.coe_completion.differentiable_within_at

lemma differentiable_at.coe_completion (h : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λ x, f x : E → F̂) x :=
h.has_fderiv_at.coe_completion.differentiable_at

lemma differentiable_on.coe_completion (h : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λ x, f x : E → F̂) s :=
λ x hx, (h x hx).coe_completion

lemma differentiable.coe_completion (h : differentiable 𝕜 f) :
  differentiable 𝕜 (λ x, f x : E → F̂) :=
λ x, (h x).coe_completion

lemma diff_cont_on_cl.coe_completion (h : diff_cont_on_cl 𝕜 f s) :
  diff_cont_on_cl 𝕜 (λ x, f x : E → F̂) s :=
(to_complL : F →L[𝕜] F̂).differentiable.comp_diff_cont_on_cl h

lemma has_ftaylor_series_up_to_on.coe_completion (h : has_ftaylor_series_up_to_on n f p s) :
  has_ftaylor_series_up_to_on n (λ x, f x : E → F̂)
    (λ x k, to_complL.comp_continuous_multilinear_map (p x k)) s :=
h.continuous_linear_map_comp (to_complL : F →L[𝕜] F̂)

lemma cont_diff_within_at.coe_completion (h : cont_diff_within_at 𝕜 n f s x) :
  cont_diff_within_at 𝕜 n (λ x, f x : E → F̂) s x :=
h.continuous_linear_map_comp (to_complL : F →L[𝕜] F̂)

lemma cont_diff_on.coe_completion (h : cont_diff_on 𝕜 n f s) :
  cont_diff_on 𝕜 n (λ x, f x : E → F̂) s :=
h.continuous_linear_map_comp (to_complL : F →L[𝕜] F̂)

lemma cont_diff.coe_completion (h : cont_diff 𝕜 n f) : cont_diff 𝕜 n (λ x, f x : E → F̂) :=
h.continuous_linear_map_comp (to_complL : F →L[𝕜] F̂)

end fderiv

section deriv

variables {f : 𝕜 → E} {x : 𝕜} {f' : E} {s : set 𝕜} {L : filter 𝕜}

@[simp, norm_cast] lemma has_deriv_at_filter_coe_completion :
  has_deriv_at_filter (λ x, f x : 𝕜 → Ê) f' x L ↔
    has_deriv_at_filter f f' x L :=
by simp only [has_deriv_at_filter_iff_is_o, ← coe_sub, ← coe_smul, is_o_completion_left]

@[simp, norm_cast] lemma has_deriv_within_at_coe_completion :
  has_deriv_within_at (λ x, f x : 𝕜 → Ê) f' s x ↔ has_deriv_within_at f f' s x :=
has_deriv_at_filter_coe_completion

@[simp, norm_cast] lemma has_deriv_at_coe_completion :
  has_deriv_at (λ x, f x : 𝕜 → Ê) f' x ↔ has_deriv_at f f' x :=
has_deriv_at_filter_coe_completion

alias has_deriv_at_filter_coe_completion ↔ _ has_deriv_at_filter.coe_completion
alias has_deriv_within_at_coe_completion ↔ _ has_deriv_within_at.coe_completion
alias has_deriv_at_coe_completion ↔ _ has_deriv_at.coe_completion

lemma differentiable_at.coe_completion_deriv (h : differentiable_at 𝕜 f x) :
  (↑(deriv f x) : Ê) = deriv (λ x, f x : 𝕜 → Ê) x :=
h.has_deriv_at.coe_completion.deriv.symm

end deriv
