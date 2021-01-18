import analysis.calculus.deriv
import analysis.analytic.basic

open filter asymptotics
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]

section fderiv

variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
  {F : Type*} [normed_group F] [normed_space 𝕜 F]
  {f : E → F} {p : formal_multilinear_series 𝕜 E F} {s : set E} {x : E} {r : ennreal}

lemma has_fpower_series_at.has_strict_fderiv_at (h : has_fpower_series_at f p x) :
  has_strict_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
begin
  rw [has_strict_fderiv_at, ← map_add_left_nhds_zero, is_o_map],
  have : ∀ y, (fin.snoc 0 y : fin 1 → E) = λ _, y,
  { intro y, ext i,
    rw [show i = fin.last 0, from subsingleton.elim _ _, fin.snoc_last] },
  simp_rw [(∘), prod.fst_add, prod.snd_add, add_sub_add_left_eq_sub,
    continuous_linear_map.map_sub, continuous_multilinear_curry_fin1_apply,
    this],
  refine h.is_O_image_sub_norm_mul_norm_sub.trans_is_o (is_o.of_norm_right _),
  refine is_o_iff_exists_eq_mul.2 ⟨_, tendsto_norm_zero, eventually_eq.rfl⟩
end

lemma has_fpower_series_at.has_fderiv_at (h : has_fpower_series_at f p x) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
h.has_strict_fderiv_at.has_fderiv_at

lemma has_fpower_series_at.differentiable_at (h : has_fpower_series_at f p x) :
  differentiable_at 𝕜 f x :=
h.has_fderiv_at.differentiable_at

lemma analytic_at.differentiable_at : analytic_at 𝕜 f x → differentiable_at 𝕜 f x
| ⟨p, hp⟩ := hp.differentiable_at

lemma analytic_at.differentiable_within_at (h : analytic_at 𝕜 f x) :
  differentiable_within_at 𝕜 f s x :=
h.differentiable_at.differentiable_within_at

lemma has_fpower_series_on_ball.differentiable_on [complete_space F]
  (h : has_fpower_series_on_ball f p x r) :
  differentiable_on 𝕜 f (emetric.ball x r) :=
λ y hy, (h.analytic_at_of_mem hy).differentiable_within_at

end fderiv

variables {f : 𝕜 → 𝕜} {p : formal_multilinear_series 𝕜 𝕜 𝕜} {s : set 𝕜} {x : 𝕜} {r : ennreal}

lemma has_fpower_series_at.has_strict_deriv_at (h : has_fpower_series_at f p x) :
  has_strict_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_fderiv_at.has_strict_deriv_at

lemma has_fpower_series_at.has_deriv_at (h : has_fpower_series_at f p x) :
  has_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_deriv_at.has_deriv_at
