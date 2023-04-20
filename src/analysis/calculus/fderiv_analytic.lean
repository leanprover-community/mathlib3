/-
Copyright (c) 2021 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.calculus.deriv
import analysis.analytic.basic
import analysis.calculus.cont_diff

/-!
# Frechet derivatives of analytic functions.

A function expressible as a power series at a point has a Frechet derivative there.
Also the special case in terms of `deriv` when the domain is 1-dimensional.
-/

open filter asymptotics
open_locale ennreal

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]

section fderiv

variables {p : formal_multilinear_series 𝕜 E F} {r : ℝ≥0∞}
variables {f : E → F} {x : E} {s : set E}

lemma has_fpower_series_at.has_strict_fderiv_at (h : has_fpower_series_at f p x) :
  has_strict_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p 1)) x :=
begin
  refine h.is_O_image_sub_norm_mul_norm_sub.trans_is_o (is_o.of_norm_right _),
  refine is_o_iff_exists_eq_mul.2 ⟨λ y, ‖y - (x, x)‖, _, eventually_eq.rfl⟩,
  refine (continuous_id.sub continuous_const).norm.tendsto' _ _ _,
  rw [_root_.id, sub_self, norm_zero]
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

lemma has_fpower_series_at.fderiv_eq (h : has_fpower_series_at f p x) :
  fderiv 𝕜 f x = continuous_multilinear_curry_fin1 𝕜 E F (p 1) :=
h.has_fderiv_at.fderiv

lemma has_fpower_series_on_ball.differentiable_on [complete_space F]
  (h : has_fpower_series_on_ball f p x r) :
  differentiable_on 𝕜 f (emetric.ball x r) :=
λ y hy, (h.analytic_at_of_mem hy).differentiable_within_at

lemma analytic_on.differentiable_on (h : analytic_on 𝕜 f s) :
  differentiable_on 𝕜 f s :=
λ y hy, (h y hy).differentiable_within_at

lemma has_fpower_series_on_ball.has_fderiv_at [complete_space F]
  (h : has_fpower_series_on_ball f p x r) {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p.change_origin y 1)) (x + y) :=
(h.change_origin hy).has_fpower_series_at.has_fderiv_at

lemma has_fpower_series_on_ball.fderiv_eq [complete_space F]
  (h : has_fpower_series_on_ball f p x r) {y : E} (hy : (‖y‖₊ : ℝ≥0∞) < r) :
  fderiv 𝕜 f (x + y) = continuous_multilinear_curry_fin1 𝕜 E F (p.change_origin y 1) :=
(h.has_fderiv_at hy).fderiv

/-- If a function has a power series on a ball, then so does its derivative. -/
lemma has_fpower_series_on_ball.fderiv [complete_space F]
  (h : has_fpower_series_on_ball f p x r) :
  has_fpower_series_on_ball (fderiv 𝕜 f)
    ((continuous_multilinear_curry_fin1 𝕜 E F : (E [×1]→L[𝕜] F) →L[𝕜] (E →L[𝕜] F))
      .comp_formal_multilinear_series (p.change_origin_series 1)) x r :=
begin
  suffices A : has_fpower_series_on_ball
    (λ z, continuous_multilinear_curry_fin1 𝕜 E F (p.change_origin (z - x) 1))
      ((continuous_multilinear_curry_fin1 𝕜 E F : (E [×1]→L[𝕜] F) →L[𝕜] (E →L[𝕜] F))
        .comp_formal_multilinear_series (p.change_origin_series 1)) x r,
  { apply A.congr,
    assume z hz,
    dsimp,
    rw [← h.fderiv_eq, add_sub_cancel'_right],
    simpa only [edist_eq_coe_nnnorm_sub, emetric.mem_ball] using hz},
  suffices B : has_fpower_series_on_ball (λ z, p.change_origin (z - x) 1)
    (p.change_origin_series 1) x r,
      from (continuous_multilinear_curry_fin1 𝕜 E F).to_continuous_linear_equiv
        .to_continuous_linear_map.comp_has_fpower_series_on_ball B,
  simpa using ((p.has_fpower_series_on_ball_change_origin 1 (h.r_pos.trans_le h.r_le)).mono
    h.r_pos h.r_le).comp_sub x,
end

/-- If a function is analytic on a set `s`, so is its Fréchet derivative. -/
lemma analytic_on.fderiv [complete_space F] (h : analytic_on 𝕜 f s) :
  analytic_on 𝕜 (fderiv 𝕜 f) s :=
begin
  assume y hy,
  rcases h y hy with ⟨p, r, hp⟩,
  exact hp.fderiv.analytic_at,
end

/-- If a function is analytic on a set `s`, so are its successive Fréchet derivative. -/
lemma analytic_on.iterated_fderiv [complete_space F] (h : analytic_on 𝕜 f s) (n : ℕ) :
  analytic_on 𝕜 (iterated_fderiv 𝕜 n f) s :=
begin
  induction n with n IH,
  { rw iterated_fderiv_zero_eq_comp,
    exact ((continuous_multilinear_curry_fin0 𝕜 E F).symm : F →L[𝕜] (E [×0]→L[𝕜] F))
      .comp_analytic_on h },
  { rw iterated_fderiv_succ_eq_comp_left,
    apply (continuous_multilinear_curry_left_equiv 𝕜 (λ (i : fin (n + 1)), E) F)
      .to_continuous_linear_equiv.to_continuous_linear_map.comp_analytic_on,
    exact IH.fderiv }
end

/-- An analytic function is infinitely differentiable. -/
lemma analytic_on.cont_diff_on [complete_space F] (h : analytic_on 𝕜 f s) {n : ℕ∞} :
  cont_diff_on 𝕜 n f s :=
begin
  let t := {x | analytic_at 𝕜 f x},
  suffices : cont_diff_on 𝕜 n f t, from this.mono h,
  have H : analytic_on 𝕜 f t := λ x hx, hx,
  have t_open : is_open t := is_open_analytic_at 𝕜 f,
  apply cont_diff_on_of_continuous_on_differentiable_on,
  { assume m hm,
    apply (H.iterated_fderiv m).continuous_on.congr,
    assume x hx,
    exact iterated_fderiv_within_of_is_open _ t_open hx },
  { assume m hm,
    apply (H.iterated_fderiv m).differentiable_on.congr,
    assume x hx,
    exact iterated_fderiv_within_of_is_open _ t_open hx }
end

end fderiv

section deriv

variables {p : formal_multilinear_series 𝕜 𝕜 F} {r : ℝ≥0∞}
variables {f : 𝕜 → F} {x : 𝕜} {s : set 𝕜}

protected lemma has_fpower_series_at.has_strict_deriv_at (h : has_fpower_series_at f p x) :
  has_strict_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_fderiv_at.has_strict_deriv_at

protected lemma has_fpower_series_at.has_deriv_at (h : has_fpower_series_at f p x) :
  has_deriv_at f (p 1 (λ _, 1)) x :=
h.has_strict_deriv_at.has_deriv_at

protected lemma has_fpower_series_at.deriv (h : has_fpower_series_at f p x) :
  deriv f x = p 1 (λ _, 1) :=
h.has_deriv_at.deriv

/-- If a function is analytic on a set `s`, so is its derivative. -/
lemma analytic_on.deriv [complete_space F] (h : analytic_on 𝕜 f s) :
  analytic_on 𝕜 (deriv f) s :=
(continuous_linear_map.apply 𝕜 F (1 : 𝕜)).comp_analytic_on h.fderiv

/-- If a function is analytic on a set `s`, so are its successive derivatives. -/
lemma analytic_on.iterated_deriv [complete_space F] (h : analytic_on 𝕜 f s) (n : ℕ) :
  analytic_on 𝕜 (deriv^[n] f) s :=
begin
  induction n with n IH,
  { exact h },
  { simpa only [function.iterate_succ', function.comp_app] using IH.deriv }
end

end deriv
