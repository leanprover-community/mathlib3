/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import analysis.inner_product_space.basic
import analysis.special_functions.sqrt

/-!
# Derivative of the inner product

In this file we prove that the inner product and square of the norm in an inner space are
infinitely `ℝ`-smooth. In order to state these results, we need a `normed_space ℝ E`
instance. Though we can deduce this structure from `inner_product_space 𝕜 E`, this instance may be
not definitionally equal to some other “natural” instance. So, we assume `[normed_space ℝ E]`.
-/

noncomputable theory

open is_R_or_C real filter
open_locale big_operators classical topological_space

variables {𝕜 E F : Type*} [is_R_or_C 𝕜]
variables [inner_product_space 𝕜 E] [inner_product_space ℝ F]
local notation `⟪`x`, `y`⟫` := @inner 𝕜 _ _ x y

variables [normed_space ℝ E]

/-- Derivative of the inner product. -/
def fderiv_inner_clm (p : E × E) : E × E →L[ℝ] 𝕜 := is_bounded_bilinear_map_inner.deriv p

@[simp] lemma fderiv_inner_clm_apply (p x : E × E) :
  fderiv_inner_clm  p x = ⟪p.1, x.2⟫ + ⟪x.1, p.2⟫ := rfl

lemma cont_diff_inner {n} : cont_diff ℝ n (λ p : E × E, ⟪p.1, p.2⟫) :=
is_bounded_bilinear_map_inner.cont_diff

lemma cont_diff_at_inner {p : E × E} {n} :
  cont_diff_at ℝ n (λ p : E × E, ⟪p.1, p.2⟫) p :=
cont_diff_inner.cont_diff_at

lemma differentiable_inner : differentiable ℝ (λ p : E × E, ⟪p.1, p.2⟫) :=
is_bounded_bilinear_map_inner.differentiable_at

variables {G : Type*} [normed_group G] [normed_space ℝ G]
  {f g : G → E} {f' g' : G →L[ℝ] E} {s : set G} {x : G} {n : with_top ℕ}

include 𝕜

lemma cont_diff_within_at.inner (hf : cont_diff_within_at ℝ n f s x)
  (hg : cont_diff_within_at ℝ n g s x) :
  cont_diff_within_at ℝ n (λ x, ⟪f x, g x⟫) s x :=
cont_diff_at_inner.comp_cont_diff_within_at x (hf.prod hg)

lemma cont_diff_at.inner (hf : cont_diff_at ℝ n f x)
  (hg : cont_diff_at ℝ n g x) :
  cont_diff_at ℝ n (λ x, ⟪f x, g x⟫) x :=
hf.inner hg

lemma cont_diff_on.inner (hf : cont_diff_on ℝ n f s) (hg : cont_diff_on ℝ n g s) :
  cont_diff_on ℝ n (λ x, ⟪f x, g x⟫) s :=
λ x hx, (hf x hx).inner (hg x hx)

lemma cont_diff.inner (hf : cont_diff ℝ n f) (hg : cont_diff ℝ n g) :
  cont_diff ℝ n (λ x, ⟪f x, g x⟫) :=
cont_diff_inner.comp (hf.prod hg)

lemma has_fderiv_within_at.inner (hf : has_fderiv_within_at f f' s x)
  (hg : has_fderiv_within_at g g' s x) :
  has_fderiv_within_at (λ t, ⟪f t, g t⟫) ((fderiv_inner_clm (f x, g x)).comp $ f'.prod g') s x :=
(is_bounded_bilinear_map_inner.has_fderiv_at (f x, g x)).comp_has_fderiv_within_at x (hf.prod hg)

lemma has_strict_fderiv_at.inner (hf : has_strict_fderiv_at f f' x)
  (hg : has_strict_fderiv_at g g' x) :
  has_strict_fderiv_at (λ t, ⟪f t, g t⟫) ((fderiv_inner_clm (f x, g x)).comp $ f'.prod g') x :=
(is_bounded_bilinear_map_inner.has_strict_fderiv_at (f x, g x)).comp x (hf.prod hg)

lemma has_fderiv_at.inner (hf : has_fderiv_at f f' x) (hg : has_fderiv_at g g' x) :
  has_fderiv_at (λ t, ⟪f t, g t⟫) ((fderiv_inner_clm (f x, g x)).comp $ f'.prod g') x :=
(is_bounded_bilinear_map_inner.has_fderiv_at (f x, g x)).comp x (hf.prod hg)

lemma has_deriv_within_at.inner {f g : ℝ → E} {f' g' : E} {s : set ℝ} {x : ℝ}
  (hf : has_deriv_within_at f f' s x) (hg : has_deriv_within_at g g' s x) :
  has_deriv_within_at (λ t, ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) s x :=
by simpa using (hf.has_fderiv_within_at.inner hg.has_fderiv_within_at).has_deriv_within_at

lemma has_deriv_at.inner {f g : ℝ → E} {f' g' : E} {x : ℝ} :
  has_deriv_at f f' x →  has_deriv_at g g' x →
  has_deriv_at (λ t, ⟪f t, g t⟫) (⟪f x, g'⟫ + ⟪f', g x⟫) x :=
by simpa only [← has_deriv_within_at_univ] using has_deriv_within_at.inner

lemma differentiable_within_at.inner (hf : differentiable_within_at ℝ f s x)
  (hg : differentiable_within_at ℝ g s x) :
  differentiable_within_at ℝ (λ x, ⟪f x, g x⟫) s x :=
((differentiable_inner _).has_fderiv_at.comp_has_fderiv_within_at x
  (hf.prod hg).has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.inner (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) :
  differentiable_at ℝ (λ x, ⟪f x, g x⟫) x :=
(differentiable_inner _).comp x (hf.prod hg)

lemma differentiable_on.inner (hf : differentiable_on ℝ f s) (hg : differentiable_on ℝ g s) :
  differentiable_on ℝ (λ x, ⟪f x, g x⟫) s :=
λ x hx, (hf x hx).inner (hg x hx)

lemma differentiable.inner (hf : differentiable ℝ f) (hg : differentiable ℝ g) :
  differentiable ℝ (λ x, ⟪f x, g x⟫) :=
λ x, (hf x).inner (hg x)

lemma fderiv_inner_apply (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x) (y : G) :
  fderiv ℝ (λ t, ⟪f t, g t⟫) x y = ⟪f x, fderiv ℝ g x y⟫ + ⟪fderiv ℝ f x y, g x⟫ :=
by { rw [(hf.has_fderiv_at.inner hg.has_fderiv_at).fderiv], refl }

lemma deriv_inner_apply {f g : ℝ → E} {x : ℝ} (hf : differentiable_at ℝ f x)
  (hg : differentiable_at ℝ g x) :
  deriv (λ t, ⟪f t, g t⟫) x = ⟪f x, deriv g x⟫ + ⟪deriv f x, g x⟫ :=
(hf.has_deriv_at.inner hg.has_deriv_at).deriv

lemma cont_diff_norm_sq : cont_diff ℝ n (λ x : E, ∥x∥ ^ 2) :=
begin
  simp only [sq, ← inner_self_eq_norm_mul_norm],
  exact (re_clm : 𝕜 →L[ℝ] ℝ).cont_diff.comp (cont_diff_id.inner cont_diff_id)
end

lemma cont_diff.norm_sq (hf : cont_diff ℝ n f) :
  cont_diff ℝ n (λ x, ∥f x∥ ^ 2) :=
cont_diff_norm_sq.comp hf

lemma cont_diff_within_at.norm_sq (hf : cont_diff_within_at ℝ n f s x) :
  cont_diff_within_at ℝ n (λ y, ∥f y∥ ^ 2) s x :=
cont_diff_norm_sq.cont_diff_at.comp_cont_diff_within_at x hf

lemma cont_diff_at.norm_sq (hf : cont_diff_at ℝ n f x) :
  cont_diff_at ℝ n (λ y, ∥f y∥ ^ 2) x :=
hf.norm_sq

lemma cont_diff_at_norm {x : E} (hx : x ≠ 0) : cont_diff_at ℝ n norm x :=
have ∥id x∥ ^ 2 ≠ 0, from pow_ne_zero _ (norm_pos_iff.2 hx).ne',
by simpa only [id, sqrt_sq, norm_nonneg] using cont_diff_at_id.norm_sq.sqrt this

lemma cont_diff_at.norm (hf : cont_diff_at ℝ n f x) (h0 : f x ≠ 0) :
  cont_diff_at ℝ n (λ y, ∥f y∥) x :=
(cont_diff_at_norm h0).comp x hf

lemma cont_diff_at.dist (hf : cont_diff_at ℝ n f x) (hg : cont_diff_at ℝ n g x)
  (hne : f x ≠ g x) :
  cont_diff_at ℝ n (λ y, dist (f y) (g y)) x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm (sub_ne_zero.2 hne) }

lemma cont_diff_within_at.norm (hf : cont_diff_within_at ℝ n f s x) (h0 : f x ≠ 0) :
  cont_diff_within_at ℝ n (λ y, ∥f y∥) s x :=
(cont_diff_at_norm h0).comp_cont_diff_within_at x hf

lemma cont_diff_within_at.dist (hf : cont_diff_within_at ℝ n f s x)
  (hg : cont_diff_within_at ℝ n g s x) (hne : f x ≠ g x) :
  cont_diff_within_at ℝ n (λ y, dist (f y) (g y)) s x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm (sub_ne_zero.2 hne) }

lemma cont_diff_on.norm_sq (hf : cont_diff_on ℝ n f s) :
  cont_diff_on ℝ n (λ y, ∥f y∥ ^ 2) s :=
(λ x hx, (hf x hx).norm_sq)

lemma cont_diff_on.norm (hf : cont_diff_on ℝ n f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
  cont_diff_on ℝ n (λ y, ∥f y∥) s :=
λ x hx, (hf x hx).norm (h0 x hx)

lemma cont_diff_on.dist (hf : cont_diff_on ℝ n f s)
  (hg : cont_diff_on ℝ n g s) (hne : ∀ x ∈ s, f x ≠ g x) :
  cont_diff_on ℝ n (λ y, dist (f y) (g y)) s :=
λ x hx, (hf x hx).dist (hg x hx) (hne x hx)

lemma cont_diff.norm (hf : cont_diff ℝ n f) (h0 : ∀ x, f x ≠ 0) :
  cont_diff ℝ n (λ y, ∥f y∥) :=
cont_diff_iff_cont_diff_at.2 $ λ x, hf.cont_diff_at.norm (h0 x)

lemma cont_diff.dist (hf : cont_diff ℝ n f) (hg : cont_diff ℝ n g)
  (hne : ∀ x, f x ≠ g x) :
  cont_diff ℝ n (λ y, dist (f y) (g y)) :=
cont_diff_iff_cont_diff_at.2 $
  λ x, hf.cont_diff_at.dist hg.cont_diff_at (hne x)

omit 𝕜
lemma has_strict_fderiv_at_norm_sq (x : F) :
  has_strict_fderiv_at (λ x, ∥x∥ ^ 2) (bit0 (innerSL x)) x :=
begin
  simp only [sq, ← inner_self_eq_norm_mul_norm],
  convert (has_strict_fderiv_at_id x).inner (has_strict_fderiv_at_id x),
  ext y,
  simp [bit0, real_inner_comm],
end
include 𝕜

lemma differentiable_at.norm_sq (hf : differentiable_at ℝ f x) :
  differentiable_at ℝ (λ y, ∥f y∥ ^ 2) x :=
(cont_diff_at_id.norm_sq.differentiable_at le_rfl).comp x hf

lemma differentiable_at.norm (hf : differentiable_at ℝ f x) (h0 : f x ≠ 0) :
  differentiable_at ℝ (λ y, ∥f y∥) x :=
((cont_diff_at_norm h0).differentiable_at le_rfl).comp x hf

lemma differentiable_at.dist (hf : differentiable_at ℝ f x) (hg : differentiable_at ℝ g x)
  (hne : f x ≠ g x) :
  differentiable_at ℝ (λ y, dist (f y) (g y)) x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm (sub_ne_zero.2 hne) }

lemma differentiable.norm_sq (hf : differentiable ℝ f) : differentiable ℝ (λ y, ∥f y∥ ^ 2) :=
λ x, (hf x).norm_sq

lemma differentiable.norm (hf : differentiable ℝ f) (h0 : ∀ x, f x ≠ 0) :
  differentiable ℝ (λ y, ∥f y∥) :=
λ x, (hf x).norm (h0 x)

lemma differentiable.dist (hf : differentiable ℝ f) (hg : differentiable ℝ g)
  (hne : ∀ x, f x ≠ g x) :
  differentiable ℝ (λ y, dist (f y) (g y)) :=
λ x, (hf x).dist (hg x) (hne x)

lemma differentiable_within_at.norm_sq (hf : differentiable_within_at ℝ f s x) :
  differentiable_within_at ℝ (λ y, ∥f y∥ ^ 2) s x :=
(cont_diff_at_id.norm_sq.differentiable_at le_rfl).comp_differentiable_within_at x hf

lemma differentiable_within_at.norm (hf : differentiable_within_at ℝ f s x) (h0 : f x ≠ 0) :
  differentiable_within_at ℝ (λ y, ∥f y∥) s x :=
((cont_diff_at_id.norm h0).differentiable_at le_rfl).comp_differentiable_within_at x hf

lemma differentiable_within_at.dist (hf : differentiable_within_at ℝ f s x)
  (hg : differentiable_within_at ℝ g s x) (hne : f x ≠ g x) :
  differentiable_within_at ℝ (λ y, dist (f y) (g y)) s x :=
by { simp only [dist_eq_norm], exact (hf.sub hg).norm (sub_ne_zero.2 hne) }

lemma differentiable_on.norm_sq (hf : differentiable_on ℝ f s) :
  differentiable_on ℝ (λ y, ∥f y∥ ^ 2) s :=
λ x hx, (hf x hx).norm_sq

lemma differentiable_on.norm (hf : differentiable_on ℝ f s) (h0 : ∀ x ∈ s, f x ≠ 0) :
  differentiable_on ℝ (λ y, ∥f y∥) s :=
λ x hx, (hf x hx).norm (h0 x hx)

lemma differentiable_on.dist (hf : differentiable_on ℝ f s) (hg : differentiable_on ℝ g s)
  (hne : ∀ x ∈ s, f x ≠ g x) :
  differentiable_on ℝ (λ y, dist (f y) (g y)) s :=
λ x hx, (hf x hx).dist (hg x hx) (hne x hx)
