/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.calculus.fderiv.bilinear

/-!
# Multiplicative operations on derivatives

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

For detailed documentation of the Fréchet derivative,
see the module docstring of `analysis/calculus/fderiv/basic.lean`.

This file contains the usual formulas (and existence assertions) for the derivative of

* multiplication of a function by a scalar function
* multiplication of two scalar functions
* inverse function (assuming that it exists; the inverse function theorem is in `../inverse.lean`)
-/

open filter asymptotics continuous_linear_map set metric
open_locale topology classical nnreal filter asymptotics ennreal

noncomputable theory


section

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
variables {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_add_comm_group G'] [normed_space 𝕜 G']

variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}

section clm_comp_apply
/-! ### Derivative of the pointwise composition/application of continuous linear maps -/

variables {H : Type*} [normed_add_comm_group H] [normed_space 𝕜 H] {c : E → G →L[𝕜] H}
  {c' : E →L[𝕜] G →L[𝕜] H} {d : E → F →L[𝕜] G} {d' : E →L[𝕜] F →L[𝕜] G} {u : E → G}
  {u' : E →L[𝕜] G}

lemma has_strict_fderiv_at.clm_comp (hc : has_strict_fderiv_at c c' x)
  (hd : has_strict_fderiv_at d d' x) : has_strict_fderiv_at (λ y, (c y).comp (d y))
  ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
(is_bounded_bilinear_map_comp.has_strict_fderiv_at (c x, d x)).comp x $ hc.prod hd

lemma has_fderiv_within_at.clm_comp (hc : has_fderiv_within_at c c' s x)
  (hd : has_fderiv_within_at d d' s x) : has_fderiv_within_at (λ y, (c y).comp (d y))
  ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') s x :=
(is_bounded_bilinear_map_comp.has_fderiv_at (c x, d x)).comp_has_fderiv_within_at x $ hc.prod hd

lemma has_fderiv_at.clm_comp (hc : has_fderiv_at c c' x)
  (hd : has_fderiv_at d d' x) : has_fderiv_at (λ y, (c y).comp (d y))
  ((compL 𝕜 F G H (c x)).comp d' + ((compL 𝕜 F G H).flip (d x)).comp c') x :=
(is_bounded_bilinear_map_comp.has_fderiv_at (c x, d x)).comp x $ hc.prod hd

lemma differentiable_within_at.clm_comp
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  differentiable_within_at 𝕜 (λ y, (c y).comp (d y)) s x :=
(hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.clm_comp (hc : differentiable_at 𝕜 c x)
  (hd : differentiable_at 𝕜 d x) : differentiable_at 𝕜 (λ y, (c y).comp (d y)) x :=
(hc.has_fderiv_at.clm_comp hd.has_fderiv_at).differentiable_at

lemma differentiable_on.clm_comp (hc : differentiable_on 𝕜 c s) (hd : differentiable_on 𝕜 d s) :
  differentiable_on 𝕜 (λ y, (c y).comp (d y)) s :=
λx hx, (hc x hx).clm_comp (hd x hx)

lemma differentiable.clm_comp (hc : differentiable 𝕜 c) (hd : differentiable 𝕜 d) :
  differentiable 𝕜 (λ y, (c y).comp (d y)) :=
λx, (hc x).clm_comp (hd x)

lemma fderiv_within_clm_comp (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  fderiv_within 𝕜 (λ y, (c y).comp (d y)) s x =
    (compL 𝕜 F G H (c x)).comp (fderiv_within 𝕜 d s x) +
    ((compL 𝕜 F G H).flip (d x)).comp (fderiv_within 𝕜 c s x) :=
(hc.has_fderiv_within_at.clm_comp hd.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_clm_comp (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  fderiv 𝕜 (λ y, (c y).comp (d y)) x =
    (compL 𝕜 F G H (c x)).comp (fderiv 𝕜 d x) +
    ((compL 𝕜 F G H).flip (d x)).comp (fderiv 𝕜 c x) :=
(hc.has_fderiv_at.clm_comp hd.has_fderiv_at).fderiv

lemma has_strict_fderiv_at.clm_apply (hc : has_strict_fderiv_at c c' x)
  (hu : has_strict_fderiv_at u u' x) :
  has_strict_fderiv_at (λ y, (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
(is_bounded_bilinear_map_apply.has_strict_fderiv_at (c x, u x)).comp x (hc.prod hu)

lemma has_fderiv_within_at.clm_apply (hc : has_fderiv_within_at c c' s x)
  (hu : has_fderiv_within_at u u' s x) :
  has_fderiv_within_at (λ y, (c y) (u y)) ((c x).comp u' + c'.flip (u x)) s x :=
(is_bounded_bilinear_map_apply.has_fderiv_at (c x, u x)).comp_has_fderiv_within_at x (hc.prod hu)

lemma has_fderiv_at.clm_apply (hc : has_fderiv_at c c' x) (hu : has_fderiv_at u u' x) :
  has_fderiv_at (λ y, (c y) (u y)) ((c x).comp u' + c'.flip (u x)) x :=
(is_bounded_bilinear_map_apply.has_fderiv_at (c x, u x)).comp x (hc.prod hu)

lemma differentiable_within_at.clm_apply
  (hc : differentiable_within_at 𝕜 c s x) (hu : differentiable_within_at 𝕜 u s x) :
  differentiable_within_at 𝕜 (λ y, (c y) (u y)) s x :=
(hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).differentiable_within_at

lemma differentiable_at.clm_apply (hc : differentiable_at 𝕜 c x)
  (hu : differentiable_at 𝕜 u x) : differentiable_at 𝕜 (λ y, (c y) (u y)) x :=
(hc.has_fderiv_at.clm_apply hu.has_fderiv_at).differentiable_at

lemma differentiable_on.clm_apply (hc : differentiable_on 𝕜 c s) (hu : differentiable_on 𝕜 u s) :
  differentiable_on 𝕜 (λ y, (c y) (u y)) s :=
λx hx, (hc x hx).clm_apply (hu x hx)

lemma differentiable.clm_apply (hc : differentiable 𝕜 c) (hu : differentiable 𝕜 u) :
  differentiable 𝕜 (λ y, (c y) (u y)) :=
λx, (hc x).clm_apply (hu x)

lemma fderiv_within_clm_apply (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hu : differentiable_within_at 𝕜 u s x) :
  fderiv_within 𝕜 (λ y, (c y) (u y)) s x =
    ((c x).comp (fderiv_within 𝕜 u s x) + (fderiv_within 𝕜 c s x).flip (u x)) :=
(hc.has_fderiv_within_at.clm_apply hu.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_clm_apply (hc : differentiable_at 𝕜 c x) (hu : differentiable_at 𝕜 u x) :
  fderiv 𝕜 (λ y, (c y) (u y)) x = ((c x).comp (fderiv 𝕜 u x) + (fderiv 𝕜 c x).flip (u x)) :=
(hc.has_fderiv_at.clm_apply hu.has_fderiv_at).fderiv

end clm_comp_apply

section smul
/-! ### Derivative of the product of a scalar-valued function and a vector-valued function

If `c` is a differentiable scalar-valued function and `f` is a differentiable vector-valued
function, then `λ x, c x • f x` is differentiable as well. Lemmas in this section works for
function `c` taking values in the base field, as well as in a normed algebra over the base
field: e.g., they work for `c : E → ℂ` and `f : E → F` provided that `F` is a complex
normed vector space.
-/

variables {𝕜' : Type*} [nontrivially_normed_field 𝕜'] [normed_algebra 𝕜 𝕜']
  [normed_space 𝕜' F] [is_scalar_tower 𝕜 𝕜' F]
variables {c : E → 𝕜'} {c' : E →L[𝕜] 𝕜'}

theorem has_strict_fderiv_at.smul (hc : has_strict_fderiv_at c c' x)
  (hf : has_strict_fderiv_at f f' x) :
  has_strict_fderiv_at (λ y, c y • f y) (c x • f' + c'.smul_right (f x)) x :=
(is_bounded_bilinear_map_smul.has_strict_fderiv_at (c x, f x)).comp x $
  hc.prod hf

theorem has_fderiv_within_at.smul
  (hc : has_fderiv_within_at c c' s x) (hf : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at (λ y, c y • f y) (c x • f' + c'.smul_right (f x)) s x :=
(is_bounded_bilinear_map_smul.has_fderiv_at (c x, f x)).comp_has_fderiv_within_at x $
  hc.prod hf

theorem has_fderiv_at.smul (hc : has_fderiv_at c c' x) (hf : has_fderiv_at f f' x) :
  has_fderiv_at (λ y, c y • f y) (c x • f' + c'.smul_right (f x)) x :=
(is_bounded_bilinear_map_smul.has_fderiv_at (c x, f x)).comp x $
  hc.prod hf

lemma differentiable_within_at.smul
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  differentiable_within_at 𝕜 (λ y, c y • f y) s x :=
(hc.has_fderiv_within_at.smul hf.has_fderiv_within_at).differentiable_within_at

@[simp] lemma differentiable_at.smul (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  differentiable_at 𝕜 (λ y, c y • f y) x :=
(hc.has_fderiv_at.smul hf.has_fderiv_at).differentiable_at

lemma differentiable_on.smul (hc : differentiable_on 𝕜 c s) (hf : differentiable_on 𝕜 f s) :
  differentiable_on 𝕜 (λ y, c y • f y) s :=
λx hx, (hc x hx).smul (hf x hx)

@[simp] lemma differentiable.smul (hc : differentiable 𝕜 c) (hf : differentiable 𝕜 f) :
  differentiable 𝕜 (λ y, c y • f y) :=
λx, (hc x).smul (hf x)

lemma fderiv_within_smul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hf : differentiable_within_at 𝕜 f s x) :
  fderiv_within 𝕜 (λ y, c y • f y) s x =
    c x • fderiv_within 𝕜 f s x + (fderiv_within 𝕜 c s x).smul_right (f x) :=
(hc.has_fderiv_within_at.smul hf.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_smul (hc : differentiable_at 𝕜 c x) (hf : differentiable_at 𝕜 f x) :
  fderiv 𝕜 (λ y, c y • f y) x =
    c x • fderiv 𝕜 f x + (fderiv 𝕜 c x).smul_right (f x) :=
(hc.has_fderiv_at.smul hf.has_fderiv_at).fderiv

theorem has_strict_fderiv_at.smul_const (hc : has_strict_fderiv_at c c' x) (f : F) :
  has_strict_fderiv_at (λ y, c y • f) (c'.smul_right f) x :=
by simpa only [smul_zero, zero_add] using hc.smul (has_strict_fderiv_at_const f x)

theorem has_fderiv_within_at.smul_const (hc : has_fderiv_within_at c c' s x) (f : F) :
  has_fderiv_within_at (λ y, c y • f) (c'.smul_right f) s x :=
by simpa only [smul_zero, zero_add] using hc.smul (has_fderiv_within_at_const f x s)

theorem has_fderiv_at.smul_const (hc : has_fderiv_at c c' x) (f : F) :
  has_fderiv_at (λ y, c y • f) (c'.smul_right f) x :=
by simpa only [smul_zero, zero_add] using hc.smul (has_fderiv_at_const f x)

lemma differentiable_within_at.smul_const
  (hc : differentiable_within_at 𝕜 c s x) (f : F) :
  differentiable_within_at 𝕜 (λ y, c y • f) s x :=
(hc.has_fderiv_within_at.smul_const f).differentiable_within_at

lemma differentiable_at.smul_const (hc : differentiable_at 𝕜 c x) (f : F) :
  differentiable_at 𝕜 (λ y, c y • f) x :=
(hc.has_fderiv_at.smul_const f).differentiable_at

lemma differentiable_on.smul_const (hc : differentiable_on 𝕜 c s) (f : F) :
  differentiable_on 𝕜 (λ y, c y • f) s :=
λx hx, (hc x hx).smul_const f

lemma differentiable.smul_const (hc : differentiable 𝕜 c) (f : F) :
  differentiable 𝕜 (λ y, c y • f) :=
λx, (hc x).smul_const f

lemma fderiv_within_smul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (f : F) :
  fderiv_within 𝕜 (λ y, c y • f) s x =
    (fderiv_within 𝕜 c s x).smul_right f :=
(hc.has_fderiv_within_at.smul_const f).fderiv_within hxs

lemma fderiv_smul_const (hc : differentiable_at 𝕜 c x) (f : F) :
  fderiv 𝕜 (λ y, c y • f) x = (fderiv 𝕜 c x).smul_right f :=
(hc.has_fderiv_at.smul_const f).fderiv

end smul

section mul
/-! ### Derivative of the product of two functions -/

variables {𝔸 𝔸' : Type*} [normed_ring 𝔸] [normed_comm_ring 𝔸'] [normed_algebra 𝕜 𝔸]
  [normed_algebra 𝕜 𝔸'] {a b : E → 𝔸} {a' b' : E →L[𝕜] 𝔸} {c d : E → 𝔸'} {c' d' : E →L[𝕜] 𝔸'}

theorem has_strict_fderiv_at.mul' {x : E} (ha : has_strict_fderiv_at a a' x)
  (hb : has_strict_fderiv_at b b' x) :
  has_strict_fderiv_at (λ y, a y * b y) (a x • b' + a'.smul_right (b x)) x :=
((continuous_linear_map.mul 𝕜 𝔸).is_bounded_bilinear_map.has_strict_fderiv_at (a x, b x)).comp x
  (ha.prod hb)

theorem has_strict_fderiv_at.mul
  (hc : has_strict_fderiv_at c c' x) (hd : has_strict_fderiv_at d d' x) :
  has_strict_fderiv_at (λ y, c y * d y) (c x • d' + d x • c') x :=
by { convert hc.mul' hd, ext z, apply mul_comm }

theorem has_fderiv_within_at.mul'
  (ha : has_fderiv_within_at a a' s x) (hb : has_fderiv_within_at b b' s x) :
  has_fderiv_within_at (λ y, a y * b y) (a x • b' + a'.smul_right (b x)) s x :=
((continuous_linear_map.mul 𝕜 𝔸).is_bounded_bilinear_map.has_fderiv_at
  (a x, b x)).comp_has_fderiv_within_at x (ha.prod hb)

theorem has_fderiv_within_at.mul
  (hc : has_fderiv_within_at c c' s x) (hd : has_fderiv_within_at d d' s x) :
  has_fderiv_within_at (λ y, c y * d y) (c x • d' + d x • c') s x :=
by { convert hc.mul' hd, ext z, apply mul_comm }

theorem has_fderiv_at.mul'
  (ha : has_fderiv_at a a' x) (hb : has_fderiv_at b b' x) :
  has_fderiv_at (λ y, a y * b y) (a x • b' + a'.smul_right (b x)) x :=
((continuous_linear_map.mul 𝕜 𝔸).is_bounded_bilinear_map.has_fderiv_at (a x, b x)).comp x
  (ha.prod hb)

theorem has_fderiv_at.mul (hc : has_fderiv_at c c' x) (hd : has_fderiv_at d d' x) :
  has_fderiv_at (λ y, c y * d y) (c x • d' + d x • c') x :=
by { convert hc.mul' hd, ext z, apply mul_comm }

lemma differentiable_within_at.mul
  (ha : differentiable_within_at 𝕜 a s x) (hb : differentiable_within_at 𝕜 b s x) :
  differentiable_within_at 𝕜 (λ y, a y * b y) s x :=
(ha.has_fderiv_within_at.mul' hb.has_fderiv_within_at).differentiable_within_at

@[simp] lemma differentiable_at.mul (ha : differentiable_at 𝕜 a x) (hb : differentiable_at 𝕜 b x) :
  differentiable_at 𝕜 (λ y, a y * b y) x :=
(ha.has_fderiv_at.mul' hb.has_fderiv_at).differentiable_at

lemma differentiable_on.mul (ha : differentiable_on 𝕜 a s) (hb : differentiable_on 𝕜 b s) :
  differentiable_on 𝕜 (λ y, a y * b y) s :=
λx hx, (ha x hx).mul (hb x hx)

@[simp] lemma differentiable.mul (ha : differentiable 𝕜 a) (hb : differentiable 𝕜 b) :
  differentiable 𝕜 (λ y, a y * b y) :=
λx, (ha x).mul (hb x)

lemma differentiable_within_at.pow (ha : differentiable_within_at 𝕜 a s x) :
  ∀ n : ℕ, differentiable_within_at 𝕜 (λ x, a x ^ n) s x
| 0 := by simp only [pow_zero, differentiable_within_at_const]
| (n + 1) := by simp only [pow_succ, differentiable_within_at.pow n, ha.mul]

@[simp] lemma differentiable_at.pow (ha : differentiable_at 𝕜 a x) (n : ℕ) :
  differentiable_at 𝕜 (λ x, a x ^ n) x :=
differentiable_within_at_univ.mp $ ha.differentiable_within_at.pow n

lemma differentiable_on.pow (ha : differentiable_on 𝕜 a s) (n : ℕ) :
  differentiable_on 𝕜 (λ x, a x ^ n) s :=
λ x h, (ha x h).pow n

@[simp] lemma differentiable.pow (ha : differentiable 𝕜 a) (n : ℕ) :
  differentiable 𝕜 (λ x, a x ^ n) :=
λx, (ha x).pow n

lemma fderiv_within_mul' (hxs : unique_diff_within_at 𝕜 s x)
  (ha : differentiable_within_at 𝕜 a s x) (hb : differentiable_within_at 𝕜 b s x) :
  fderiv_within 𝕜 (λ y, a y * b y) s x =
    a x • fderiv_within 𝕜 b s x + (fderiv_within 𝕜 a s x).smul_right (b x) :=
(ha.has_fderiv_within_at.mul' hb.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_within_mul (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (hd : differentiable_within_at 𝕜 d s x) :
  fderiv_within 𝕜 (λ y, c y * d y) s x =
    c x • fderiv_within 𝕜 d s x + d x • fderiv_within 𝕜 c s x :=
(hc.has_fderiv_within_at.mul hd.has_fderiv_within_at).fderiv_within hxs

lemma fderiv_mul' (ha : differentiable_at 𝕜 a x) (hb : differentiable_at 𝕜 b x) :
  fderiv 𝕜 (λ y, a y * b y) x =
    a x • fderiv 𝕜 b x + (fderiv 𝕜 a x).smul_right (b x) :=
(ha.has_fderiv_at.mul' hb.has_fderiv_at).fderiv

lemma fderiv_mul (hc : differentiable_at 𝕜 c x) (hd : differentiable_at 𝕜 d x) :
  fderiv 𝕜 (λ y, c y * d y) x =
    c x • fderiv 𝕜 d x + d x • fderiv 𝕜 c x :=
(hc.has_fderiv_at.mul hd.has_fderiv_at).fderiv

theorem has_strict_fderiv_at.mul_const' (ha : has_strict_fderiv_at a a' x) (b : 𝔸) :
  has_strict_fderiv_at (λ y, a y * b) (a'.smul_right b) x :=
(((continuous_linear_map.mul 𝕜 𝔸).flip b).has_strict_fderiv_at).comp x ha

theorem has_strict_fderiv_at.mul_const (hc : has_strict_fderiv_at c c' x) (d : 𝔸') :
  has_strict_fderiv_at (λ y, c y * d) (d • c') x :=
by { convert hc.mul_const' d, ext z, apply mul_comm }

theorem has_fderiv_within_at.mul_const' (ha : has_fderiv_within_at a a' s x) (b : 𝔸) :
  has_fderiv_within_at (λ y, a y * b) (a'.smul_right b) s x :=
(((continuous_linear_map.mul 𝕜 𝔸).flip b).has_fderiv_at).comp_has_fderiv_within_at x ha

theorem has_fderiv_within_at.mul_const (hc : has_fderiv_within_at c c' s x) (d : 𝔸') :
  has_fderiv_within_at (λ y, c y * d) (d • c') s x :=
by { convert hc.mul_const' d, ext z, apply mul_comm }

theorem has_fderiv_at.mul_const' (ha : has_fderiv_at a a' x) (b : 𝔸) :
  has_fderiv_at (λ y, a y * b) (a'.smul_right b) x :=
(((continuous_linear_map.mul 𝕜 𝔸).flip b).has_fderiv_at).comp x ha

theorem has_fderiv_at.mul_const (hc : has_fderiv_at c c' x) (d : 𝔸') :
  has_fderiv_at (λ y, c y * d) (d • c') x :=
by { convert hc.mul_const' d, ext z, apply mul_comm }

lemma differentiable_within_at.mul_const
  (ha : differentiable_within_at 𝕜 a s x) (b : 𝔸) :
  differentiable_within_at 𝕜 (λ y, a y * b) s x :=
(ha.has_fderiv_within_at.mul_const' b).differentiable_within_at

lemma differentiable_at.mul_const (ha : differentiable_at 𝕜 a x) (b : 𝔸) :
  differentiable_at 𝕜 (λ y, a y * b) x :=
(ha.has_fderiv_at.mul_const' b).differentiable_at

lemma differentiable_on.mul_const (ha : differentiable_on 𝕜 a s) (b : 𝔸) :
  differentiable_on 𝕜 (λ y, a y * b) s :=
λx hx, (ha x hx).mul_const b

lemma differentiable.mul_const (ha : differentiable 𝕜 a) (b : 𝔸) :
  differentiable 𝕜 (λ y, a y * b) :=
λx, (ha x).mul_const b

lemma fderiv_within_mul_const' (hxs : unique_diff_within_at 𝕜 s x)
  (ha : differentiable_within_at 𝕜 a s x) (b : 𝔸) :
  fderiv_within 𝕜 (λ y, a y * b) s x = (fderiv_within 𝕜 a s x).smul_right b :=
(ha.has_fderiv_within_at.mul_const' b).fderiv_within hxs

lemma fderiv_within_mul_const (hxs : unique_diff_within_at 𝕜 s x)
  (hc : differentiable_within_at 𝕜 c s x) (d : 𝔸') :
  fderiv_within 𝕜 (λ y, c y * d) s x = d • fderiv_within 𝕜 c s x :=
(hc.has_fderiv_within_at.mul_const d).fderiv_within hxs

lemma fderiv_mul_const' (ha : differentiable_at 𝕜 a x) (b : 𝔸) :
  fderiv 𝕜 (λ y, a y * b) x = (fderiv 𝕜 a x).smul_right b :=
(ha.has_fderiv_at.mul_const' b).fderiv

lemma fderiv_mul_const (hc : differentiable_at 𝕜 c x) (d : 𝔸') :
  fderiv 𝕜 (λ y, c y * d) x = d • fderiv 𝕜 c x :=
(hc.has_fderiv_at.mul_const d).fderiv

theorem has_strict_fderiv_at.const_mul (ha : has_strict_fderiv_at a a' x) (b : 𝔸) :
  has_strict_fderiv_at (λ y, b * a y) (b • a') x :=
(((continuous_linear_map.mul 𝕜 𝔸) b).has_strict_fderiv_at).comp x ha

theorem has_fderiv_within_at.const_mul
  (ha : has_fderiv_within_at a a' s x) (b : 𝔸) :
  has_fderiv_within_at (λ y, b * a y) (b • a') s x :=
(((continuous_linear_map.mul 𝕜 𝔸) b).has_fderiv_at).comp_has_fderiv_within_at x ha

theorem has_fderiv_at.const_mul (ha : has_fderiv_at a a' x) (b : 𝔸) :
  has_fderiv_at (λ y, b * a y) (b • a') x :=
(((continuous_linear_map.mul 𝕜 𝔸) b).has_fderiv_at).comp x ha

lemma differentiable_within_at.const_mul
  (ha : differentiable_within_at 𝕜 a s x) (b : 𝔸) :
  differentiable_within_at 𝕜 (λ y, b * a y) s x :=
(ha.has_fderiv_within_at.const_mul b).differentiable_within_at

lemma differentiable_at.const_mul (ha : differentiable_at 𝕜 a x) (b : 𝔸) :
  differentiable_at 𝕜 (λ y, b * a y) x :=
(ha.has_fderiv_at.const_mul b).differentiable_at

lemma differentiable_on.const_mul (ha : differentiable_on 𝕜 a s) (b : 𝔸) :
  differentiable_on 𝕜 (λ y, b * a y) s :=
λx hx, (ha x hx).const_mul b

lemma differentiable.const_mul (ha : differentiable 𝕜 a) (b : 𝔸) :
  differentiable 𝕜 (λ y, b * a y) :=
λx, (ha x).const_mul b

lemma fderiv_within_const_mul (hxs : unique_diff_within_at 𝕜 s x)
  (ha : differentiable_within_at 𝕜 a s x) (b : 𝔸) :
  fderiv_within 𝕜 (λ y, b * a y) s x = b • fderiv_within 𝕜 a s x :=
(ha.has_fderiv_within_at.const_mul b).fderiv_within hxs

lemma fderiv_const_mul (ha : differentiable_at 𝕜 a x) (b : 𝔸) :
  fderiv 𝕜 (λ y, b * a y) x = b • fderiv 𝕜 a x :=
(ha.has_fderiv_at.const_mul b).fderiv

end mul

section algebra_inverse
variables {R : Type*} [normed_ring R] [normed_algebra 𝕜 R] [complete_space R]
open normed_ring continuous_linear_map ring

/-- At an invertible element `x` of a normed algebra `R`, the Fréchet derivative of the inversion
operation is the linear map `λ t, - x⁻¹ * t * x⁻¹`. -/
lemma has_fderiv_at_ring_inverse (x : Rˣ) :
  has_fderiv_at ring.inverse (-mul_left_right 𝕜 R ↑x⁻¹ ↑x⁻¹) x :=
begin
  have h_is_o : (λ (t : R), inverse (↑x + t) - ↑x⁻¹ + ↑x⁻¹ * t * ↑x⁻¹) =o[𝓝 0] (λ (t : R), t),
  { refine (inverse_add_norm_diff_second_order x).trans_is_o ((is_o_norm_norm).mp _),
    simp only [norm_pow, norm_norm],
    have h12 : 1 < 2 := by norm_num,
    convert (asymptotics.is_o_pow_pow h12).comp_tendsto tendsto_norm_zero,
    ext, simp },
  have h_lim : tendsto (λ (y:R), y - x) (𝓝 x) (𝓝 0),
  { refine tendsto_zero_iff_norm_tendsto_zero.mpr _,
    exact tendsto_iff_norm_tendsto_zero.mp tendsto_id },
  simp only [has_fderiv_at, has_fderiv_at_filter],
  convert h_is_o.comp_tendsto h_lim,
  ext y,
  simp only [coe_comp', function.comp_app, mul_left_right_apply, neg_apply, inverse_unit x,
    units.inv_mul, add_sub_cancel'_right, mul_sub, sub_mul, one_mul, sub_neg_eq_add]
end

lemma differentiable_at_inverse (x : Rˣ) : differentiable_at 𝕜 (@ring.inverse R _) x :=
(has_fderiv_at_ring_inverse x).differentiable_at

lemma fderiv_inverse (x : Rˣ) :
  fderiv 𝕜 (@ring.inverse R _) x = - mul_left_right 𝕜 R ↑x⁻¹ ↑x⁻¹ :=
(has_fderiv_at_ring_inverse x).fderiv

end algebra_inverse

end
