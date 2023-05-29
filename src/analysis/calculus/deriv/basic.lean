/-
Copyright (c) 2019 Gabriel Ebner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gabriel Ebner, Sébastien Gouëzel
-/
import analysis.calculus.fderiv.basic

/-!

# One-dimensional derivatives

This file defines the derivative of a function `f : 𝕜 → F` where `𝕜` is a
normed field and `F` is a normed space over this field. The derivative of
such a function `f` at a point `x` is given by an element `f' : F`.

The theory is developed analogously to the [Fréchet
derivatives](./fderiv.html). We first introduce predicates defined in terms
of the corresponding predicates for Fréchet derivatives:

 - `has_deriv_at_filter f f' x L` states that the function `f` has the
    derivative `f'` at the point `x` as `x` goes along the filter `L`.

 - `has_deriv_within_at f f' s x` states that the function `f` has the
    derivative `f'` at the point `x` within the subset `s`.

 - `has_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x`.

 - `has_strict_deriv_at f f' x` states that the function `f` has the derivative `f'`
    at the point `x` in the sense of strict differentiability, i.e.,
   `f y - f z = (y - z) • f' + o (y - z)` as `y, z → x`.

For the last two notions we also define a functional version:

  - `deriv_within f s x` is a derivative of `f` at `x` within `s`. If the
    derivative does not exist, then `deriv_within f s x` equals zero.

  - `deriv f x` is a derivative of `f` at `x`. If the derivative does not
    exist, then `deriv f x` equals zero.

The theorems `fderiv_within_deriv_within` and `fderiv_deriv` show that the
one-dimensional derivatives coincide with the general Fréchet derivatives.

We also show the existence and compute the derivatives of:
  - constants
  - the identity function
  - linear maps (in `linear.lean`)
  - addition (in `add.lean`)
  - sum of finitely many functions (in `add.lean`)
  - negation (in `add.lean`)
  - subtraction (in `add.lean`)
  - star  (in `star.lean`)
  - multiplication of two functions in `𝕜 → 𝕜` (in `mul.lean`)
  - multiplication of a function in `𝕜 → 𝕜` and of a function in `𝕜 → E` (in `mul.lean`)
  - powers of a function (in `pow.lean` and `zpow.lean`)
  - inverse `x → x⁻¹` (in `inv.lean`)
  - division (in `inv.lean`)
  - composition of a function in `𝕜 → F` with a function in `𝕜 → 𝕜` (in `comp.lean`)
  - composition of a function in `F → E` with a function in `𝕜 → F` (in `comp.lean`)
  - inverse function (assuming that it exists; the inverse function theorem is in `inverse.lean`)
  - polynomials (in `polynomial.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

We set up the simplifier so that it can compute the derivative of simple functions. For instance,
```lean
example (x : ℝ) : deriv (λ x, cos (sin x) * exp x) x = (cos(sin(x))-sin(sin(x))*cos(x))*exp(x) :=
by { simp, ring }
```

## Implementation notes

Most of the theorems are direct restatements of the corresponding theorems
for Fréchet derivatives.

The strategy to construct simp lemmas that give the simplifier the possibility to compute
derivatives is the same as the one for differentiability statements, as explained in `fderiv.lean`.
See the explanations there.
-/

universes u v w
noncomputable theory
open_locale classical topology big_operators filter ennreal
open filter asymptotics set
open continuous_linear_map (smul_right smul_right_one_eq_iff)


variables {𝕜 : Type u} [nontrivially_normed_field 𝕜]
variables {F : Type v} [normed_add_comm_group F] [normed_space 𝕜 F]
variables {E : Type w} [normed_add_comm_group E] [normed_space 𝕜 E]

/--
`f` has the derivative `f'` at the point `x` as `x` goes along the filter `L`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges along the filter `L`.
-/
def has_deriv_at_filter (f : 𝕜 → F) (f' : F) (x : 𝕜) (L : filter 𝕜) :=
has_fderiv_at_filter f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x L

/--
`f` has the derivative `f'` at the point `x` within the subset `s`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def has_deriv_within_at (f : 𝕜 → F) (f' : F) (s : set 𝕜) (x : 𝕜) :=
has_deriv_at_filter f f' x (𝓝[s] x)

/--
`f` has the derivative `f'` at the point `x`.

That is, `f x' = f x + (x' - x) • f' + o(x' - x)` where `x'` converges to `x`.
-/
def has_deriv_at (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
has_deriv_at_filter f f' x (𝓝 x)

/-- `f` has the derivative `f'` at the point `x` in the sense of strict differentiability.

That is, `f y - f z = (y - z) • f' + o(y - z)` as `y, z → x`. -/
def has_strict_deriv_at (f : 𝕜 → F) (f' : F) (x : 𝕜) :=
has_strict_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x

/--
Derivative of `f` at the point `x` within the set `s`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_within_at f f' s x`), then
`f x' = f x + (x' - x) • deriv_within f s x + o(x' - x)` where `x'` converges to `x` inside `s`.
-/
def deriv_within (f : 𝕜 → F) (s : set 𝕜) (x : 𝕜) :=
fderiv_within 𝕜 f s x 1

/--
Derivative of `f` at the point `x`, if it exists.  Zero otherwise.

If the derivative exists (i.e., `∃ f', has_deriv_at f f' x`), then
`f x' = f x + (x' - x) • deriv f x + o(x' - x)` where `x'` converges to `x`.
-/
def deriv (f : 𝕜 → F) (x : 𝕜) :=
fderiv 𝕜 f x 1

variables {f f₀ f₁ g : 𝕜 → F}
variables {f' f₀' f₁' g' : F}
variables {x : 𝕜}
variables {s t : set 𝕜}
variables {L L₁ L₂ : filter 𝕜}

/-- Expressing `has_fderiv_at_filter f f' x L` in terms of `has_deriv_at_filter` -/
lemma has_fderiv_at_filter_iff_has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at_filter f f' x L ↔ has_deriv_at_filter f (f' 1) x L :=
by simp [has_deriv_at_filter]

lemma has_fderiv_at_filter.has_deriv_at_filter {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at_filter f f' x L → has_deriv_at_filter f (f' 1) x L :=
has_fderiv_at_filter_iff_has_deriv_at_filter.mp

/-- Expressing `has_fderiv_within_at f f' s x` in terms of `has_deriv_within_at` -/
lemma has_fderiv_within_at_iff_has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_within_at f f' s x ↔ has_deriv_within_at f (f' 1) s x :=
has_fderiv_at_filter_iff_has_deriv_at_filter

/-- Expressing `has_deriv_within_at f f' s x` in terms of `has_fderiv_within_at` -/
lemma has_deriv_within_at_iff_has_fderiv_within_at {f' : F} :
  has_deriv_within_at f f' s x ↔
  has_fderiv_within_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
iff.rfl

lemma has_fderiv_within_at.has_deriv_within_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_within_at f f' s x → has_deriv_within_at f (f' 1) s x :=
has_fderiv_within_at_iff_has_deriv_within_at.mp

lemma has_deriv_within_at.has_fderiv_within_at {f' : F} :
  has_deriv_within_at f f' s x → has_fderiv_within_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') s x :=
has_deriv_within_at_iff_has_fderiv_within_at.mp

/-- Expressing `has_fderiv_at f f' x` in terms of `has_deriv_at` -/
lemma has_fderiv_at_iff_has_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at f f' x ↔ has_deriv_at f (f' 1) x :=
has_fderiv_at_filter_iff_has_deriv_at_filter

lemma has_fderiv_at.has_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_fderiv_at f f' x → has_deriv_at f (f' 1) x :=
has_fderiv_at_iff_has_deriv_at.mp

lemma has_strict_fderiv_at_iff_has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_strict_fderiv_at f f' x ↔ has_strict_deriv_at f (f' 1) x :=
by simp [has_strict_deriv_at, has_strict_fderiv_at]

protected lemma has_strict_fderiv_at.has_strict_deriv_at {f' : 𝕜 →L[𝕜] F} :
  has_strict_fderiv_at f f' x → has_strict_deriv_at f (f' 1) x :=
has_strict_fderiv_at_iff_has_strict_deriv_at.mp

lemma has_strict_deriv_at_iff_has_strict_fderiv_at :
  has_strict_deriv_at f f' x ↔ has_strict_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
iff.rfl

alias has_strict_deriv_at_iff_has_strict_fderiv_at ↔ has_strict_deriv_at.has_strict_fderiv_at _

/-- Expressing `has_deriv_at f f' x` in terms of `has_fderiv_at` -/
lemma has_deriv_at_iff_has_fderiv_at {f' : F} :
  has_deriv_at f f' x ↔
  has_fderiv_at f (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') x :=
iff.rfl

alias has_deriv_at_iff_has_fderiv_at ↔ has_deriv_at.has_fderiv_at _

lemma deriv_within_zero_of_not_differentiable_within_at
  (h : ¬ differentiable_within_at 𝕜 f s x) : deriv_within f s x = 0 :=
by { unfold deriv_within, rw fderiv_within_zero_of_not_differentiable_within_at, simp, assumption }

lemma differentiable_within_at_of_deriv_within_ne_zero (h : deriv_within f s x ≠ 0) :
  differentiable_within_at 𝕜 f s x :=
not_imp_comm.1 deriv_within_zero_of_not_differentiable_within_at h

lemma deriv_zero_of_not_differentiable_at (h : ¬ differentiable_at 𝕜 f x) : deriv f x = 0 :=
by { unfold deriv, rw fderiv_zero_of_not_differentiable_at, simp, assumption }

lemma differentiable_at_of_deriv_ne_zero (h : deriv f x ≠ 0) : differentiable_at 𝕜 f x :=
not_imp_comm.1 deriv_zero_of_not_differentiable_at h

theorem unique_diff_within_at.eq_deriv (s : set 𝕜) (H : unique_diff_within_at 𝕜 s x)
  (h : has_deriv_within_at f f' s x) (h₁ : has_deriv_within_at f f₁' s x) : f' = f₁' :=
smul_right_one_eq_iff.mp $ unique_diff_within_at.eq H h h₁

theorem has_deriv_at_filter_iff_is_o :
  has_deriv_at_filter f f' x L ↔ (λ x' : 𝕜, f x' - f x - (x' - x) • f') =o[L] (λ x', x' - x) :=
iff.rfl

theorem has_deriv_at_filter_iff_tendsto :
  has_deriv_at_filter f f' x L ↔
  tendsto (λ x' : 𝕜, ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) L (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_within_at_iff_is_o :
  has_deriv_within_at f f' s x
    ↔ (λ x' : 𝕜, f x' - f x - (x' - x) • f') =o[𝓝[s] x] (λ x', x' - x) :=
iff.rfl

theorem has_deriv_within_at_iff_tendsto : has_deriv_within_at f f' s x ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝[s] x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_iff_is_o :
  has_deriv_at f f' x ↔ (λ x' : 𝕜, f x' - f x - (x' - x) • f') =o[𝓝 x] (λ x', x' - x) :=
iff.rfl

theorem has_deriv_at_iff_tendsto : has_deriv_at f f' x ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - (x' - x) • f'‖) (𝓝 x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_deriv_at_filter.is_O_sub (h : has_deriv_at_filter f f' x L) :
  (λ x', f x' - f x) =O[L] (λ x', x' - x) :=
has_fderiv_at_filter.is_O_sub h

theorem has_deriv_at_filter.is_O_sub_rev (hf : has_deriv_at_filter f f' x L) (hf' : f' ≠ 0) :
  (λ x', x' - x) =O[L] (λ x', f x' - f x) :=
suffices antilipschitz_with ‖f'‖₊⁻¹ (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f'), from hf.is_O_sub_rev this,
add_monoid_hom_class.antilipschitz_of_bound (smul_right (1 : 𝕜 →L[𝕜] 𝕜) f') $
  λ x, by simp [norm_smul, ← div_eq_inv_mul, mul_div_cancel _ (mt norm_eq_zero.1 hf')]

theorem has_strict_deriv_at.has_deriv_at (h : has_strict_deriv_at f f' x) :
  has_deriv_at f f' x :=
h.has_fderiv_at
theorem has_deriv_within_at_congr_set' {s t : set 𝕜} (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
    has_deriv_within_at f f' s x ↔ has_deriv_within_at f f' t x :=
has_fderiv_within_at_congr_set' y h

theorem has_deriv_within_at_congr_set {s t : set 𝕜} (h : s =ᶠ[𝓝 x] t) :
    has_deriv_within_at f f' s x ↔ has_deriv_within_at f f' t x :=
has_fderiv_within_at_congr_set h

alias has_deriv_within_at_congr_set ↔ has_deriv_within_at.congr_set _

@[simp] lemma has_deriv_within_at_diff_singleton :
  has_deriv_within_at f f' (s \ {x}) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_diff_singleton _

@[simp] lemma has_deriv_within_at_Ioi_iff_Ici [partial_order 𝕜] :
  has_deriv_within_at f f' (Ioi x) x ↔ has_deriv_within_at f f' (Ici x) x :=
by rw [← Ici_diff_left, has_deriv_within_at_diff_singleton]

alias has_deriv_within_at_Ioi_iff_Ici ↔
  has_deriv_within_at.Ici_of_Ioi has_deriv_within_at.Ioi_of_Ici

@[simp] lemma has_deriv_within_at_Iio_iff_Iic [partial_order 𝕜] :
  has_deriv_within_at f f' (Iio x) x ↔ has_deriv_within_at f f' (Iic x) x :=
by rw [← Iic_diff_right, has_deriv_within_at_diff_singleton]

alias has_deriv_within_at_Iio_iff_Iic ↔
  has_deriv_within_at.Iic_of_Iio has_deriv_within_at.Iio_of_Iic

theorem has_deriv_within_at.Ioi_iff_Ioo [linear_order 𝕜] [order_closed_topology 𝕜] {x y : 𝕜}
  (h : x < y) :
  has_deriv_within_at f f' (Ioo x y) x ↔ has_deriv_within_at f f' (Ioi x) x :=
has_fderiv_within_at_inter $ Iio_mem_nhds h

alias has_deriv_within_at.Ioi_iff_Ioo ↔
  has_deriv_within_at.Ioi_of_Ioo has_deriv_within_at.Ioo_of_Ioi

theorem has_deriv_at_iff_is_o_nhds_zero : has_deriv_at f f' x ↔
  (λh, f (x + h) - f x - h • f') =o[𝓝 0] (λh, h) :=
has_fderiv_at_iff_is_o_nhds_zero

theorem has_deriv_at_filter.mono (h : has_deriv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) :
  has_deriv_at_filter f f' x L₁ :=
has_fderiv_at_filter.mono h hst

theorem has_deriv_within_at.mono (h : has_deriv_within_at f f' t x) (hst : s ⊆ t) :
  has_deriv_within_at f f' s x :=
has_fderiv_within_at.mono h hst

theorem has_deriv_within_at.mono_of_mem (h : has_deriv_within_at f f' t x) (hst : t ∈ 𝓝[s] x) :
  has_deriv_within_at f f' s x :=
has_fderiv_within_at.mono_of_mem h hst

theorem has_deriv_at.has_deriv_at_filter (h : has_deriv_at f f' x) (hL : L ≤ 𝓝 x) :
  has_deriv_at_filter f f' x L :=
has_fderiv_at.has_fderiv_at_filter h hL

theorem has_deriv_at.has_deriv_within_at
  (h : has_deriv_at f f' x) : has_deriv_within_at f f' s x :=
has_fderiv_at.has_fderiv_within_at h

lemma has_deriv_within_at.differentiable_within_at (h : has_deriv_within_at f f' s x) :
  differentiable_within_at 𝕜 f s x :=
has_fderiv_within_at.differentiable_within_at h

lemma has_deriv_at.differentiable_at (h : has_deriv_at f f' x) : differentiable_at 𝕜 f x :=
has_fderiv_at.differentiable_at h

@[simp] lemma has_deriv_within_at_univ : has_deriv_within_at f f' univ x ↔ has_deriv_at f f' x :=
has_fderiv_within_at_univ

theorem has_deriv_at.unique
  (h₀ : has_deriv_at f f₀' x) (h₁ : has_deriv_at f f₁' x) : f₀' = f₁' :=
smul_right_one_eq_iff.mp $ h₀.has_fderiv_at.unique h₁

lemma has_deriv_within_at_inter' (h : t ∈ 𝓝[s] x) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter' h

lemma has_deriv_within_at_inter (h : t ∈ 𝓝 x) :
  has_deriv_within_at f f' (s ∩ t) x ↔ has_deriv_within_at f f' s x :=
has_fderiv_within_at_inter h

lemma has_deriv_within_at.union (hs : has_deriv_within_at f f' s x)
  (ht : has_deriv_within_at f f' t x) :
  has_deriv_within_at f f' (s ∪ t) x :=
hs.has_fderiv_within_at.union ht.has_fderiv_within_at

lemma has_deriv_within_at.nhds_within (h : has_deriv_within_at f f' s x)
  (ht : s ∈ 𝓝[t] x) : has_deriv_within_at f f' t x :=
(has_deriv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

lemma has_deriv_within_at.has_deriv_at (h : has_deriv_within_at f f' s x) (hs : s ∈ 𝓝 x) :
  has_deriv_at f f' x :=
has_fderiv_within_at.has_fderiv_at h hs

lemma differentiable_within_at.has_deriv_within_at (h : differentiable_within_at 𝕜 f s x) :
  has_deriv_within_at f (deriv_within f s x) s x :=
h.has_fderiv_within_at.has_deriv_within_at

lemma differentiable_at.has_deriv_at (h : differentiable_at 𝕜 f x) : has_deriv_at f (deriv f x) x :=
h.has_fderiv_at.has_deriv_at

@[simp] lemma has_deriv_at_deriv_iff : has_deriv_at f (deriv f x) x ↔ differentiable_at 𝕜 f x :=
⟨λ h, h.differentiable_at, λ h, h.has_deriv_at⟩

@[simp] lemma has_deriv_within_at_deriv_within_iff :
  has_deriv_within_at f (deriv_within f s x) s x ↔ differentiable_within_at 𝕜 f s x :=
⟨λ h, h.differentiable_within_at, λ h, h.has_deriv_within_at⟩

lemma differentiable_on.has_deriv_at (h : differentiable_on 𝕜 f s) (hs : s ∈ 𝓝 x) :
  has_deriv_at f (deriv f x) x :=
(h.has_fderiv_at hs).has_deriv_at

lemma has_deriv_at.deriv (h : has_deriv_at f f' x) : deriv f x = f' :=
h.differentiable_at.has_deriv_at.unique h

lemma deriv_eq {f' : 𝕜 → F} (h : ∀ x, has_deriv_at f (f' x) x) : deriv f = f' :=
funext $ λ x, (h x).deriv

lemma has_deriv_within_at.deriv_within
  (h : has_deriv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) :
  deriv_within f s x = f' :=
hxs.eq_deriv _ h.differentiable_within_at.has_deriv_within_at h

lemma fderiv_within_deriv_within : (fderiv_within 𝕜 f s x : 𝕜 → F) 1 = deriv_within f s x :=
rfl

lemma deriv_within_fderiv_within :
  smul_right (1 : 𝕜 →L[𝕜] 𝕜) (deriv_within f s x) = fderiv_within 𝕜 f s x :=
by simp [deriv_within]

lemma fderiv_deriv : (fderiv 𝕜 f x : 𝕜 → F) 1 = deriv f x :=
rfl

lemma deriv_fderiv :
  smul_right (1 : 𝕜 →L[𝕜] 𝕜) (deriv f x) = fderiv 𝕜 f x :=
by simp [deriv]

lemma differentiable_at.deriv_within (h : differentiable_at 𝕜 f x)
  (hxs : unique_diff_within_at 𝕜 s x) : deriv_within f s x = deriv f x :=
by { unfold deriv_within deriv, rw h.fderiv_within hxs }

theorem has_deriv_within_at.deriv_eq_zero (hd : has_deriv_within_at f 0 s x)
  (H : unique_diff_within_at 𝕜 s x) : deriv f x = 0 :=
(em' (differentiable_at 𝕜 f x)).elim deriv_zero_of_not_differentiable_at $
  λ h, H.eq_deriv _ h.has_deriv_at.has_deriv_within_at hd

lemma deriv_within_of_mem (st : t ∈ 𝓝[s] x) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  deriv_within f s x = deriv_within f t x :=
((differentiable_within_at.has_deriv_within_at h).mono_of_mem st).deriv_within ht

lemma deriv_within_subset (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  deriv_within f s x = deriv_within f t x :=
((differentiable_within_at.has_deriv_within_at h).mono st).deriv_within ht

lemma deriv_within_congr_set' (y : 𝕜) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
  deriv_within f s x = deriv_within f t x :=
by simp only [deriv_within, fderiv_within_congr_set' y h]

lemma deriv_within_congr_set (h : s =ᶠ[𝓝 x] t) : deriv_within f s x = deriv_within f t x :=
by simp only [deriv_within, fderiv_within_congr_set h]

@[simp] lemma deriv_within_univ : deriv_within f univ = deriv f :=
by { ext, unfold deriv_within deriv, rw fderiv_within_univ }

lemma deriv_within_inter (ht : t ∈ 𝓝 x) :
  deriv_within f (s ∩ t) x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_inter ht }

lemma deriv_within_of_open (hs : is_open s) (hx : x ∈ s) :
  deriv_within f s x = deriv f x :=
by { unfold deriv_within, rw fderiv_within_of_open hs hx, refl }

lemma deriv_mem_iff {f : 𝕜 → F} {s : set F} {x : 𝕜} :
  deriv f x ∈ s ↔ (differentiable_at 𝕜 f x ∧ deriv f x ∈ s) ∨
    (¬differentiable_at 𝕜 f x ∧ (0 : F) ∈ s) :=
by by_cases hx : differentiable_at 𝕜 f x; simp [deriv_zero_of_not_differentiable_at, *]

lemma deriv_within_mem_iff {f : 𝕜 → F} {t : set 𝕜} {s : set F} {x : 𝕜} :
  deriv_within f t x ∈ s ↔ (differentiable_within_at 𝕜 f t x ∧ deriv_within f t x ∈ s) ∨
    (¬differentiable_within_at 𝕜 f t x ∧ (0 : F) ∈ s) :=
by by_cases hx : differentiable_within_at 𝕜 f t x;
  simp [deriv_within_zero_of_not_differentiable_within_at, *]

lemma differentiable_within_at_Ioi_iff_Ici [partial_order 𝕜] :
  differentiable_within_at 𝕜 f (Ioi x) x ↔ differentiable_within_at 𝕜 f (Ici x) x :=
⟨λ h, h.has_deriv_within_at.Ici_of_Ioi.differentiable_within_at,
λ h, h.has_deriv_within_at.Ioi_of_Ici.differentiable_within_at⟩

-- Golfed while splitting the file
lemma deriv_within_Ioi_eq_Ici {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] (f : ℝ → E)
  (x : ℝ) :
  deriv_within f (Ioi x) x = deriv_within f (Ici x) x :=
begin
  by_cases H : differentiable_within_at ℝ f (Ioi x) x,
  { have A := H.has_deriv_within_at.Ici_of_Ioi,
    have B := (differentiable_within_at_Ioi_iff_Ici.1 H).has_deriv_within_at,
    simpa using (unique_diff_on_Ici x).eq le_rfl A B },
  { rw [deriv_within_zero_of_not_differentiable_within_at H,
      deriv_within_zero_of_not_differentiable_within_at],
    rwa differentiable_within_at_Ioi_iff_Ici at H }
end

section congr
/-! ### Congruence properties of derivatives -/

theorem filter.eventually_eq.has_deriv_at_filter_iff
  (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x) (h₁ : f₀' = f₁') :
  has_deriv_at_filter f₀ f₀' x L ↔ has_deriv_at_filter f₁ f₁' x L :=
h₀.has_fderiv_at_filter_iff hx (by simp [h₁])

lemma has_deriv_at_filter.congr_of_eventually_eq (h : has_deriv_at_filter f f' x L)
  (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : has_deriv_at_filter f₁ f' x L :=
by rwa hL.has_deriv_at_filter_iff hx rfl

lemma has_deriv_within_at.congr_mono (h : has_deriv_within_at f f' s x) (ht : ∀x ∈ t, f₁ x = f x)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_deriv_within_at f₁ f' t x :=
has_fderiv_within_at.congr_mono h ht hx h₁

lemma has_deriv_within_at.congr (h : has_deriv_within_at f f' s x) (hs : ∀x ∈ s, f₁ x = f x)
  (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
h.congr_mono hs hx (subset.refl _)

lemma has_deriv_within_at.congr_of_mem (h : has_deriv_within_at f f' s x) (hs : ∀x ∈ s, f₁ x = f x)
  (hx : x ∈ s) : has_deriv_within_at f₁ f' s x :=
h.congr hs (hs _ hx)

lemma has_deriv_within_at.congr_of_eventually_eq (h : has_deriv_within_at f f' s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : has_deriv_within_at f₁ f' s x :=
has_deriv_at_filter.congr_of_eventually_eq h h₁ hx

lemma has_deriv_within_at.congr_of_eventually_eq_of_mem (h : has_deriv_within_at f f' s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) : has_deriv_within_at f₁ f' s x :=
h.congr_of_eventually_eq h₁ (h₁.eq_of_nhds_within hx)

lemma has_deriv_at.congr_of_eventually_eq (h : has_deriv_at f f' x)
  (h₁ : f₁ =ᶠ[𝓝 x] f) : has_deriv_at f₁ f' x :=
has_deriv_at_filter.congr_of_eventually_eq h h₁ (mem_of_mem_nhds h₁ : _)

lemma filter.eventually_eq.deriv_within_eq (hL : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw hL.fderiv_within_eq hx }

lemma deriv_within_congr (hs : eq_on f₁ f s) (hx : f₁ x = f x) :
  deriv_within f₁ s x = deriv_within f s x :=
by { unfold deriv_within, rw fderiv_within_congr hs hx }

lemma filter.eventually_eq.deriv_eq (hL : f₁ =ᶠ[𝓝 x] f) : deriv f₁ x = deriv f x :=
by { unfold deriv, rwa filter.eventually_eq.fderiv_eq }

protected lemma filter.eventually_eq.deriv (h : f₁ =ᶠ[𝓝 x] f) : deriv f₁ =ᶠ[𝓝 x] deriv f :=
h.eventually_eq_nhds.mono $ λ x h, h.deriv_eq

end congr

section id
/-! ### Derivative of the identity -/
variables (s x L)

theorem has_deriv_at_filter_id : has_deriv_at_filter id 1 x L :=
(has_fderiv_at_filter_id x L).has_deriv_at_filter

theorem has_deriv_within_at_id : has_deriv_within_at id 1 s x :=
has_deriv_at_filter_id _ _

theorem has_deriv_at_id : has_deriv_at id 1 x :=
has_deriv_at_filter_id _ _

theorem has_deriv_at_id' : has_deriv_at (λ (x : 𝕜), x) 1 x :=
has_deriv_at_filter_id _ _

theorem has_strict_deriv_at_id : has_strict_deriv_at id 1 x :=
(has_strict_fderiv_at_id x).has_strict_deriv_at

lemma deriv_id : deriv id x = 1 :=
has_deriv_at.deriv (has_deriv_at_id x)

@[simp] lemma deriv_id' : deriv (@id 𝕜) = λ _, 1 := funext deriv_id

@[simp] lemma deriv_id'' : deriv (λ x : 𝕜, x) = λ _, 1 := deriv_id'

lemma deriv_within_id (hxs : unique_diff_within_at 𝕜 s x) : deriv_within id s x = 1 :=
(has_deriv_within_at_id x s).deriv_within hxs

end id

section const
/-! ### Derivative of constant functions -/
variables (c : F) (s x L)

theorem has_deriv_at_filter_const : has_deriv_at_filter (λ x, c) 0 x L :=
(has_fderiv_at_filter_const c x L).has_deriv_at_filter

theorem has_strict_deriv_at_const : has_strict_deriv_at (λ x, c) 0 x :=
(has_strict_fderiv_at_const c x).has_strict_deriv_at

theorem has_deriv_within_at_const : has_deriv_within_at (λ x, c) 0 s x :=
has_deriv_at_filter_const _ _ _

theorem has_deriv_at_const : has_deriv_at (λ x, c) 0 x :=
has_deriv_at_filter_const _ _ _

lemma deriv_const : deriv (λ x, c) x = 0 :=
has_deriv_at.deriv (has_deriv_at_const x c)

@[simp] lemma deriv_const' : deriv (λ x:𝕜, c) = λ x, 0 :=
funext (λ x, deriv_const x c)

lemma deriv_within_const (hxs : unique_diff_within_at 𝕜 s x) : deriv_within (λ x, c) s x = 0 :=
(has_deriv_within_at_const _ _ _).deriv_within hxs

end const

section continuous
/-! ### Continuity of a function admitting a derivative -/

theorem has_deriv_at_filter.tendsto_nhds
  (hL : L ≤ 𝓝 x) (h : has_deriv_at_filter f f' x L) :
  tendsto f L (𝓝 (f x)) :=
h.tendsto_nhds hL

theorem has_deriv_within_at.continuous_within_at
  (h : has_deriv_within_at f f' s x) : continuous_within_at f s x :=
has_deriv_at_filter.tendsto_nhds inf_le_left h

theorem has_deriv_at.continuous_at (h : has_deriv_at f f' x) : continuous_at f x :=
has_deriv_at_filter.tendsto_nhds le_rfl h

protected theorem has_deriv_at.continuous_on {f f' : 𝕜 → F}
  (hderiv : ∀ x ∈ s, has_deriv_at f (f' x) x) : continuous_on f s :=
λ x hx, (hderiv x hx).continuous_at.continuous_within_at

end continuous

