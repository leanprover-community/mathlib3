/-
Copyright (c) 2019 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Sébastien Gouëzel, Yury Kudryashov
-/
import analysis.asymptotics.asymptotic_equivalent
import analysis.calculus.tangent_cone
import analysis.normed_space.bounded_linear_maps

/-!
# The Fréchet derivative

Let `E` and `F` be normed spaces, `f : E → F`, and `f' : E →L[𝕜] F` a
continuous 𝕜-linear map, where `𝕜` is a non-discrete normed field. Then

  `has_fderiv_within_at f f' s x`

says that `f` has derivative `f'` at `x`, where the domain of interest
is restricted to `s`. We also have

  `has_fderiv_at f f' x := has_fderiv_within_at f f' x univ`

Finally,

  `has_strict_fderiv_at f f' x`

means that `f : E → F` has derivative `f' : E →L[𝕜] F` in the sense of strict differentiability,
i.e., `f y - f z - f'(y - z) = o(y - z)` as `y, z → x`. This notion is used in the inverse
function theorem, and is defined here only to avoid proving theorems like
`is_bounded_bilinear_map.has_fderiv_at` twice: first for `has_fderiv_at`, then for
`has_strict_fderiv_at`.

## Main results

In addition to the definition and basic properties of the derivative,
the folder `analysis/calculus/fderiv/` contains the usual formulas
(and existence assertions) for the derivative of
* constants
* the identity
* bounded linear maps (`linear.lean`)
* bounded bilinear maps (`bilinear.lean`)
* sum of two functions (`add.lean`)
* sum of finitely many functions (`add.lean`)
* multiplication of a function by a scalar constant (`add.lean`)
* negative of a function (`add.lean`)
* subtraction of two functions (`add.lean`)
* multiplication of a function by a scalar function (`mul.lean`)
* multiplication of two scalar functions (`mul.lean`)
* composition of functions (the chain rule) (`comp.lean`)
* inverse function (`mul.lean`)
  (assuming that it exists; the inverse function theorem is in `../inverse.lean`)

For most binary operations we also define `const_op` and `op_const` theorems for the cases when
the first or second argument is a constant. This makes writing chains of `has_deriv_at`'s easier,
and they more frequently lead to the desired result.

One can also interpret the derivative of a function `f : 𝕜 → E` as an element of `E` (by identifying
a linear function from `𝕜` to `E` with its value at `1`). Results on the Fréchet derivative are
translated to this more elementary point of view on the derivative in the file `deriv.lean`. The
derivative of polynomials is handled there, as it is naturally one-dimensional.

The simplifier is set up to prove automatically that some functions are differentiable, or
differentiable at a point (but not differentiable on a set or within a set at a point, as checking
automatically that the good domains are mapped one to the other when using composition is not
something the simplifier can easily do). This means that one can write
`example (x : ℝ) : differentiable ℝ (λ x, sin (exp (3 + x^2)) - 5 * cos x) := by simp`.
If there are divisions, one needs to supply to the simplifier proofs that the denominators do
not vanish, as in
```lean
example (x : ℝ) (h : 1 + sin x ≠ 0) : differentiable_at ℝ (λ x, exp x / (1 + sin x)) x :=
by simp [h]
```
Of course, these examples only work once `exp`, `cos` and `sin` have been shown to be
differentiable, in `analysis.special_functions.trigonometric`.

The simplifier is not set up to compute the Fréchet derivative of maps (as these are in general
complicated multidimensional linear maps), but it will compute one-dimensional derivatives,
see `deriv.lean`.

## Implementation details

The derivative is defined in terms of the `is_o` relation, but also
characterized in terms of the `tendsto` relation.

We also introduce predicates `differentiable_within_at 𝕜 f s x` (where `𝕜` is the base field,
`f` the function to be differentiated, `x` the point at which the derivative is asserted to exist,
and `s` the set along which the derivative is defined), as well as `differentiable_at 𝕜 f x`,
`differentiable_on 𝕜 f s` and `differentiable 𝕜 f` to express the existence of a derivative.

To be able to compute with derivatives, we write `fderiv_within 𝕜 f s x` and `fderiv 𝕜 f x`
for some choice of a derivative if it exists, and the zero function otherwise. This choice only
behaves well along sets for which the derivative is unique, i.e., those for which the tangent
directions span a dense subset of the whole space. The predicates `unique_diff_within_at s x` and
`unique_diff_on s`, defined in `tangent_cone.lean` express this property. We prove that indeed
they imply the uniqueness of the derivative. This is satisfied for open subsets, and in particular
for `univ`. This uniqueness only holds when the field is non-discrete, which we request at the very
beginning: otherwise, a derivative can be defined, but it has no interesting properties whatsoever.

To make sure that the simplifier can prove automatically that functions are differentiable, we tag
many lemmas with the `simp` attribute, for instance those saying that the sum of differentiable
functions is differentiable, as well as their product, their cartesian product, and so on. A notable
exception is the chain rule: we do not mark as a simp lemma the fact that, if `f` and `g` are
differentiable, then their composition also is: `simp` would always be able to match this lemma,
by taking `f` or `g` to be the identity. Instead, for every reasonable function (say, `exp`),
we add a lemma that if `f` is differentiable then so is `(λ x, exp (f x))`. This means adding
some boilerplate lemmas, but these can also be useful in their own right.

Tests for this ability of the simplifier (with more examples) are provided in
`tests/differentiable.lean`.

## Tags

derivative, differentiable, Fréchet, calculus

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

/-- A function `f` has the continuous linear map `f'` as derivative along the filter `L` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` converges along the filter `L`. This definition
is designed to be specialized for `L = 𝓝 x` (in `has_fderiv_at`), giving rise to the usual notion
of Fréchet derivative, and for `L = 𝓝[s] x` (in `has_fderiv_within_at`), giving rise to
the notion of Fréchet derivative along the set `s`. -/
def has_fderiv_at_filter (f : E → F) (f' : E →L[𝕜] F) (x : E) (L : filter E) :=
(λ x', f x' - f x - f' (x' - x)) =o[L] (λ x', x' - x)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` within a set `s` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x` inside `s`. -/
def has_fderiv_within_at (f : E → F) (f' : E →L[𝕜] F) (s : set E) (x : E) :=
has_fderiv_at_filter f f' x (𝓝[s] x)

/-- A function `f` has the continuous linear map `f'` as derivative at `x` if
`f x' = f x + f' (x' - x) + o (x' - x)` when `x'` tends to `x`. -/
def has_fderiv_at (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
has_fderiv_at_filter f f' x (𝓝 x)

/-- A function `f` has derivative `f'` at `a` in the sense of *strict differentiability*
if `f x - f y - f' (x - y) = o(x - y)` as `x, y → a`. This form of differentiability is required,
e.g., by the inverse function theorem. Any `C^1` function on a vector space over `ℝ` is strictly
differentiable but this definition works, e.g., for vector spaces over `p`-adic numbers. -/
def has_strict_fderiv_at (f : E → F) (f' : E →L[𝕜] F) (x : E) :=
(λ p : E × E, f p.1 - f p.2 - f' (p.1 - p.2)) =o[𝓝 (x, x)] (λ p : E × E, p.1 - p.2)

variables (𝕜)

/-- A function `f` is differentiable at a point `x` within a set `s` if it admits a derivative
there (possibly non-unique). -/
def differentiable_within_at (f : E → F) (s : set E) (x : E) :=
∃f' : E →L[𝕜] F, has_fderiv_within_at f f' s x

/-- A function `f` is differentiable at a point `x` if it admits a derivative there (possibly
non-unique). -/
def differentiable_at (f : E → F) (x : E) :=
∃f' : E →L[𝕜] F, has_fderiv_at f f' x

/-- If `f` has a derivative at `x` within `s`, then `fderiv_within 𝕜 f s x` is such a derivative.
Otherwise, it is set to `0`. -/
def fderiv_within (f : E → F) (s : set E) (x : E) : E →L[𝕜] F :=
if h : ∃f', has_fderiv_within_at f f' s x then classical.some h else 0

/-- If `f` has a derivative at `x`, then `fderiv 𝕜 f x` is such a derivative. Otherwise, it is
set to `0`. -/
def fderiv (f : E → F) (x : E) : E →L[𝕜] F :=
if h : ∃f', has_fderiv_at f f' x then classical.some h else 0

/-- `differentiable_on 𝕜 f s` means that `f` is differentiable within `s` at any point of `s`. -/
def differentiable_on (f : E → F) (s : set E) :=
∀x ∈ s, differentiable_within_at 𝕜 f s x

/-- `differentiable 𝕜 f` means that `f` is differentiable at any point. -/
def differentiable (f : E → F) :=
∀x, differentiable_at 𝕜 f x

variables {𝕜}
variables {f f₀ f₁ g : E → F}
variables {f' f₀' f₁' g' : E →L[𝕜] F}
variables (e : E →L[𝕜] F)
variables {x : E}
variables {s t : set E}
variables {L L₁ L₂ : filter E}

lemma fderiv_within_zero_of_not_differentiable_within_at
  (h : ¬ differentiable_within_at 𝕜 f s x) : fderiv_within 𝕜 f s x = 0 :=
have ¬ ∃ f', has_fderiv_within_at f f' s x, from h,
by simp [fderiv_within, this]

lemma fderiv_zero_of_not_differentiable_at (h : ¬ differentiable_at 𝕜 f x) : fderiv 𝕜 f x = 0 :=
have ¬ ∃ f', has_fderiv_at f f' x, from h,
by simp [fderiv, this]

section derivative_uniqueness
/- In this section, we discuss the uniqueness of the derivative.
We prove that the definitions `unique_diff_within_at` and `unique_diff_on` indeed imply the
uniqueness of the derivative. -/

/-- If a function f has a derivative f' at x, a rescaled version of f around x converges to f',
i.e., `n (f (x + (1/n) v) - f x)` converges to `f' v`. More generally, if `c n` tends to infinity
and `c n * d n` tends to `v`, then `c n * (f (x + d n) - f x)` tends to `f' v`. This lemma expresses
this fact, for functions having a derivative within a set. Its specific formulation is useful for
tangent cone related discussions. -/
theorem has_fderiv_within_at.lim (h : has_fderiv_within_at f f' s x) {α : Type*} (l : filter α)
  {c : α → 𝕜} {d : α → E} {v : E} (dtop : ∀ᶠ n in l, x + d n ∈ s)
  (clim : tendsto (λ n, ‖c n‖) l at_top)
  (cdlim : tendsto (λ n, c n • d n) l (𝓝 v)) :
  tendsto (λn, c n • (f (x + d n) - f x)) l (𝓝 (f' v)) :=
begin
  have tendsto_arg : tendsto (λ n, x + d n) l (𝓝[s] x),
  { conv in (𝓝[s] x) { rw ← add_zero x },
    rw [nhds_within, tendsto_inf],
    split,
    { apply tendsto_const_nhds.add (tangent_cone_at.lim_zero l clim cdlim) },
    { rwa tendsto_principal } },
  have : (λ y, f y - f x - f' (y - x)) =o[𝓝[s] x] (λ y, y - x) := h,
  have : (λ n, f (x + d n) - f x - f' ((x + d n) - x)) =o[l] (λ n, (x + d n)  - x) :=
    this.comp_tendsto tendsto_arg,
  have : (λ n, f (x + d n) - f x - f' (d n)) =o[l] d := by simpa only [add_sub_cancel'],
  have : (λ n, c n • (f (x + d n) - f x - f' (d n))) =o[l] (λ n, c n • d n) :=
    (is_O_refl c l).smul_is_o this,
  have : (λ n, c n • (f (x + d n) - f x - f' (d n))) =o[l] (λ n, (1:ℝ)) :=
    this.trans_is_O (cdlim.is_O_one ℝ),
  have L1 : tendsto (λn, c n • (f (x + d n) - f x - f' (d n))) l (𝓝 0) :=
    (is_o_one_iff ℝ).1 this,
  have L2 : tendsto (λn, f' (c n • d n)) l (𝓝 (f' v)) :=
    tendsto.comp f'.cont.continuous_at cdlim,
  have L3 : tendsto (λn, (c n • (f (x + d n) - f x - f' (d n)) +  f' (c n • d n)))
            l (𝓝 (0 + f' v)) :=
    L1.add L2,
  have : (λn, (c n • (f (x + d n) - f x - f' (d n)) +  f' (c n • d n)))
          = (λn, c n • (f (x + d n) - f x)),
    by { ext n, simp [smul_add, smul_sub] },
  rwa [this, zero_add] at L3
end

/-- If `f'` and `f₁'` are two derivatives of `f` within `s` at `x`, then they are equal on the
tangent cone to `s` at `x` -/
theorem has_fderiv_within_at.unique_on (hf : has_fderiv_within_at f f' s x)
  (hg : has_fderiv_within_at f f₁' s x) :
  eq_on f' f₁' (tangent_cone_at 𝕜 s x) :=
λ y ⟨c, d, dtop, clim, cdlim⟩,
  tendsto_nhds_unique (hf.lim at_top dtop clim cdlim) (hg.lim at_top dtop clim cdlim)

/-- `unique_diff_within_at` achieves its goal: it implies the uniqueness of the derivative. -/
theorem unique_diff_within_at.eq (H : unique_diff_within_at 𝕜 s x)
  (hf : has_fderiv_within_at f f' s x) (hg : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
continuous_linear_map.ext_on H.1 (hf.unique_on hg)

theorem unique_diff_on.eq (H : unique_diff_on 𝕜 s) (hx : x ∈ s)
  (h : has_fderiv_within_at f f' s x) (h₁ : has_fderiv_within_at f f₁' s x) : f' = f₁' :=
(H x hx).eq h h₁

end derivative_uniqueness

section fderiv_properties
/-! ### Basic properties of the derivative -/

theorem has_fderiv_at_filter_iff_tendsto :
  has_fderiv_at_filter f f' x L ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) L (𝓝 0) :=
have h : ∀ x', ‖x' - x‖ = 0 → ‖f x' - f x - f' (x' - x)‖ = 0, from λ x' hx',
  by { rw [sub_eq_zero.1 (norm_eq_zero.1 hx')], simp },
begin
  unfold has_fderiv_at_filter,
  rw [←is_o_norm_left, ←is_o_norm_right, is_o_iff_tendsto h],
  exact tendsto_congr (λ _, div_eq_inv_mul _ _),
end

theorem has_fderiv_within_at_iff_tendsto : has_fderiv_within_at f f' s x ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝[s] x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_tendsto : has_fderiv_at f f' x ↔
  tendsto (λ x', ‖x' - x‖⁻¹ * ‖f x' - f x - f' (x' - x)‖) (𝓝 x) (𝓝 0) :=
has_fderiv_at_filter_iff_tendsto

theorem has_fderiv_at_iff_is_o_nhds_zero : has_fderiv_at f f' x ↔
  (λ h : E, f (x + h) - f x - f' h) =o[𝓝 0] (λh, h) :=
begin
  rw [has_fderiv_at, has_fderiv_at_filter, ← map_add_left_nhds_zero x, is_o_map],
  simp [(∘)]
end

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. This version
only assumes that `‖f x - f x₀‖ ≤ C * ‖x - x₀‖` in a neighborhood of `x`. -/
lemma has_fderiv_at.le_of_lip' {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : has_fderiv_at f f' x₀)
  {C : ℝ} (hC₀ : 0 ≤ C) (hlip : ∀ᶠ x in 𝓝 x₀, ‖f x - f x₀‖ ≤ C * ‖x - x₀‖) : ‖f'‖ ≤ C :=
begin
  refine le_of_forall_pos_le_add (λ ε ε0, op_norm_le_of_nhds_zero _ _),
  exact add_nonneg hC₀ ε0.le,
  rw [← map_add_left_nhds_zero x₀, eventually_map] at hlip,
  filter_upwards [is_o_iff.1 (has_fderiv_at_iff_is_o_nhds_zero.1 hf) ε0, hlip] with y hy hyC,
  rw add_sub_cancel' at hyC,
  calc ‖f' y‖ ≤ ‖f (x₀ + y) - f x₀‖ + ‖f (x₀ + y) - f x₀ - f' y‖ : norm_le_insert _ _
          ... ≤ C * ‖y‖ + ε * ‖y‖                                : add_le_add hyC hy
          ... = (C + ε) * ‖y‖                                    : (add_mul _ _ _).symm
end

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`. -/
lemma has_fderiv_at.le_of_lip {f : E → F} {f' : E →L[𝕜] F} {x₀ : E} (hf : has_fderiv_at f f' x₀)
  {s : set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : lipschitz_on_with C f s) : ‖f'‖ ≤ C :=
begin
  refine hf.le_of_lip' C.coe_nonneg _,
  filter_upwards [hs] with x hx using hlip.norm_sub_le hx (mem_of_mem_nhds hs),
end

theorem has_fderiv_at_filter.mono (h : has_fderiv_at_filter f f' x L₂) (hst : L₁ ≤ L₂) :
  has_fderiv_at_filter f f' x L₁ :=
h.mono hst

theorem has_fderiv_within_at.mono_of_mem (h : has_fderiv_within_at f f' t x) (hst : t ∈ 𝓝[s] x) :
  has_fderiv_within_at f f' s x :=
h.mono $ nhds_within_le_iff.mpr hst

theorem has_fderiv_within_at.mono (h : has_fderiv_within_at f f' t x) (hst : s ⊆ t) :
  has_fderiv_within_at f f' s x :=
h.mono $ nhds_within_mono _ hst

theorem has_fderiv_at.has_fderiv_at_filter (h : has_fderiv_at f f' x) (hL : L ≤ 𝓝 x) :
  has_fderiv_at_filter f f' x L :=
h.mono hL

theorem has_fderiv_at.has_fderiv_within_at
  (h : has_fderiv_at f f' x) : has_fderiv_within_at f f' s x :=
h.has_fderiv_at_filter inf_le_left

lemma has_fderiv_within_at.differentiable_within_at (h : has_fderiv_within_at f f' s x) :
  differentiable_within_at 𝕜 f s x :=
⟨f', h⟩

lemma has_fderiv_at.differentiable_at (h : has_fderiv_at f f' x) : differentiable_at 𝕜 f x :=
⟨f', h⟩

@[simp] lemma has_fderiv_within_at_univ :
  has_fderiv_within_at f f' univ x ↔ has_fderiv_at f f' x :=
by { simp only [has_fderiv_within_at, nhds_within_univ], refl }

alias has_fderiv_within_at_univ ↔ has_fderiv_within_at.has_fderiv_at_of_univ _

lemma has_fderiv_within_at_insert {y : E} :
  has_fderiv_within_at f f' (insert y s) x ↔ has_fderiv_within_at f f' s x :=
begin
  rcases eq_or_ne x y with rfl|h,
  { simp_rw [has_fderiv_within_at, has_fderiv_at_filter],
    apply asymptotics.is_o_insert,
    simp only [sub_self, map_zero] },
  refine ⟨λ h, h.mono $ subset_insert y s, λ hf, hf.mono_of_mem _⟩,
  simp_rw [nhds_within_insert_of_ne h, self_mem_nhds_within]
end

alias has_fderiv_within_at_insert ↔ has_fderiv_within_at.of_insert has_fderiv_within_at.insert'

lemma has_fderiv_within_at.insert (h : has_fderiv_within_at f f' s x) :
  has_fderiv_within_at f f' (insert x s) x :=
h.insert'

lemma has_fderiv_within_at_diff_singleton (y : E) :
  has_fderiv_within_at f f' (s \ {y}) x ↔ has_fderiv_within_at f f' s x :=
by rw [← has_fderiv_within_at_insert, insert_diff_singleton, has_fderiv_within_at_insert]

lemma has_strict_fderiv_at.is_O_sub (hf : has_strict_fderiv_at f f' x) :
  (λ p : E × E, f p.1 - f p.2) =O[𝓝 (x, x)] (λ p : E × E, p.1 - p.2) :=
hf.is_O.congr_of_sub.2 (f'.is_O_comp _ _)

lemma has_fderiv_at_filter.is_O_sub (h : has_fderiv_at_filter f f' x L) :
  (λ x', f x' - f x) =O[L] (λ x', x' - x) :=
h.is_O.congr_of_sub.2 (f'.is_O_sub _ _)

protected lemma has_strict_fderiv_at.has_fderiv_at (hf : has_strict_fderiv_at f f' x) :
  has_fderiv_at f f' x :=
begin
  rw [has_fderiv_at, has_fderiv_at_filter, is_o_iff],
  exact (λ c hc, tendsto_id.prod_mk_nhds tendsto_const_nhds (is_o_iff.1 hf hc))
end

protected lemma has_strict_fderiv_at.differentiable_at (hf : has_strict_fderiv_at f f' x) :
  differentiable_at 𝕜 f x :=
hf.has_fderiv_at.differentiable_at

/-- If `f` is strictly differentiable at `x` with derivative `f'` and `K > ‖f'‖₊`, then `f` is
`K`-Lipschitz in a neighborhood of `x`. -/
lemma has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt (hf : has_strict_fderiv_at f f' x)
  (K : ℝ≥0) (hK : ‖f'‖₊ < K) : ∃ s ∈ 𝓝 x, lipschitz_on_with K f s :=
begin
  have := hf.add_is_O_with (f'.is_O_with_comp _ _) hK,
  simp only [sub_add_cancel, is_O_with] at this,
  rcases exists_nhds_square this with ⟨U, Uo, xU, hU⟩,
  exact ⟨U, Uo.mem_nhds xU, lipschitz_on_with_iff_norm_sub_le.2 $
    λ x hx y hy, hU (mk_mem_prod hx hy)⟩
end

/-- If `f` is strictly differentiable at `x` with derivative `f'`, then `f` is Lipschitz in a
neighborhood of `x`. See also `has_strict_fderiv_at.exists_lipschitz_on_with_of_nnnorm_lt` for a
more precise statement. -/
lemma has_strict_fderiv_at.exists_lipschitz_on_with (hf : has_strict_fderiv_at f f' x) :
  ∃ K (s ∈ 𝓝 x), lipschitz_on_with K f s :=
(exists_gt _).imp hf.exists_lipschitz_on_with_of_nnnorm_lt

/-- Directional derivative agrees with `has_fderiv`. -/
lemma has_fderiv_at.lim (hf : has_fderiv_at f f' x) (v : E) {α : Type*} {c : α → 𝕜}
  {l : filter α} (hc : tendsto (λ n, ‖c n‖) l at_top) :
  tendsto (λ n, (c n) • (f (x + (c n)⁻¹ • v) - f x)) l (𝓝 (f' v)) :=
begin
  refine (has_fderiv_within_at_univ.2 hf).lim _ univ_mem hc _,
  assume U hU,
  refine (eventually_ne_of_tendsto_norm_at_top hc (0:𝕜)).mono (λ y hy, _),
  convert mem_of_mem_nhds hU,
  dsimp only,
  rw [← mul_smul, mul_inv_cancel hy, one_smul]
end

theorem has_fderiv_at.unique
  (h₀ : has_fderiv_at f f₀' x) (h₁ : has_fderiv_at f f₁' x) : f₀' = f₁' :=
begin
  rw ← has_fderiv_within_at_univ at h₀ h₁,
  exact unique_diff_within_at_univ.eq h₀ h₁
end

lemma has_fderiv_within_at_inter' (h : t ∈ 𝓝[s] x) :
  has_fderiv_within_at f f' (s ∩ t) x ↔ has_fderiv_within_at f f' s x :=
by simp [has_fderiv_within_at, nhds_within_restrict'' s h]

lemma has_fderiv_within_at_inter (h : t ∈ 𝓝 x) :
  has_fderiv_within_at f f' (s ∩ t) x ↔ has_fderiv_within_at f f' s x :=
by simp [has_fderiv_within_at, nhds_within_restrict' s h]

lemma has_fderiv_within_at.union (hs : has_fderiv_within_at f f' s x)
  (ht : has_fderiv_within_at f f' t x) :
  has_fderiv_within_at f f' (s ∪ t) x :=
begin
  simp only [has_fderiv_within_at, nhds_within_union],
  exact hs.sup ht,
end

lemma has_fderiv_within_at.nhds_within (h : has_fderiv_within_at f f' s x)
  (ht : s ∈ 𝓝[t] x) : has_fderiv_within_at f f' t x :=
(has_fderiv_within_at_inter' ht).1 (h.mono (inter_subset_right _ _))

lemma has_fderiv_within_at.has_fderiv_at (h : has_fderiv_within_at f f' s x) (hs : s ∈ 𝓝 x) :
  has_fderiv_at f f' x :=
by rwa [← univ_inter s, has_fderiv_within_at_inter hs, has_fderiv_within_at_univ] at h

lemma differentiable_within_at.differentiable_at
  (h : differentiable_within_at 𝕜 f s x) (hs : s ∈ 𝓝 x) : differentiable_at 𝕜 f x :=
h.imp (λ f' hf', hf'.has_fderiv_at hs)

lemma differentiable_within_at.has_fderiv_within_at (h : differentiable_within_at 𝕜 f s x) :
  has_fderiv_within_at f (fderiv_within 𝕜 f s x) s x :=
begin
  dunfold fderiv_within,
  dunfold differentiable_within_at at h,
  rw dif_pos h,
  exact classical.some_spec h
end

lemma differentiable_at.has_fderiv_at (h : differentiable_at 𝕜 f x) :
  has_fderiv_at f (fderiv 𝕜 f x) x :=
begin
  dunfold fderiv,
  dunfold differentiable_at at h,
  rw dif_pos h,
  exact classical.some_spec h
end

lemma differentiable_on.has_fderiv_at (h : differentiable_on 𝕜 f s) (hs : s ∈ 𝓝 x) :
  has_fderiv_at f (fderiv 𝕜 f x) x :=
((h x (mem_of_mem_nhds hs)).differentiable_at hs).has_fderiv_at

lemma differentiable_on.differentiable_at (h : differentiable_on 𝕜 f s) (hs : s ∈ 𝓝 x) :
  differentiable_at 𝕜 f x :=
(h.has_fderiv_at hs).differentiable_at

lemma differentiable_on.eventually_differentiable_at (h : differentiable_on 𝕜 f s) (hs : s ∈ 𝓝 x) :
  ∀ᶠ y in 𝓝 x, differentiable_at 𝕜 f y :=
(eventually_eventually_nhds.2 hs).mono $ λ y, h.differentiable_at

lemma has_fderiv_at.fderiv (h : has_fderiv_at f f' x) : fderiv 𝕜 f x = f' :=
by { ext, rw h.unique h.differentiable_at.has_fderiv_at }

lemma fderiv_eq {f' : E → E →L[𝕜] F} (h : ∀ x, has_fderiv_at f (f' x) x) : fderiv 𝕜 f = f' :=
funext $ λ x, (h x).fderiv

/-- Converse to the mean value inequality: if `f` is differentiable at `x₀` and `C`-lipschitz
on a neighborhood of `x₀` then it its derivative at `x₀` has norm bounded by `C`.
Version using `fderiv`. -/
lemma fderiv_at.le_of_lip {f : E → F} {x₀ : E} (hf : differentiable_at 𝕜 f x₀)
  {s : set E} (hs : s ∈ 𝓝 x₀) {C : ℝ≥0} (hlip : lipschitz_on_with C f s) : ‖fderiv 𝕜 f x₀‖ ≤ C :=
hf.has_fderiv_at.le_of_lip hs hlip

lemma has_fderiv_within_at.fderiv_within
  (h : has_fderiv_within_at f f' s x) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 f s x = f' :=
(hxs.eq h h.differentiable_within_at.has_fderiv_within_at).symm

/-- If `x` is not in the closure of `s`, then `f` has any derivative at `x` within `s`,
as this statement is empty. -/
lemma has_fderiv_within_at_of_not_mem_closure (h : x ∉ closure s) :
  has_fderiv_within_at f f' s x :=
begin
  simp only [mem_closure_iff_nhds_within_ne_bot, ne_bot_iff, ne.def, not_not] at h,
  simp [has_fderiv_within_at, has_fderiv_at_filter, h, is_o, is_O_with],
end

lemma differentiable_within_at.mono (h : differentiable_within_at 𝕜 f t x) (st : s ⊆ t) :
  differentiable_within_at 𝕜 f s x :=
begin
  rcases h with ⟨f', hf'⟩,
  exact ⟨f', hf'.mono st⟩
end

lemma differentiable_within_at.mono_of_mem (h : differentiable_within_at 𝕜 f s x) {t : set E}
  (hst : s ∈ 𝓝[t] x) :
  differentiable_within_at 𝕜 f t x :=
(h.has_fderiv_within_at.mono_of_mem hst).differentiable_within_at

lemma differentiable_within_at_univ :
  differentiable_within_at 𝕜 f univ x ↔ differentiable_at 𝕜 f x :=
by simp only [differentiable_within_at, has_fderiv_within_at_univ, differentiable_at]

lemma differentiable_within_at_inter (ht : t ∈ 𝓝 x) :
  differentiable_within_at 𝕜 f (s ∩ t) x ↔ differentiable_within_at 𝕜 f s x :=
by simp only [differentiable_within_at, has_fderiv_within_at_inter ht]

lemma differentiable_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  differentiable_within_at 𝕜 f (s ∩ t) x ↔ differentiable_within_at 𝕜 f s x :=
by simp only [differentiable_within_at, has_fderiv_within_at_inter' ht]

lemma differentiable_at.differentiable_within_at
  (h : differentiable_at 𝕜 f x) : differentiable_within_at 𝕜 f s x :=
(differentiable_within_at_univ.2 h).mono (subset_univ _)

lemma differentiable.differentiable_at (h : differentiable 𝕜 f) :
  differentiable_at 𝕜 f x :=
h x

lemma differentiable_at.fderiv_within
  (h : differentiable_at 𝕜 f x) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
h.has_fderiv_at.has_fderiv_within_at.fderiv_within hxs

lemma differentiable_on.mono (h : differentiable_on 𝕜 f t) (st : s ⊆ t) :
  differentiable_on 𝕜 f s :=
λ x hx, (h x (st hx)).mono st

lemma differentiable_on_univ :
  differentiable_on 𝕜 f univ ↔ differentiable 𝕜 f :=
by simp only [differentiable_on, differentiable, differentiable_within_at_univ, mem_univ,
  forall_true_left]

lemma differentiable.differentiable_on (h : differentiable 𝕜 f) : differentiable_on 𝕜 f s :=
(differentiable_on_univ.2 h).mono (subset_univ _)

lemma differentiable_on_of_locally_differentiable_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ differentiable_on 𝕜 f (s ∩ u)) : differentiable_on 𝕜 f s :=
begin
  assume x xs,
  rcases h x xs with ⟨t, t_open, xt, ht⟩,
  exact (differentiable_within_at_inter (is_open.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
end

lemma fderiv_within_of_mem (st : t ∈ 𝓝[s] x) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  fderiv_within 𝕜 f s x = fderiv_within 𝕜 f t x :=
((differentiable_within_at.has_fderiv_within_at h).mono_of_mem st).fderiv_within ht

lemma fderiv_within_subset (st : s ⊆ t) (ht : unique_diff_within_at 𝕜 s x)
  (h : differentiable_within_at 𝕜 f t x) :
  fderiv_within 𝕜 f s x = fderiv_within 𝕜 f t x :=
fderiv_within_of_mem (nhds_within_mono _ st self_mem_nhds_within) ht h

lemma fderiv_within_inter (ht : t ∈ 𝓝 x) :
  fderiv_within 𝕜 f (s ∩ t) x = fderiv_within 𝕜 f s x :=
by simp only [fderiv_within, has_fderiv_within_at_inter ht]

lemma fderiv_within_of_mem_nhds (h : s ∈ 𝓝 x) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
by simp only [fderiv, fderiv_within, has_fderiv_at, has_fderiv_within_at, nhds_within_eq_nhds.2 h]

@[simp] lemma fderiv_within_univ : fderiv_within 𝕜 f univ = fderiv 𝕜 f :=
funext $ λ _, fderiv_within_of_mem_nhds univ_mem

lemma fderiv_within_of_open (hs : is_open s) (hx : x ∈ s) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
fderiv_within_of_mem_nhds (hs.mem_nhds hx)

lemma fderiv_within_eq_fderiv (hs : unique_diff_within_at 𝕜 s x) (h : differentiable_at 𝕜 f x) :
  fderiv_within 𝕜 f s x = fderiv 𝕜 f x :=
begin
  rw ← fderiv_within_univ,
  exact fderiv_within_subset (subset_univ _) hs h.differentiable_within_at
end

lemma fderiv_mem_iff {f : E → F} {s : set (E →L[𝕜] F)} {x : E} :
  fderiv 𝕜 f x ∈ s ↔ (differentiable_at 𝕜 f x ∧ fderiv 𝕜 f x ∈ s) ∨
    (¬differentiable_at 𝕜 f x ∧ (0 : E →L[𝕜] F) ∈ s) :=
by by_cases hx : differentiable_at 𝕜 f x; simp [fderiv_zero_of_not_differentiable_at, *]

lemma fderiv_within_mem_iff {f : E → F} {t : set E} {s : set (E →L[𝕜] F)} {x : E} :
  fderiv_within 𝕜 f t x ∈ s ↔ (differentiable_within_at 𝕜 f t x ∧ fderiv_within 𝕜 f t x ∈ s) ∨
    (¬differentiable_within_at 𝕜 f t x ∧ (0 : E →L[𝕜] F) ∈ s) :=
by by_cases hx : differentiable_within_at 𝕜 f t x;
  simp [fderiv_within_zero_of_not_differentiable_within_at, *]

lemma asymptotics.is_O.has_fderiv_within_at {s : set E} {x₀ : E} {n : ℕ}
  (h : f =O[𝓝[s] x₀] λ x, ‖x - x₀‖^n) (hx₀ : x₀ ∈ s) (hn : 1 < n) :
  has_fderiv_within_at f (0 : E →L[𝕜] F) s x₀ :=
by simp_rw [has_fderiv_within_at, has_fderiv_at_filter,
  h.eq_zero_of_norm_pow_within hx₀ $ zero_lt_one.trans hn, zero_apply, sub_zero,
  h.trans_is_o ((is_o_pow_sub_sub x₀ hn).mono nhds_within_le_nhds)]

lemma asymptotics.is_O.has_fderiv_at {x₀ : E} {n : ℕ}
  (h : f =O[𝓝 x₀] λ x, ‖x - x₀‖^n) (hn : 1 < n) :
  has_fderiv_at f (0 : E →L[𝕜] F) x₀ :=
begin
  rw [← nhds_within_univ] at h,
  exact (h.has_fderiv_within_at (mem_univ _) hn).has_fderiv_at_of_univ
end

lemma has_fderiv_within_at.is_O {f : E → F} {s : set E} {x₀ : E} {f' : E →L[𝕜] F}
  (h : has_fderiv_within_at f f' s x₀) :
  (λ x, f x - f x₀) =O[𝓝[s] x₀] λ x, x - x₀ :=
by simpa only [sub_add_cancel] using h.is_O.add (is_O_sub f' (𝓝[s] x₀) x₀)

lemma has_fderiv_at.is_O {f : E → F} {x₀ : E} {f' : E →L[𝕜] F} (h : has_fderiv_at f f' x₀) :
  (λ x, f x - f x₀) =O[𝓝 x₀] λ x, x - x₀ :=
by simpa only [sub_add_cancel] using h.is_O.add (is_O_sub f' (𝓝 x₀) x₀)

end fderiv_properties

section continuous
/-! ### Deducing continuity from differentiability -/

theorem has_fderiv_at_filter.tendsto_nhds
  (hL : L ≤ 𝓝 x) (h : has_fderiv_at_filter f f' x L) :
  tendsto f L (𝓝 (f x)) :=
begin
  have : tendsto (λ x', f x' - f x) L (𝓝 0),
  { refine h.is_O_sub.trans_tendsto (tendsto.mono_left _ hL),
    rw ← sub_self x, exact tendsto_id.sub tendsto_const_nhds },
  have := tendsto.add this tendsto_const_nhds,
  rw zero_add (f x) at this,
  exact this.congr (by simp only [sub_add_cancel, eq_self_iff_true, forall_const])
end

theorem has_fderiv_within_at.continuous_within_at
  (h : has_fderiv_within_at f f' s x) : continuous_within_at f s x :=
has_fderiv_at_filter.tendsto_nhds inf_le_left h

theorem has_fderiv_at.continuous_at (h : has_fderiv_at f f' x) :
  continuous_at f x :=
has_fderiv_at_filter.tendsto_nhds le_rfl h

lemma differentiable_within_at.continuous_within_at (h : differentiable_within_at 𝕜 f s x) :
  continuous_within_at f s x :=
let ⟨f', hf'⟩ := h in hf'.continuous_within_at

lemma differentiable_at.continuous_at (h : differentiable_at 𝕜 f x) : continuous_at f x :=
let ⟨f', hf'⟩ := h in hf'.continuous_at

lemma differentiable_on.continuous_on (h : differentiable_on 𝕜 f s) : continuous_on f s :=
λx hx, (h x hx).continuous_within_at

lemma differentiable.continuous (h : differentiable 𝕜 f) : continuous f :=
continuous_iff_continuous_at.2 $ λx, (h x).continuous_at

protected lemma has_strict_fderiv_at.continuous_at (hf : has_strict_fderiv_at f f' x) :
  continuous_at f x :=
hf.has_fderiv_at.continuous_at

lemma has_strict_fderiv_at.is_O_sub_rev {f' : E ≃L[𝕜] F}
  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) x) :
  (λ p : E × E, p.1 - p.2) =O[𝓝 (x, x)](λ p : E × E, f p.1 - f p.2) :=
((f'.is_O_comp_rev _ _).trans (hf.trans_is_O (f'.is_O_comp_rev _ _)).right_is_O_add).congr
(λ _, rfl) (λ _, sub_add_cancel _ _)

lemma has_fderiv_at_filter.is_O_sub_rev (hf : has_fderiv_at_filter f f' x L) {C}
  (hf' : antilipschitz_with C f') :
  (λ x', x' - x) =O[L] (λ x', f x' - f x) :=
have (λ x', x' - x) =O[L] (λ x', f' (x' - x)),
  from is_O_iff.2 ⟨C, eventually_of_forall $ λ x',
    add_monoid_hom_class.bound_of_antilipschitz f' hf' _⟩,
(this.trans (hf.trans_is_O this).right_is_O_add).congr (λ _, rfl) (λ _, sub_add_cancel _ _)

end continuous

section congr
/-! ### congr properties of the derivative -/

lemma has_fderiv_within_at_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
  has_fderiv_within_at f f' s x ↔ has_fderiv_within_at f f' t x :=
calc has_fderiv_within_at f f' s x ↔ has_fderiv_within_at f f' (s \ {y}) x :
  (has_fderiv_within_at_diff_singleton _).symm
... ↔ has_fderiv_within_at f f' (t \ {y}) x :
  suffices 𝓝[s \ {y}] x = 𝓝[t \ {y}] x, by simp only [has_fderiv_within_at, this],
  by simpa only [set_eventually_eq_iff_inf_principal, ← nhds_within_inter', diff_eq, inter_comm]
    using h
... ↔ has_fderiv_within_at f f' t x : has_fderiv_within_at_diff_singleton _

lemma has_fderiv_within_at_congr_set (h : s =ᶠ[𝓝 x] t) :
  has_fderiv_within_at f f' s x ↔ has_fderiv_within_at f f' t x :=
has_fderiv_within_at_congr_set' x $ h.filter_mono inf_le_left

lemma differentiable_within_at_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
  differentiable_within_at 𝕜 f s x ↔ differentiable_within_at 𝕜 f t x :=
exists_congr $ λ _, has_fderiv_within_at_congr_set' _ h

lemma differentiable_within_at_congr_set (h : s =ᶠ[𝓝 x] t) :
  differentiable_within_at 𝕜 f s x ↔ differentiable_within_at 𝕜 f t x :=
exists_congr $ λ _, has_fderiv_within_at_congr_set h

lemma fderiv_within_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
  fderiv_within 𝕜 f s x = fderiv_within 𝕜 f t x :=
by simp only [fderiv_within, has_fderiv_within_at_congr_set' y h]

lemma fderiv_within_congr_set (h : s =ᶠ[𝓝 x] t) :
  fderiv_within 𝕜 f s x = fderiv_within 𝕜 f t x :=
fderiv_within_congr_set' x $ h.filter_mono inf_le_left

lemma fderiv_within_eventually_congr_set' (y : E) (h : s =ᶠ[𝓝[{y}ᶜ] x] t) :
  fderiv_within 𝕜 f s =ᶠ[𝓝 x] fderiv_within 𝕜 f t :=
(eventually_nhds_nhds_within.2 h).mono $ λ _, fderiv_within_congr_set' y

lemma fderiv_within_eventually_congr_set (h : s =ᶠ[𝓝 x] t) :
  fderiv_within 𝕜 f s =ᶠ[𝓝 x] fderiv_within 𝕜 f t :=
fderiv_within_eventually_congr_set' x $ h.filter_mono inf_le_left

theorem filter.eventually_eq.has_strict_fderiv_at_iff
  (h : f₀ =ᶠ[𝓝 x] f₁) (h' : ∀ y, f₀' y = f₁' y) :
  has_strict_fderiv_at f₀ f₀' x ↔ has_strict_fderiv_at f₁ f₁' x :=
begin
  refine is_o_congr ((h.prod_mk_nhds h).mono _) (eventually_of_forall $ λ _, rfl),
  rintros p ⟨hp₁, hp₂⟩,
  simp only [*]
end

theorem has_strict_fderiv_at.congr_of_eventually_eq (h : has_strict_fderiv_at f f' x)
  (h₁ : f =ᶠ[𝓝 x] f₁) : has_strict_fderiv_at f₁ f' x :=
(h₁.has_strict_fderiv_at_iff (λ _, rfl)).1 h

theorem filter.eventually_eq.has_fderiv_at_filter_iff
  (h₀ : f₀ =ᶠ[L] f₁) (hx : f₀ x = f₁ x) (h₁ : ∀ x, f₀' x = f₁' x) :
  has_fderiv_at_filter f₀ f₀' x L ↔ has_fderiv_at_filter f₁ f₁' x L :=
is_o_congr (h₀.mono $ λ y hy, by simp only [hy, h₁, hx]) (eventually_of_forall $ λ _, rfl)

lemma has_fderiv_at_filter.congr_of_eventually_eq (h : has_fderiv_at_filter f f' x L)
  (hL : f₁ =ᶠ[L] f) (hx : f₁ x = f x) : has_fderiv_at_filter f₁ f' x L :=
(hL.has_fderiv_at_filter_iff hx $ λ _, rfl).2 h

theorem filter.eventually_eq.has_fderiv_at_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
  has_fderiv_at f₀ f' x ↔ has_fderiv_at f₁ f' x :=
h.has_fderiv_at_filter_iff h.eq_of_nhds (λ _, rfl)

theorem filter.eventually_eq.differentiable_at_iff (h : f₀ =ᶠ[𝓝 x] f₁) :
  differentiable_at 𝕜 f₀ x ↔ differentiable_at 𝕜 f₁ x :=
exists_congr $ λ f', h.has_fderiv_at_iff

theorem filter.eventually_eq.has_fderiv_within_at_iff (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : f₀ x = f₁ x) :
  has_fderiv_within_at f₀ f' s x ↔ has_fderiv_within_at f₁ f' s x :=
h.has_fderiv_at_filter_iff hx (λ _, rfl)

theorem filter.eventually_eq.has_fderiv_within_at_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁) (hx : x ∈ s) :
  has_fderiv_within_at f₀ f' s x ↔ has_fderiv_within_at f₁ f' s x :=
h.has_fderiv_within_at_iff (h.eq_of_nhds_within hx)

theorem filter.eventually_eq.differentiable_within_at_iff (h : f₀ =ᶠ[𝓝[s] x] f₁)
  (hx : f₀ x = f₁ x) :
  differentiable_within_at 𝕜 f₀ s x ↔ differentiable_within_at 𝕜 f₁ s x :=
exists_congr $ λ f', h.has_fderiv_within_at_iff hx

theorem filter.eventually_eq.differentiable_within_at_iff_of_mem (h : f₀ =ᶠ[𝓝[s] x] f₁)
  (hx : x ∈ s) :
  differentiable_within_at 𝕜 f₀ s x ↔ differentiable_within_at 𝕜 f₁ s x :=
h.differentiable_within_at_iff (h.eq_of_nhds_within hx)

lemma has_fderiv_within_at.congr_mono (h : has_fderiv_within_at f f' s x) (ht : eq_on f₁ f t)
  (hx : f₁ x = f x) (h₁ : t ⊆ s) : has_fderiv_within_at f₁ f' t x :=
has_fderiv_at_filter.congr_of_eventually_eq (h.mono h₁) (filter.mem_inf_of_right ht) hx

lemma has_fderiv_within_at.congr (h : has_fderiv_within_at f f' s x) (hs : eq_on f₁ f s)
  (hx : f₁ x = f x) : has_fderiv_within_at f₁ f' s x :=
h.congr_mono hs hx (subset.refl _)

lemma has_fderiv_within_at.congr' (h : has_fderiv_within_at f f' s x) (hs : eq_on f₁ f s)
  (hx : x ∈ s) : has_fderiv_within_at f₁ f' s x :=
h.congr hs (hs hx)

lemma has_fderiv_within_at.congr_of_eventually_eq (h : has_fderiv_within_at f f' s x)
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) : has_fderiv_within_at f₁ f' s x :=
has_fderiv_at_filter.congr_of_eventually_eq h h₁ hx

lemma has_fderiv_at.congr_of_eventually_eq (h : has_fderiv_at f f' x)
  (h₁ : f₁ =ᶠ[𝓝 x] f) : has_fderiv_at f₁ f' x :=
has_fderiv_at_filter.congr_of_eventually_eq h h₁ (mem_of_mem_nhds h₁ : _)

lemma differentiable_within_at.congr_mono (h : differentiable_within_at 𝕜 f s x)
  (ht : eq_on f₁ f t) (hx : f₁ x = f x) (h₁ : t ⊆ s) : differentiable_within_at 𝕜 f₁ t x :=
(h.has_fderiv_within_at.congr_mono ht hx h₁).differentiable_within_at

lemma differentiable_within_at.congr (h : differentiable_within_at 𝕜 f s x)
  (ht : ∀x ∈ s, f₁ x = f x) (hx : f₁ x = f x) : differentiable_within_at 𝕜 f₁ s x :=
differentiable_within_at.congr_mono h ht hx (subset.refl _)

lemma differentiable_within_at.congr_of_eventually_eq
  (h : differentiable_within_at 𝕜 f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  (hx : f₁ x = f x) : differentiable_within_at 𝕜 f₁ s x :=
(h.has_fderiv_within_at.congr_of_eventually_eq h₁ hx).differentiable_within_at

lemma differentiable_on.congr_mono (h : differentiable_on 𝕜 f s) (h' : ∀x ∈ t, f₁ x = f x)
  (h₁ : t ⊆ s) : differentiable_on 𝕜 f₁ t :=
λ x hx, (h x (h₁ hx)).congr_mono h' (h' x hx) h₁

lemma differentiable_on.congr (h : differentiable_on 𝕜 f s) (h' : ∀x ∈ s, f₁ x = f x) :
  differentiable_on 𝕜 f₁ s :=
λ x hx, (h x hx).congr h' (h' x hx)

lemma differentiable_on_congr (h' : ∀x ∈ s, f₁ x = f x) :
  differentiable_on 𝕜 f₁ s ↔ differentiable_on 𝕜 f s :=
⟨λ h, differentiable_on.congr h (λy hy, (h' y hy).symm),
λ h, differentiable_on.congr h h'⟩

lemma differentiable_at.congr_of_eventually_eq (h : differentiable_at 𝕜 f x) (hL : f₁ =ᶠ[𝓝 x] f) :
  differentiable_at 𝕜 f₁ x :=
hL.differentiable_at_iff.2 h

lemma differentiable_within_at.fderiv_within_congr_mono (h : differentiable_within_at 𝕜 f s x)
  (hs : eq_on f₁ f t) (hx : f₁ x = f x) (hxt : unique_diff_within_at 𝕜 t x) (h₁ : t ⊆ s) :
  fderiv_within 𝕜 f₁ t x = fderiv_within 𝕜 f s x :=
(has_fderiv_within_at.congr_mono h.has_fderiv_within_at hs hx h₁).fderiv_within hxt

lemma filter.eventually_eq.fderiv_within_eq (hs : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
by simp only [fderiv_within, hs.has_fderiv_within_at_iff hx]

lemma filter.eventually_eq.fderiv_within' (hs : f₁ =ᶠ[𝓝[s] x] f) (ht : t ⊆ s) :
  fderiv_within 𝕜 f₁ t =ᶠ[𝓝[s] x] fderiv_within 𝕜 f t :=
(eventually_nhds_within_nhds_within.2 hs).mp $ eventually_mem_nhds_within.mono $ λ y hys hs,
  filter.eventually_eq.fderiv_within_eq (hs.filter_mono $ nhds_within_mono _ ht)
    (hs.self_of_nhds_within hys)

protected lemma filter.eventually_eq.fderiv_within (hs : f₁ =ᶠ[𝓝[s] x] f) :
  fderiv_within 𝕜 f₁ s =ᶠ[𝓝[s] x] fderiv_within 𝕜 f s :=
hs.fderiv_within' subset.rfl

lemma filter.eventually_eq.fderiv_within_eq_nhds (h : f₁ =ᶠ[𝓝 x] f) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
(h.filter_mono nhds_within_le_nhds).fderiv_within_eq h.self_of_nhds

lemma fderiv_within_congr (hs : eq_on f₁ f s) (hx : f₁ x = f x) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
(hs.eventually_eq.filter_mono inf_le_right).fderiv_within_eq hx

lemma fderiv_within_congr' (hs : eq_on f₁ f s) (hx : x ∈ s) :
  fderiv_within 𝕜 f₁ s x = fderiv_within 𝕜 f s x :=
fderiv_within_congr hs (hs hx)

lemma filter.eventually_eq.fderiv_eq (h : f₁ =ᶠ[𝓝 x] f) :
  fderiv 𝕜 f₁ x = fderiv 𝕜 f x :=
by rw [← fderiv_within_univ, ← fderiv_within_univ, h.fderiv_within_eq_nhds]

protected lemma filter.eventually_eq.fderiv (h : f₁ =ᶠ[𝓝 x] f) :
  fderiv 𝕜 f₁ =ᶠ[𝓝 x] fderiv 𝕜 f :=
h.eventually_eq_nhds.mono $ λ x h, h.fderiv_eq

end congr

section id
/-! ### Derivative of the identity -/

theorem has_strict_fderiv_at_id (x : E) :
  has_strict_fderiv_at id (id 𝕜 E) x :=
(is_o_zero _ _).congr_left $ by simp

theorem has_fderiv_at_filter_id (x : E) (L : filter E) :
  has_fderiv_at_filter id (id 𝕜 E) x L :=
(is_o_zero _ _).congr_left $ by simp

theorem has_fderiv_within_at_id (x : E) (s : set E) :
  has_fderiv_within_at id (id 𝕜 E) s x :=
has_fderiv_at_filter_id _ _

theorem has_fderiv_at_id (x : E) : has_fderiv_at id (id 𝕜 E) x :=
has_fderiv_at_filter_id _ _

@[simp] lemma differentiable_at_id : differentiable_at 𝕜 id x :=
(has_fderiv_at_id x).differentiable_at

@[simp] lemma differentiable_at_id' : differentiable_at 𝕜 (λ x, x) x :=
(has_fderiv_at_id x).differentiable_at

lemma differentiable_within_at_id : differentiable_within_at 𝕜 id s x :=
differentiable_at_id.differentiable_within_at

@[simp] lemma differentiable_id : differentiable 𝕜 (id : E → E) :=
λx, differentiable_at_id

@[simp] lemma differentiable_id' : differentiable 𝕜 (λ (x : E), x) :=
λx, differentiable_at_id

lemma differentiable_on_id : differentiable_on 𝕜 id s :=
differentiable_id.differentiable_on

lemma fderiv_id : fderiv 𝕜 id x = id 𝕜 E :=
has_fderiv_at.fderiv (has_fderiv_at_id x)

@[simp] lemma fderiv_id' : fderiv 𝕜 (λ (x : E), x) x = continuous_linear_map.id 𝕜 E :=
fderiv_id

lemma fderiv_within_id (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 id s x = id 𝕜 E :=
begin
  rw differentiable_at.fderiv_within (differentiable_at_id) hxs,
  exact fderiv_id
end

lemma fderiv_within_id' (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λ (x : E), x) s x = continuous_linear_map.id 𝕜 E :=
fderiv_within_id hxs

end id

section const
/-! ### derivative of a constant function -/

theorem has_strict_fderiv_at_const (c : F) (x : E) :
  has_strict_fderiv_at (λ _, c) (0 : E →L[𝕜] F) x :=
(is_o_zero _ _).congr_left $ λ _, by simp only [zero_apply, sub_self]

theorem has_fderiv_at_filter_const (c : F) (x : E) (L : filter E) :
  has_fderiv_at_filter (λ x, c) (0 : E →L[𝕜] F) x L :=
(is_o_zero _ _).congr_left $ λ _, by simp only [zero_apply, sub_self]

theorem has_fderiv_within_at_const (c : F) (x : E) (s : set E) :
  has_fderiv_within_at (λ x, c) (0 : E →L[𝕜] F) s x :=
has_fderiv_at_filter_const _ _ _

theorem has_fderiv_at_const (c : F) (x : E) :
  has_fderiv_at (λ x, c) (0 : E →L[𝕜] F) x :=
has_fderiv_at_filter_const _ _ _

@[simp] lemma differentiable_at_const (c : F) : differentiable_at 𝕜 (λx, c) x :=
⟨0, has_fderiv_at_const c x⟩

lemma differentiable_within_at_const (c : F) : differentiable_within_at 𝕜 (λx, c) s x :=
differentiable_at.differentiable_within_at (differentiable_at_const _)

lemma fderiv_const_apply (c : F) : fderiv 𝕜 (λy, c) x = 0 :=
has_fderiv_at.fderiv (has_fderiv_at_const c x)

@[simp] lemma fderiv_const (c : F) : fderiv 𝕜 (λ (y : E), c) = 0 :=
by { ext m, rw fderiv_const_apply, refl }

lemma fderiv_within_const_apply (c : F) (hxs : unique_diff_within_at 𝕜 s x) :
  fderiv_within 𝕜 (λy, c) s x = 0 :=
begin
  rw differentiable_at.fderiv_within (differentiable_at_const _) hxs,
  exact fderiv_const_apply _
end

@[simp] lemma differentiable_const (c : F) : differentiable 𝕜 (λx : E, c) :=
λx, differentiable_at_const _

lemma differentiable_on_const (c : F) : differentiable_on 𝕜 (λx, c) s :=
(differentiable_const _).differentiable_on

lemma has_fderiv_within_at_singleton (f : E → F) (x : E) :
  has_fderiv_within_at f (0 : E →L[𝕜] F) {x} x :=
by simp only [has_fderiv_within_at, nhds_within_singleton, has_fderiv_at_filter, is_o_pure,
  continuous_linear_map.zero_apply, sub_self]

lemma has_fderiv_at_of_subsingleton [h : subsingleton E] (f : E → F) (x : E) :
  has_fderiv_at f (0 : E →L[𝕜] F) x :=
begin
  rw [← has_fderiv_within_at_univ, subsingleton_univ.eq_singleton_of_mem (mem_univ x)],
  exact has_fderiv_within_at_singleton f x
end

lemma differentiable_on_empty : differentiable_on 𝕜 f ∅ := λ x, false.elim

lemma differentiable_on_singleton : differentiable_on 𝕜 f {x} :=
forall_eq.2 (has_fderiv_within_at_singleton f x).differentiable_within_at

lemma set.subsingleton.differentiable_on (hs : s.subsingleton) : differentiable_on 𝕜 f s :=
hs.induction_on differentiable_on_empty (λ x, differentiable_on_singleton)

lemma has_fderiv_at_zero_of_eventually_const
  (c : F) (hf : f =ᶠ[𝓝 x] (λ y, c)) :
  has_fderiv_at f (0 : E →L[𝕜] F) x :=
(has_fderiv_at_const _ _).congr_of_eventually_eq hf

end const

end

/-! ### Support of derivatives -/

section support

open function
variables (𝕜 : Type*) {E F : Type*} [nontrivially_normed_field 𝕜] [normed_add_comm_group E]
  [normed_space 𝕜 E] [normed_add_comm_group F] [normed_space 𝕜 F] {f : E → F}

lemma support_fderiv_subset : support (fderiv 𝕜 f) ⊆ tsupport f :=
begin
  intros x,
  rw [← not_imp_not, not_mem_tsupport_iff_eventually_eq, nmem_support],
  exact λ hx, (hx.fderiv_eq.trans $ fderiv_const_apply 0),
end

lemma tsupport_fderiv_subset : tsupport (fderiv 𝕜 f) ⊆ tsupport f :=
closure_minimal (support_fderiv_subset 𝕜) is_closed_closure

lemma has_compact_support.fderiv (hf : has_compact_support f) : has_compact_support (fderiv 𝕜 f) :=
hf.mono' $ support_fderiv_subset 𝕜

end support
