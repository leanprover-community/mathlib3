/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.fderiv
import analysis.normed_space.multilinear
import analysis.calculus.formal_multilinear_series
import data.enat.basic

/-!
# Higher differentiability

A function is `C^1` on a domain if it is differentiable there, and its derivative is continuous.
By induction, it is `C^n` if it is `C^{n-1}` and its (n-1)-th derivative is `C^1` there or,
equivalently, if it is `C^1` and its derivative is `C^{n-1}`.
Finally, it is `C^∞` if it is `C^n` for all n.

We formalize these notions by defining iteratively the `n+1`-th derivative of a function as the
derivative of the `n`-th derivative. It is called `iterated_fderiv 𝕜 n f x` where `𝕜` is the
field, `n` is the number of iterations, `f` is the function and `x` is the point, and it is given
as an `n`-multilinear map. We also define a version `iterated_fderiv_within` relative to a domain,
as well as predicates `cont_diff_within_at`, `cont_diff_at`, `cont_diff_on` and
`cont_diff` saying that the function is `C^n` within a set at a point, at a point, on a set
and on the whole space respectively.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `cont_diff_on` is not defined directly in terms of the
regularity of the specific choice `iterated_fderiv_within 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`has_ftaylor_series_up_to_on`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nontrivially normed field `𝕜`.

* `has_ftaylor_series_up_to n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `has_ftaylor_series_up_to_on n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.
* `cont_diff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `cont_diff_on 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `cont_diff_at 𝕜 n f x`: expresses that `f` is `C^n` around `x`.
* `cont_diff_within_at 𝕜 n f s x`: expresses that `f` is `C^n` around `x` within the set `s`.
* `iterated_fderiv_within 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iterated_fderiv_within 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iterated_fderiv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iterated_fderiv 𝕜 (n-1) f` if one exists, and `0` otherwise.

In sets of unique differentiability, `cont_diff_on 𝕜 n f s` can be expressed in terms of the
properties of `iterated_fderiv_within 𝕜 m f s` for `m ≤ n`. In the whole space,
`cont_diff 𝕜 n f` can be expressed in terms of the properties of `iterated_fderiv 𝕜 m f`
for `m ≤ n`.

## Implementation notes

The definitions in this file are designed to work on any field `𝕜`. They are sometimes slightly more
complicated than the naive definitions one would guess from the intuition over the real or complex
numbers, but they are designed to circumvent the lack of gluing properties and partitions of unity
in general. In the usual situations, they coincide with the usual definitions.

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iterated_fderiv_within`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`.

This definition still has the problem that a function which is locally `C^n` would not need to
be `C^n`, as different choices of sequences of derivatives around different points might possibly
not be glued together to give a globally defined sequence of derivatives. (Note that this issue
can not happen over reals, thanks to partition of unity, but the behavior over a general field is
not so clear, and we want a definition for general fields). Also, there are locality
problems for the order parameter: one could image a function which, for each `n`, has a nice
sequence of derivatives up to order `n`, but they do not coincide for varying `n` and can therefore
not be glued to give rise to an infinite sequence of derivatives. This would give a function
which is `C^n` for all `n`, but not `C^∞`. We solve this issue by putting locality conditions
in space and order in our definition of `cont_diff_within_at` and `cont_diff_on`.
The resulting definition is slightly more complicated to work with (in fact not so much), but it
gives rise to completely satisfactory theorems.

For instance, with this definition, a real function which is `C^m` (but not better) on `(-1/m, 1/m)`
for each natural `m` is by definition `C^∞` at `0`.

There is another issue with the definition of `cont_diff_within_at 𝕜 n f s x`. We can
require the existence and good behavior of derivatives up to order `n` on a neighborhood of `x`
within `s`. However, this does not imply continuity or differentiability within `s` of the function
at `x` when `x` does not belong to `s`. Therefore, we require such existence and good behavior on
a neighborhood of `x` within `s ∪ {x}` (which appears as `insert x s` in this file).

### Side of the composition, and universe issues

With a naïve direct definition, the `n`-th derivative of a function belongs to the space
`E →L[𝕜] (E →L[𝕜] (E ... F)...)))` where there are n iterations of `E →L[𝕜]`. This space
may also be seen as the space of continuous multilinear functions on `n` copies of `E` with
values in `F`, by uncurrying. This is the point of view that is usually adopted in textbooks,
and that we also use. This means that the definition and the first proofs are slightly involved,
as one has to keep track of the uncurrying operation. The uncurrying can be done from the
left or from the right, amounting to defining the `n+1`-th derivative either as the derivative of
the `n`-th derivative, or as the `n`-th derivative of the derivative.
For proofs, it would be more convenient to use the latter approach (from the right),
as it means to prove things at the `n+1`-th step we only need to understand well enough the
derivative in `E →L[𝕜] F` (contrary to the approach from the left, where one would need to know
enough on the `n`-th derivative to deduce things on the `n+1`-th derivative).

However, the definition from the right leads to a universe polymorphism problem: if we define
`iterated_fderiv 𝕜 (n + 1) f x = iterated_fderiv 𝕜 n (fderiv 𝕜 f) x` by induction, we need to
generalize over all spaces (as `f` and `fderiv 𝕜 f` don't take values in the same space). It is
only possible to generalize over all spaces in some fixed universe in an inductive definition.
For `f : E → F`, then `fderiv 𝕜 f` is a map `E → (E →L[𝕜] F)`. Therefore, the definition will only
work if `F` and `E →L[𝕜] F` are in the same universe.

This issue does not appear with the definition from the left, where one does not need to generalize
over all spaces. Therefore, we use the definition from the left. This means some proofs later on
become a little bit more complicated: to prove that a function is `C^n`, the most efficient approach
is to exhibit a formula for its `n`-th derivative and prove it is continuous (contrary to the
inductive approach where one would prove smoothness statements without giving a formula for the
derivative). In the end, this approach is still satisfactory as it is good to have formulas for the
iterated derivatives in various constructions.

One point where we depart from this explicit approach is in the proof of smoothness of a
composition: there is a formula for the `n`-th derivative of a composition (Faà di Bruno's formula),
but it is very complicated and barely usable, while the inductive proof is very simple. Thus, we
give the inductive proof. As explained above, it works by generalizing over the target space, hence
it only works well if all spaces belong to the same universe. To get the general version, we lift
things to a common universe using a trick.

### Variables management

The textbook definitions and proofs use various identifications and abuse of notations, for instance
when saying that the natural space in which the derivative lives, i.e.,
`E →L[𝕜] (E →L[𝕜] ( ... →L[𝕜] F))`, is the same as a space of multilinear maps. When doing things
formally, we need to provide explicit maps for these identifications, and chase some diagrams to see
everything is compatible with the identifications. In particular, one needs to check that taking the
derivative and then doing the identification, or first doing the identification and then taking the
derivative, gives the same result. The key point for this is that taking the derivative commutes
with continuous linear equivalences. Therefore, we need to implement all our identifications with
continuous linear equivs.

## Notations

We use the notation `E [×n]→L[𝕜] F` for the space of continuous multilinear maps on `E^n` with
values in `F`. This is the space in which the `n`-th derivative of a function from `E` to `F` lives.

In this file, we denote `⊤ : ℕ∞` with `∞`.

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

noncomputable theory
open_locale classical big_operators nnreal topology

local notation `∞` := (⊤ : ℕ∞)

local attribute [instance, priority 1001]
normed_add_comm_group.to_add_comm_group normed_space.to_module' add_comm_group.to_add_comm_monoid

open set fin filter function

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [normed_add_comm_group G] [normed_space 𝕜 G]
{X : Type*} [normed_add_comm_group X] [normed_space 𝕜 X]
{s s₁ t u : set E} {f f₁ : E → F} {g : F → G} {x x₀ : E} {c : F}
{m n : ℕ∞} {p : E → formal_multilinear_series 𝕜 E F}

/-! ### Functions with a Taylor series on a domain -/

/-- `has_ftaylor_series_up_to_on n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_within_at` but for higher order derivatives. -/
structure has_ftaylor_series_up_to_on (n : ℕ∞)
  (f : E → F) (p : E → formal_multilinear_series 𝕜 E F) (s : set E) : Prop :=
(zero_eq       : ∀ x ∈ s, (p x 0).uncurry0 = f x)
(fderiv_within : ∀ (m : ℕ) (hm : (m : ℕ∞) < n), ∀ x ∈ s,
   has_fderiv_within_at (λ y, p y m) (p x m.succ).curry_left s x)
(cont          : ∀ (m : ℕ) (hm : (m : ℕ∞) ≤ n), continuous_on (λ x, p x m) s)

lemma has_ftaylor_series_up_to_on.zero_eq'
  (h : has_ftaylor_series_up_to_on n f p s) {x : E} (hx : x ∈ s) :
  p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x) :=
by { rw ← h.zero_eq x hx, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ }

/-- If two functions coincide on a set `s`, then a Taylor series for the first one is as well a
Taylor series for the second one. -/
lemma has_ftaylor_series_up_to_on.congr
  (h : has_ftaylor_series_up_to_on n f p s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
  has_ftaylor_series_up_to_on n f₁ p s :=
begin
  refine ⟨λ x hx, _, h.fderiv_within, h.cont⟩,
  rw h₁ x hx,
  exact h.zero_eq x hx
end

lemma has_ftaylor_series_up_to_on.mono
  (h : has_ftaylor_series_up_to_on n f p s) {t : set E} (hst : t ⊆ s) :
  has_ftaylor_series_up_to_on n f p t :=
⟨λ x hx, h.zero_eq x (hst hx),
λ m hm x hx, (h.fderiv_within m hm x (hst hx)).mono hst,
λ m hm, (h.cont m hm).mono hst⟩

lemma has_ftaylor_series_up_to_on.of_le
  (h : has_ftaylor_series_up_to_on n f p s) (hmn : m ≤ n) :
  has_ftaylor_series_up_to_on m f p s :=
⟨h.zero_eq,
λ k hk x hx, h.fderiv_within k (lt_of_lt_of_le hk hmn) x hx,
λ k hk, h.cont k (le_trans hk hmn)⟩

lemma has_ftaylor_series_up_to_on.continuous_on
  (h : has_ftaylor_series_up_to_on n f p s) : continuous_on f s :=
begin
  have := (h.cont 0 bot_le).congr (λ x hx, (h.zero_eq' hx).symm),
  rwa linear_isometry_equiv.comp_continuous_on_iff at this
end

lemma has_ftaylor_series_up_to_on_zero_iff :
  has_ftaylor_series_up_to_on 0 f p s ↔ continuous_on f s ∧ (∀ x ∈ s, (p x 0).uncurry0 = f x) :=
begin
  refine ⟨λ H, ⟨H.continuous_on, H.zero_eq⟩,
          λ H, ⟨H.2, λ m hm, false.elim (not_le.2 hm bot_le), _⟩⟩,
  assume m hm,
  obtain rfl : m = 0, by exact_mod_cast (hm.antisymm (zero_le _)),
  have : ∀ x ∈ s, p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x),
    by { assume x hx, rw ← H.2 x hx, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ },
  rw [continuous_on_congr this, linear_isometry_equiv.comp_continuous_on_iff],
  exact H.1
end

lemma has_ftaylor_series_up_to_on_top_iff :
  (has_ftaylor_series_up_to_on ∞ f p s) ↔ (∀ (n : ℕ), has_ftaylor_series_up_to_on n f p s) :=
begin
  split,
  { assume H n, exact H.of_le le_top },
  { assume H,
    split,
    { exact (H 0).zero_eq },
    { assume m hm,
      apply (H m.succ).fderiv_within m (with_top.coe_lt_coe.2 (lt_add_one m)) },
    { assume m hm,
      apply (H m).cont m le_rfl } }
end

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
lemma has_ftaylor_series_up_to_on.has_fderiv_within_at
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hx : x ∈ s) :
  has_fderiv_within_at f (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) s x :=
begin
  have A : ∀ y ∈ s, f y = (continuous_multilinear_curry_fin0 𝕜 E F) (p y 0),
  { assume y hy, rw ← h.zero_eq y hy, refl },
  suffices H : has_fderiv_within_at
      (λ y, continuous_multilinear_curry_fin0 𝕜 E F (p y 0))
      (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) s x,
    by exact H.congr A (A x hx),
  rw linear_isometry_equiv.comp_has_fderiv_within_at_iff',
  have : ((0 : ℕ) : ℕ∞) < n :=
    lt_of_lt_of_le (with_top.coe_lt_coe.2 nat.zero_lt_one) hn,
  convert h.fderiv_within _ this x hx,
  ext y v,
  change (p x 1) (snoc 0 y) = (p x 1) (cons y v),
  unfold_coes,
  congr' with i,
  rw unique.eq_default i,
  refl
end

lemma has_ftaylor_series_up_to_on.differentiable_on
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) : differentiable_on 𝕜 f s :=
λ x hx, (h.has_fderiv_within_at hn hx).differentiable_within_at

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then the term
of order `1` of this series is a derivative of `f` at `x`. -/
lemma has_ftaylor_series_up_to_on.has_fderiv_at
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) x :=
(h.has_fderiv_within_at hn (mem_of_mem_nhds hx)).has_fderiv_at hx

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
in a neighborhood of `x`, the term of order `1` of this series is a derivative of `f`. -/
lemma has_ftaylor_series_up_to_on.eventually_has_fderiv_at
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) :
  ∀ᶠ y in 𝓝 x, has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p y 1)) y :=
(eventually_eventually_nhds.2 hx).mono $ λ y hy, h.has_fderiv_at hn hy

/-- If a function has a Taylor series at order at least `1` on a neighborhood of `x`, then
it is differentiable at `x`. -/
lemma has_ftaylor_series_up_to_on.differentiable_at
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hx : s ∈ 𝓝 x) :
  differentiable_at 𝕜 f x :=
(h.has_fderiv_at hn hx).differentiable_at

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p` is a Taylor series up to `n`, and
`p (n + 1)` is a derivative of `p n`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_left {n : ℕ} :
  has_ftaylor_series_up_to_on (n + 1) f p s ↔
  has_ftaylor_series_up_to_on n f p s
  ∧ (∀ x ∈ s, has_fderiv_within_at (λ y, p y n) (p x n.succ).curry_left s x)
  ∧ continuous_on (λ x, p x (n + 1)) s :=
begin
  split,
  { assume h,
    exact ⟨h.of_le (with_top.coe_le_coe.2 (nat.le_succ n)),
           h.fderiv_within _ (with_top.coe_lt_coe.2 (lt_add_one n)),
           h.cont (n + 1) le_rfl⟩ },
  { assume h,
    split,
    { exact h.1.zero_eq },
    { assume m hm,
      by_cases h' : m < n,
      { exact h.1.fderiv_within m (with_top.coe_lt_coe.2 h') },
      { have : m = n := nat.eq_of_lt_succ_of_not_lt (with_top.coe_lt_coe.1 hm) h',
        rw this,
        exact h.2.1 } },
    { assume m hm,
      by_cases h' : m ≤ n,
      { apply h.1.cont m (with_top.coe_le_coe.2 h') },
      { have : m = (n + 1) := le_antisymm (with_top.coe_le_coe.1 hm) (not_le.1 h'),
        rw this,
        exact h.2.2 } } }
end

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_on_succ_iff_right {n : ℕ} :
  has_ftaylor_series_up_to_on ((n + 1) : ℕ) f p s ↔
  (∀ x ∈ s, (p x 0).uncurry0 = f x)
  ∧ (∀ x ∈ s, has_fderiv_within_at (λ y, p y 0) (p x 1).curry_left s x)
  ∧ has_ftaylor_series_up_to_on n
    (λ x, continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) (λ x, (p x).shift) s :=
begin
  split,
  { assume H,
    refine ⟨H.zero_eq, H.fderiv_within 0 (with_top.coe_lt_coe.2 (nat.succ_pos n)), _⟩,
    split,
    { assume x hx, refl },
    { assume m (hm : (m : ℕ∞) < n) x (hx : x ∈ s),
      have A : (m.succ : ℕ∞) < n.succ,
        by { rw with_top.coe_lt_coe at ⊢ hm, exact nat.lt_succ_iff.mpr hm },
      change has_fderiv_within_at
        ((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm
           ∘ (λ (y : E), p y m.succ))
        (p x m.succ.succ).curry_right.curry_left s x,
      rw linear_isometry_equiv.comp_has_fderiv_within_at_iff',
      convert H.fderiv_within _ A x hx,
      ext y v,
      change (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        = (p x (nat.succ (nat.succ m))) (cons y v),
      rw [← cons_snoc_eq_snoc_cons, snoc_init_self] },
    { assume m (hm : (m : ℕ∞) ≤ n),
      have A : (m.succ : ℕ∞) ≤ n.succ,
        by { rw with_top.coe_le_coe at ⊢ hm, exact nat.pred_le_iff.mp hm },
      change continuous_on ((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm
           ∘ (λ (y : E), p y m.succ)) s,
      rw linear_isometry_equiv.comp_continuous_on_iff,
      exact H.cont _ A } },
  { rintros ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩,
    split,
    { exact Hzero_eq },
    { assume m (hm : (m : ℕ∞) < n.succ) x (hx : x ∈ s),
      cases m,
      { exact Hfderiv_zero x hx },
      { have A : (m : ℕ∞) < n,
          by { rw with_top.coe_lt_coe at hm ⊢, exact nat.lt_of_succ_lt_succ hm },
        have : has_fderiv_within_at ((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm
           ∘ (λ (y : E), p y m.succ)) ((p x).shift m.succ).curry_left s x :=
          Htaylor.fderiv_within _ A x hx,
        rw linear_isometry_equiv.comp_has_fderiv_within_at_iff' at this,
        convert this,
        ext y v,
        change (p x (nat.succ (nat.succ m))) (cons y v)
          = (p x m.succ.succ) (snoc (cons y (init v)) (v (last _))),
        rw [← cons_snoc_eq_snoc_cons, snoc_init_self] } },
    { assume m (hm : (m : ℕ∞) ≤ n.succ),
      cases m,
      { have : differentiable_on 𝕜 (λ x, p x 0) s :=
          λ x hx, (Hfderiv_zero x hx).differentiable_within_at,
        exact this.continuous_on },
      { have A : (m : ℕ∞) ≤ n,
          by { rw with_top.coe_le_coe at hm ⊢, exact nat.lt_succ_iff.mp hm },
        have : continuous_on ((continuous_multilinear_curry_right_equiv' 𝕜 m E F).symm
           ∘ (λ (y : E), p y m.succ)) s :=
        Htaylor.cont _ A,
        rwa linear_isometry_equiv.comp_continuous_on_iff at this } } }
end

/-! ### Smooth functions within a set around a point -/

variable (𝕜)

/-- A function is continuously differentiable up to order `n` within a set `s` at a point `x` if
it admits continuous derivatives up to order `n` in a neighborhood of `x` in `s ∪ {x}`.
For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).

For instance, a real function which is `C^m` on `(-1/m, 1/m)` for each natural `m`, but not
better, is `C^∞` at `0` within `univ`.
-/
def cont_diff_within_at (n : ℕ∞) (f : E → F) (s : set E) (x : E) : Prop :=
∀ (m : ℕ), (m : ℕ∞) ≤ n →
  ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → formal_multilinear_series 𝕜 E F,
    has_ftaylor_series_up_to_on m f p u

variable {𝕜}

lemma cont_diff_within_at_nat {n : ℕ} :
  cont_diff_within_at 𝕜 n f s x ↔
  ∃ u ∈ 𝓝[insert x s] x, ∃ p : E → formal_multilinear_series 𝕜 E F,
  has_ftaylor_series_up_to_on n f p u :=
⟨λ H, H n le_rfl, λ ⟨u, hu, p, hp⟩ m hm, ⟨u, hu, p, hp.of_le hm⟩⟩

lemma cont_diff_within_at.of_le
  (h : cont_diff_within_at 𝕜 n f s x) (hmn : m ≤ n) :
  cont_diff_within_at 𝕜 m f s x :=
λ k hk, h k (le_trans hk hmn)

lemma cont_diff_within_at_iff_forall_nat_le :
  cont_diff_within_at 𝕜 n f s x ↔ ∀ m : ℕ, ↑m ≤ n → cont_diff_within_at 𝕜 m f s x :=
⟨λ H m hm, H.of_le hm, λ H m hm, H m hm _ le_rfl⟩

lemma cont_diff_within_at_top :
  cont_diff_within_at 𝕜 ∞ f s x ↔ ∀ (n : ℕ), cont_diff_within_at 𝕜 n f s x :=
cont_diff_within_at_iff_forall_nat_le.trans $ by simp only [forall_prop_of_true, le_top]

lemma cont_diff_within_at.continuous_within_at
  (h : cont_diff_within_at 𝕜 n f s x) : continuous_within_at f s x :=
begin
  rcases h 0 bot_le with ⟨u, hu, p, H⟩,
  rw [mem_nhds_within_insert] at hu,
  exact (H.continuous_on.continuous_within_at hu.1).mono_of_mem hu.2
end

lemma cont_diff_within_at.congr_of_eventually_eq
  (h : cont_diff_within_at 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  cont_diff_within_at 𝕜 n f₁ s x :=
λ m hm, let ⟨u, hu, p, H⟩ := h m hm in
⟨{x ∈ u | f₁ x = f x}, filter.inter_mem hu (mem_nhds_within_insert.2 ⟨hx, h₁⟩), p,
  (H.mono (sep_subset _ _)).congr (λ _, and.right)⟩

lemma cont_diff_within_at.congr_of_eventually_eq_insert
  (h : cont_diff_within_at 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[insert x s] x] f) :
  cont_diff_within_at 𝕜 n f₁ s x :=
h.congr_of_eventually_eq (nhds_within_mono x (subset_insert x s) h₁)
  (mem_of_mem_nhds_within (mem_insert x s) h₁ : _)

lemma cont_diff_within_at.congr_of_eventually_eq'
  (h : cont_diff_within_at 𝕜 n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : x ∈ s) :
  cont_diff_within_at 𝕜 n f₁ s x :=
h.congr_of_eventually_eq h₁ $ h₁.self_of_nhds_within hx

lemma filter.eventually_eq.cont_diff_within_at_iff
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  cont_diff_within_at 𝕜 n f₁ s x ↔ cont_diff_within_at 𝕜 n f s x :=
⟨λ H, cont_diff_within_at.congr_of_eventually_eq H h₁.symm hx.symm,
λ H, H.congr_of_eventually_eq h₁ hx⟩

lemma cont_diff_within_at.congr
  (h : cont_diff_within_at 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
  cont_diff_within_at 𝕜 n f₁ s x :=
h.congr_of_eventually_eq (filter.eventually_eq_of_mem self_mem_nhds_within h₁) hx

lemma cont_diff_within_at.congr'
  (h : cont_diff_within_at 𝕜 n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : x ∈ s) :
  cont_diff_within_at 𝕜 n f₁ s x :=
h.congr h₁ (h₁ _ hx)

lemma cont_diff_within_at.mono_of_mem
  (h : cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : s ∈ 𝓝[t] x) :
  cont_diff_within_at 𝕜 n f t x :=
begin
  assume m hm,
  rcases h m hm with ⟨u, hu, p, H⟩,
  exact ⟨u, nhds_within_le_of_mem (insert_mem_nhds_within_insert hst) hu, p, H⟩
end

lemma cont_diff_within_at.mono
  (h : cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : t ⊆ s) :
  cont_diff_within_at 𝕜 n f t x :=
h.mono_of_mem $ filter.mem_of_superset self_mem_nhds_within hst

lemma cont_diff_within_at.congr_nhds
  (h : cont_diff_within_at 𝕜 n f s x) {t : set E} (hst : 𝓝[s] x = 𝓝[t] x) :
  cont_diff_within_at 𝕜 n f t x :=
h.mono_of_mem $ hst ▸ self_mem_nhds_within

lemma cont_diff_within_at_congr_nhds {t : set E} (hst : 𝓝[s] x = 𝓝[t] x) :
  cont_diff_within_at 𝕜 n f s x ↔ cont_diff_within_at 𝕜 n f t x :=
⟨λ h, h.congr_nhds hst, λ h, h.congr_nhds hst.symm⟩

lemma cont_diff_within_at_inter' (h : t ∈ 𝓝[s] x) :
  cont_diff_within_at 𝕜 n f (s ∩ t) x ↔ cont_diff_within_at 𝕜 n f s x :=
cont_diff_within_at_congr_nhds $ eq.symm $ nhds_within_restrict'' _ h

lemma cont_diff_within_at_inter (h : t ∈ 𝓝 x) :
  cont_diff_within_at 𝕜 n f (s ∩ t) x ↔ cont_diff_within_at 𝕜 n f s x :=
cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds h)

lemma cont_diff_within_at_insert {y : E} :
  cont_diff_within_at 𝕜 n f (insert y s) x ↔ cont_diff_within_at 𝕜 n f s x :=
begin
  simp_rw [cont_diff_within_at],
  rcases eq_or_ne x y with rfl|h,
  { simp_rw [insert_eq_of_mem (mem_insert _ _)] },
  simp_rw [insert_comm x y, nhds_within_insert_of_ne h]
end

alias cont_diff_within_at_insert ↔ cont_diff_within_at.of_insert cont_diff_within_at.insert'

lemma cont_diff_within_at.insert (h : cont_diff_within_at 𝕜 n f s x) :
  cont_diff_within_at 𝕜 n f (insert x s) x :=
h.insert'

/-- If a function is `C^n` within a set at a point, with `n ≥ 1`, then it is differentiable
within this set at this point. -/
lemma cont_diff_within_at.differentiable_within_at'
  (h : cont_diff_within_at 𝕜 n f s x) (hn : 1 ≤ n) :
  differentiable_within_at 𝕜 f (insert x s) x :=
begin
  rcases h 1 hn with ⟨u, hu, p, H⟩,
  rcases mem_nhds_within.1 hu with ⟨t, t_open, xt, tu⟩,
  rw inter_comm at tu,
  have := ((H.mono tu).differentiable_on le_rfl) x ⟨mem_insert x s, xt⟩,
  exact (differentiable_within_at_inter (is_open.mem_nhds t_open xt)).1 this,
end

lemma cont_diff_within_at.differentiable_within_at
  (h : cont_diff_within_at 𝕜 n f s x) (hn : 1 ≤ n) :
  differentiable_within_at 𝕜 f s x :=
(h.differentiable_within_at' hn).mono (subset_insert x s)

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem cont_diff_within_at_succ_iff_has_fderiv_within_at {n : ℕ} :
  cont_diff_within_at 𝕜 ((n + 1) : ℕ) f s x
  ↔ ∃ u ∈ 𝓝[insert x s] x, ∃ f' : E → (E →L[𝕜] F),
    (∀ x ∈ u, has_fderiv_within_at f (f' x) u x) ∧ (cont_diff_within_at 𝕜 n f' u x) :=
begin
  split,
  { assume h,
    rcases h n.succ le_rfl with ⟨u, hu, p, Hp⟩,
    refine ⟨u, hu, λ y, (continuous_multilinear_curry_fin1 𝕜 E F) (p y 1),
      λ y hy, Hp.has_fderiv_within_at (with_top.coe_le_coe.2 (nat.le_add_left 1 n)) hy, _⟩,
    assume m hm,
    refine ⟨u, _, λ (y : E), (p y).shift, _⟩,
    { convert self_mem_nhds_within,
      have : x ∈ insert x s, by simp,
      exact (insert_eq_of_mem (mem_of_mem_nhds_within this hu)) },
    { rw has_ftaylor_series_up_to_on_succ_iff_right at Hp,
      exact Hp.2.2.of_le hm } },
  { rintros ⟨u, hu, f', f'_eq_deriv, Hf'⟩,
    rw cont_diff_within_at_nat,
    rcases Hf' n le_rfl with ⟨v, hv, p', Hp'⟩,
    refine ⟨v ∩ u, _, λ x, (p' x).unshift (f x), _⟩,
    { apply filter.inter_mem _ hu,
      apply nhds_within_le_of_mem hu,
      exact nhds_within_mono _ (subset_insert x u) hv },
    { rw has_ftaylor_series_up_to_on_succ_iff_right,
      refine ⟨λ y hy, rfl, λ y hy, _, _⟩,
      { change has_fderiv_within_at (λ z, (continuous_multilinear_curry_fin0 𝕜 E F).symm (f z))
          ((formal_multilinear_series.unshift (p' y) (f y) 1).curry_left) (v ∩ u) y,
        rw linear_isometry_equiv.comp_has_fderiv_within_at_iff',
        convert (f'_eq_deriv y hy.2).mono (inter_subset_right v u),
        rw ← Hp'.zero_eq y hy.1,
        ext z,
        change ((p' y 0) (init (@cons 0 (λ i, E) z 0))) (@cons 0 (λ i, E) z 0 (last 0))
          = ((p' y 0) 0) z,
        unfold_coes,
        congr },
      { convert (Hp'.mono (inter_subset_left v u)).congr (λ x hx, Hp'.zero_eq x hx.1),
        { ext x y,
          change p' x 0 (init (@snoc 0 (λ i : fin 1, E) 0 y)) y = p' x 0 0 y,
          rw init_snoc },
        { ext x k v y,
          change p' x k (init (@snoc k (λ i : fin k.succ, E) v y))
            (@snoc k (λ i : fin k.succ, E) v y (last k)) = p' x k v y,
          rw [snoc_last, init_snoc] } } } }
end

/-- A version of `cont_diff_within_at_succ_iff_has_fderiv_within_at` where all derivatives
  are taken within the same set. -/
lemma cont_diff_within_at_succ_iff_has_fderiv_within_at' {n : ℕ} :
  cont_diff_within_at 𝕜 (n + 1 : ℕ) f s x
  ↔ ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ ∃ f' : E → E →L[𝕜] F,
    (∀ x ∈ u, has_fderiv_within_at f (f' x) s x) ∧ cont_diff_within_at 𝕜 n f' s x :=
begin
  refine ⟨λ hf, _, _⟩,
  { obtain ⟨u, hu, f', huf', hf'⟩ := cont_diff_within_at_succ_iff_has_fderiv_within_at.mp hf,
    obtain ⟨w, hw, hxw, hwu⟩ := mem_nhds_within.mp hu,
    rw [inter_comm] at hwu,
    refine ⟨insert x s ∩ w, inter_mem_nhds_within _ (hw.mem_nhds hxw), inter_subset_left _ _,
      f', λ y hy, _, _⟩,
    { refine ((huf' y $ hwu hy).mono hwu).mono_of_mem _,
      refine mem_of_superset _ (inter_subset_inter_left _ (subset_insert _ _)),
      refine inter_mem_nhds_within _ (hw.mem_nhds hy.2) },
    { exact hf'.mono_of_mem (nhds_within_mono _ (subset_insert _ _) hu) } },
  { rw [← cont_diff_within_at_insert, cont_diff_within_at_succ_iff_has_fderiv_within_at,
      insert_eq_of_mem (mem_insert _ _)],
    rintro ⟨u, hu, hus, f', huf', hf'⟩,
    refine ⟨u, hu, f', λ y hy, (huf' y hy).insert'.mono hus, hf'.insert.mono hus⟩ }
end

/-! ### Smooth functions within a set -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` on `s` if, for any point `x` in `s`, it
admits continuous derivatives up to order `n` on a neighborhood of `x` in `s`.

For `n = ∞`, we only require that this holds up to any finite order (where the neighborhood may
depend on the finite order we consider).
-/
def cont_diff_on (n : ℕ∞) (f : E → F) (s : set E) : Prop :=
∀ x ∈ s, cont_diff_within_at 𝕜 n f s x

variable {𝕜}

lemma has_ftaylor_series_up_to_on.cont_diff_on {f' : E → formal_multilinear_series 𝕜 E F}
  (hf : has_ftaylor_series_up_to_on n f f' s) : cont_diff_on 𝕜 n f s :=
begin
  intros x hx m hm,
  use s,
  simp only [set.insert_eq_of_mem hx, self_mem_nhds_within, true_and],
  exact ⟨f', hf.of_le hm⟩,
end

lemma cont_diff_on.cont_diff_within_at (h : cont_diff_on 𝕜 n f s) (hx : x ∈ s) :
  cont_diff_within_at 𝕜 n f s x :=
h x hx

lemma cont_diff_within_at.cont_diff_on {m : ℕ}
  (hm : (m : ℕ∞) ≤ n) (h : cont_diff_within_at 𝕜 n f s x) :
  ∃ u ∈ 𝓝[insert x s] x, u ⊆ insert x s ∧ cont_diff_on 𝕜 m f u :=
begin
  rcases h m hm with ⟨u, u_nhd, p, hp⟩,
  refine ⟨u ∩ insert x s, filter.inter_mem u_nhd self_mem_nhds_within,
    inter_subset_right _ _, _⟩,
  assume y hy m' hm',
  refine ⟨u ∩ insert x s, _, p, (hp.mono (inter_subset_left _ _)).of_le hm'⟩,
  convert self_mem_nhds_within,
  exact insert_eq_of_mem hy
end

protected lemma cont_diff_within_at.eventually {n : ℕ}
  (h : cont_diff_within_at 𝕜 n f s x) :
  ∀ᶠ y in 𝓝[insert x s] x, cont_diff_within_at 𝕜 n f s y :=
begin
  rcases h.cont_diff_on le_rfl with ⟨u, hu, hu_sub, hd⟩,
  have : ∀ᶠ (y : E) in 𝓝[insert x s] x, u ∈ 𝓝[insert x s] y ∧ y ∈ u,
    from (eventually_nhds_within_nhds_within.2 hu).and hu,
  refine this.mono (λ y hy, (hd y hy.2).mono_of_mem _),
  exact nhds_within_mono y (subset_insert _ _) hy.1
end

lemma cont_diff_on.of_le (h : cont_diff_on 𝕜 n f s) (hmn : m ≤ n) :
  cont_diff_on 𝕜 m f s :=
λ x hx, (h x hx).of_le hmn

lemma cont_diff_on.of_succ {n : ℕ} (h : cont_diff_on 𝕜 (n + 1) f s) : cont_diff_on 𝕜 n f s :=
h.of_le $ with_top.coe_le_coe.mpr le_self_add

lemma cont_diff_on.one_of_succ {n : ℕ} (h : cont_diff_on 𝕜 (n + 1) f s) : cont_diff_on 𝕜 1 f s :=
h.of_le $ with_top.coe_le_coe.mpr le_add_self

lemma cont_diff_on_iff_forall_nat_le :
  cont_diff_on 𝕜 n f s ↔ ∀ m : ℕ, ↑m ≤ n → cont_diff_on 𝕜 m f s :=
⟨λ H m hm, H.of_le hm, λ H x hx m hm, H m hm x hx m le_rfl⟩

lemma cont_diff_on_top :
  cont_diff_on 𝕜 ∞ f s ↔ ∀ (n : ℕ), cont_diff_on 𝕜 n f s :=
cont_diff_on_iff_forall_nat_le.trans $ by simp only [le_top, forall_prop_of_true]

lemma cont_diff_on_all_iff_nat :
  (∀ n, cont_diff_on 𝕜 n f s) ↔ (∀ n : ℕ, cont_diff_on 𝕜 n f s) :=
begin
  refine ⟨λ H n, H n, _⟩,
  rintro H (_|n),
  exacts [cont_diff_on_top.2 H, H n]
end

lemma cont_diff_on.continuous_on
  (h : cont_diff_on 𝕜 n f s) : continuous_on f s :=
λ x hx, (h x hx).continuous_within_at

lemma cont_diff_on.congr
  (h : cont_diff_on 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
  cont_diff_on 𝕜 n f₁ s :=
λ x hx, (h x hx).congr h₁ (h₁ x hx)

lemma cont_diff_on_congr (h₁ : ∀ x ∈ s, f₁ x = f x) :
  cont_diff_on 𝕜 n f₁ s ↔ cont_diff_on 𝕜 n f s :=
⟨λ H, H.congr (λ x hx, (h₁ x hx).symm), λ H, H.congr h₁⟩

lemma cont_diff_on.mono
  (h : cont_diff_on 𝕜 n f s) {t : set E} (hst : t ⊆ s) :
  cont_diff_on 𝕜 n f t :=
λ x hx, (h x (hst hx)).mono hst

lemma cont_diff_on.congr_mono
  (hf : cont_diff_on 𝕜 n f s) (h₁ : ∀ x ∈ s₁, f₁ x = f x) (hs : s₁ ⊆ s) :
  cont_diff_on 𝕜 n f₁ s₁ :=
(hf.mono hs).congr h₁

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
lemma cont_diff_on.differentiable_on
  (h : cont_diff_on 𝕜 n f s) (hn : 1 ≤ n) : differentiable_on 𝕜 f s :=
λ x hx, (h x hx).differentiable_within_at hn

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
lemma cont_diff_on_of_locally_cont_diff_on
  (h : ∀ x ∈ s, ∃u, is_open u ∧ x ∈ u ∧ cont_diff_on 𝕜 n f (s ∩ u)) :
  cont_diff_on 𝕜 n f s :=
begin
  assume x xs,
  rcases h x xs with ⟨u, u_open, xu, hu⟩,
  apply (cont_diff_within_at_inter _).1 (hu x ⟨xs, xu⟩),
  exact is_open.mem_nhds u_open xu
end

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem cont_diff_on_succ_iff_has_fderiv_within_at {n : ℕ} :
  cont_diff_on 𝕜 ((n + 1) : ℕ) f s
  ↔ ∀ x ∈ s, ∃ u ∈ 𝓝[insert x s] x, ∃ f' : E → (E →L[𝕜] F),
    (∀ x ∈ u, has_fderiv_within_at f (f' x) u x) ∧ (cont_diff_on 𝕜 n f' u) :=
begin
  split,
  { assume h x hx,
    rcases (h x hx) n.succ le_rfl with ⟨u, hu, p, Hp⟩,
    refine ⟨u, hu, λ y, (continuous_multilinear_curry_fin1 𝕜 E F) (p y 1),
      λ y hy, Hp.has_fderiv_within_at (with_top.coe_le_coe.2 (nat.le_add_left 1 n)) hy, _⟩,
    rw has_ftaylor_series_up_to_on_succ_iff_right at Hp,
    assume z hz m hm,
    refine ⟨u, _, λ (x : E), (p x).shift, Hp.2.2.of_le hm⟩,
    convert self_mem_nhds_within,
    exact insert_eq_of_mem hz, },
  { assume h x hx,
    rw cont_diff_within_at_succ_iff_has_fderiv_within_at,
    rcases h x hx with ⟨u, u_nhbd, f', hu, hf'⟩,
    have : x ∈ u := mem_of_mem_nhds_within (mem_insert _ _) u_nhbd,
    exact ⟨u, u_nhbd, f', hu, hf' x this⟩ }
end

/-! ### Iterated derivative within a set -/
variable (𝕜)

/--
The `n`-th derivative of a function along a set, defined inductively by saying that the `n+1`-th
derivative of `f` is the derivative of the `n`-th derivative of `f` along this set, together with
an uncurrying step to see it as a multilinear map in `n+1` variables..
-/
noncomputable def iterated_fderiv_within (n : ℕ) (f : E → F) (s : set E) :
  E → (E [×n]→L[𝕜] F) :=
nat.rec_on n
  (λ x, continuous_multilinear_map.curry0 𝕜 E (f x))
  (λ n rec x, continuous_linear_map.uncurry_left (fderiv_within 𝕜 rec s x))

/-- Formal Taylor series associated to a function within a set. -/
def ftaylor_series_within (f : E → F) (s : set E) (x : E) : formal_multilinear_series 𝕜 E F :=
λ n, iterated_fderiv_within 𝕜 n f s x

variable {𝕜}

@[simp] lemma iterated_fderiv_within_zero_apply (m : (fin 0) → E) :
  (iterated_fderiv_within 𝕜 0 f s x : ((fin 0) →  E) → F) m = f x := rfl

lemma iterated_fderiv_within_zero_eq_comp :
  iterated_fderiv_within 𝕜 0 f s = (continuous_multilinear_curry_fin0 𝕜 E F).symm ∘ f := rfl

@[simp] lemma norm_iterated_fderiv_within_zero :
  ‖iterated_fderiv_within 𝕜 0 f s x‖ = ‖f x‖ :=
by rw [iterated_fderiv_within_zero_eq_comp, linear_isometry_equiv.norm_map]

lemma iterated_fderiv_within_succ_apply_left {n : ℕ} (m : fin (n + 1) → E):
  (iterated_fderiv_within 𝕜 (n + 1) f s x : (fin (n + 1) → E) → F) m
  = (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s x : E → (E [×n]→L[𝕜] F))
      (m 0) (tail m) := rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
lemma iterated_fderiv_within_succ_eq_comp_left {n : ℕ} :
  iterated_fderiv_within 𝕜 (n + 1) f s =
  (continuous_multilinear_curry_left_equiv 𝕜 (λ(i : fin (n + 1)), E) F)
    ∘ (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s) := rfl

lemma norm_fderiv_within_iterated_fderiv_within {n : ℕ} :
  ‖fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s x‖ =
  ‖iterated_fderiv_within 𝕜 (n + 1) f s x‖ :=
by rw [iterated_fderiv_within_succ_eq_comp_left, linear_isometry_equiv.norm_map]

theorem iterated_fderiv_within_succ_apply_right {n : ℕ}
  (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (m : fin (n + 1) → E) :
  (iterated_fderiv_within 𝕜 (n + 1) f s x : (fin (n + 1) → E) → F) m
    = iterated_fderiv_within 𝕜 n (λy, fderiv_within 𝕜 f s y) s x (init m) (m (last n)) :=
begin
  induction n with n IH generalizing x,
  { rw [iterated_fderiv_within_succ_eq_comp_left, iterated_fderiv_within_zero_eq_comp,
        iterated_fderiv_within_zero_apply,
        function.comp_apply, linear_isometry_equiv.comp_fderiv_within _ (hs x hx)],
    refl },
  { let I := continuous_multilinear_curry_right_equiv' 𝕜 n E F,
    have A : ∀ y ∈ s, iterated_fderiv_within 𝕜 n.succ f s y
        = (I ∘ (iterated_fderiv_within 𝕜 n (λy, fderiv_within 𝕜 f s y) s)) y,
      by { assume y hy, ext m, rw @IH m y hy, refl },
    calc
    (iterated_fderiv_within 𝕜 (n+2) f s x : (fin (n+2) → E) → F) m =
    (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n.succ f s) s x
              : E → (E [×(n + 1)]→L[𝕜] F)) (m 0) (tail m) : rfl
    ... = (fderiv_within 𝕜 (I ∘ (iterated_fderiv_within 𝕜 n (fderiv_within 𝕜 f s) s)) s x
              : E → (E [×(n + 1)]→L[𝕜] F)) (m 0) (tail m) :
      by rw fderiv_within_congr (hs x hx) A (A x hx)
    ... = (I ∘ fderiv_within 𝕜 ((iterated_fderiv_within 𝕜 n (fderiv_within 𝕜 f s) s)) s x
              : E → (E [×(n + 1)]→L[𝕜] F)) (m 0) (tail m) :
      by { rw linear_isometry_equiv.comp_fderiv_within _ (hs x hx), refl }
    ... = (fderiv_within 𝕜 ((iterated_fderiv_within 𝕜 n (λ y, fderiv_within 𝕜 f s y) s)) s x
              : E → (E [×n]→L[𝕜] (E →L[𝕜] F))) (m 0) (init (tail m)) ((tail m) (last n)) : rfl
    ... = iterated_fderiv_within 𝕜 (nat.succ n) (λ y, fderiv_within 𝕜 f s y) s x
              (init m) (m (last (n + 1))) :
      by { rw [iterated_fderiv_within_succ_apply_left, tail_init_eq_init_tail], refl } }
end

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
lemma iterated_fderiv_within_succ_eq_comp_right {n : ℕ} (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  iterated_fderiv_within 𝕜 (n + 1) f s x =
  ((continuous_multilinear_curry_right_equiv' 𝕜 n E F)
    ∘ (iterated_fderiv_within 𝕜 n (λy, fderiv_within 𝕜 f s y) s)) x :=
by { ext m, rw iterated_fderiv_within_succ_apply_right hs hx, refl }

lemma norm_iterated_fderiv_within_fderiv_within {n : ℕ} (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  ‖iterated_fderiv_within 𝕜 n (fderiv_within 𝕜 f s) s x‖ =
  ‖iterated_fderiv_within 𝕜 (n + 1) f s x‖ :=
by rw [iterated_fderiv_within_succ_eq_comp_right hs hx, linear_isometry_equiv.norm_map]

@[simp] lemma iterated_fderiv_within_one_apply
  (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (m : (fin 1) → E) :
  (iterated_fderiv_within 𝕜 1 f s x : ((fin 1) → E) → F) m
  = (fderiv_within 𝕜 f s x : E → F) (m 0) :=
by { rw [iterated_fderiv_within_succ_apply_right hs hx, iterated_fderiv_within_zero_apply], refl }

/-- If two functions coincide on a set `s` of unique differentiability, then their iterated
differentials within this set coincide. -/
lemma iterated_fderiv_within_congr {n : ℕ}
  (hs : unique_diff_on 𝕜 s) (hL : ∀y∈s, f₁ y = f y) (hx : x ∈ s) :
  iterated_fderiv_within 𝕜 n f₁ s x = iterated_fderiv_within 𝕜 n f s x :=
begin
  induction n with n IH generalizing x,
  { ext m, simp [hL x hx] },
  { have : fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f₁ s y) s x
           = fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f s y) s x :=
      fderiv_within_congr (hs x hx) (λ y hy, IH hy) (IH hx),
    ext m,
    rw [iterated_fderiv_within_succ_apply_left, iterated_fderiv_within_succ_apply_left, this] }
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with an open set containing `x`. -/
lemma iterated_fderiv_within_inter_open {n : ℕ} (hu : is_open u)
  (hs : unique_diff_on 𝕜 (s ∩ u)) (hx : x ∈ s ∩ u) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
begin
  induction n with n IH generalizing x,
  { ext m, simp },
  { have A : fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f (s ∩ u) y) (s ∩ u) x
           = fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f s y) (s ∩ u) x :=
      fderiv_within_congr (hs x hx) (λ y hy, IH hy) (IH hx),
    have B : fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f s y) (s ∩ u) x
           = fderiv_within 𝕜 (λ y, iterated_fderiv_within 𝕜 n f s y) s x :=
      fderiv_within_inter (is_open.mem_nhds hu hx.2)
        ((unique_diff_within_at_inter (is_open.mem_nhds hu hx.2)).1 (hs x hx)),
    ext m,
    rw [iterated_fderiv_within_succ_apply_left, iterated_fderiv_within_succ_apply_left, A, B] }
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x` within `s`. -/
lemma iterated_fderiv_within_inter' {n : ℕ}
  (hu : u ∈ 𝓝[s] x) (hs : unique_diff_on 𝕜 s) (xs : x ∈ s) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
begin
  obtain ⟨v, v_open, xv, vu⟩ : ∃ v, is_open v ∧ x ∈ v ∧ v ∩ s ⊆ u := mem_nhds_within.1 hu,
  have A : (s ∩ u) ∩ v = s ∩ v,
  { apply subset.antisymm (inter_subset_inter (inter_subset_left _ _) (subset.refl _)),
    exact λ y ⟨ys, yv⟩, ⟨⟨ys, vu ⟨yv, ys⟩⟩, yv⟩ },
  have : iterated_fderiv_within 𝕜 n f (s ∩ v) x = iterated_fderiv_within 𝕜 n f s x :=
    iterated_fderiv_within_inter_open v_open (hs.inter v_open) ⟨xs, xv⟩,
  rw ← this,
  have : iterated_fderiv_within 𝕜 n f ((s ∩ u) ∩ v) x = iterated_fderiv_within 𝕜 n f (s ∩ u) x,
  { refine iterated_fderiv_within_inter_open v_open _ ⟨⟨xs, vu ⟨xv, xs⟩⟩, xv⟩,
    rw A,
    exact hs.inter v_open },
  rw A at this,
  rw ← this
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`. -/
lemma iterated_fderiv_within_inter {n : ℕ}
  (hu : u ∈ 𝓝 x) (hs : unique_diff_on 𝕜 s) (xs : x ∈ s) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
iterated_fderiv_within_inter' (mem_nhds_within_of_mem_nhds hu) hs xs

@[simp] lemma cont_diff_on_zero :
  cont_diff_on 𝕜 0 f s ↔ continuous_on f s :=
begin
  refine ⟨λ H, H.continuous_on, λ H, _⟩,
  assume x hx m hm,
  have : (m : ℕ∞) = 0 := le_antisymm hm bot_le,
  rw this,
  refine ⟨insert x s, self_mem_nhds_within, ftaylor_series_within 𝕜 f s, _⟩,
  rw has_ftaylor_series_up_to_on_zero_iff,
  exact ⟨by rwa insert_eq_of_mem hx, λ x hx, by simp [ftaylor_series_within]⟩
end

lemma cont_diff_within_at_zero (hx : x ∈ s) :
  cont_diff_within_at 𝕜 0 f s x ↔ ∃ u ∈ 𝓝[s] x, continuous_on f (s ∩ u) :=
begin
  split,
  { intros h,
    obtain ⟨u, H, p, hp⟩ := h 0 (by norm_num),
    refine ⟨u, _, _⟩,
    { simpa [hx] using H },
    { simp only [with_top.coe_zero, has_ftaylor_series_up_to_on_zero_iff] at hp,
      exact hp.1.mono (inter_subset_right s u) } },
  { rintros ⟨u, H, hu⟩,
    rw ← cont_diff_within_at_inter' H,
    have h' : x ∈ s ∩ u := ⟨hx, mem_of_mem_nhds_within hx H⟩,
    exact (cont_diff_on_zero.mpr hu).cont_diff_within_at h' }
end

/-- On a set with unique differentiability, any choice of iterated differential has to coincide
with the one we have chosen in `iterated_fderiv_within 𝕜 m f s`. -/
theorem has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on
  (h : has_ftaylor_series_up_to_on n f p s)
  {m : ℕ} (hmn : (m : ℕ∞) ≤ n) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  p x m = iterated_fderiv_within 𝕜 m f s x :=
begin
  induction m with m IH generalizing x,
  { rw [h.zero_eq' hx, iterated_fderiv_within_zero_eq_comp] },
  { have A : (m : ℕ∞) < n := lt_of_lt_of_le (with_top.coe_lt_coe.2 (lt_add_one m)) hmn,
    have : has_fderiv_within_at (λ (y : E), iterated_fderiv_within 𝕜 m f s y)
      (continuous_multilinear_map.curry_left (p x (nat.succ m))) s x :=
    (h.fderiv_within m A x hx).congr (λ y hy, (IH (le_of_lt A) hy).symm) (IH (le_of_lt A) hx).symm,
    rw [iterated_fderiv_within_succ_eq_comp_left, function.comp_apply,
      this.fderiv_within (hs x hx)],
    exact (continuous_multilinear_map.uncurry_curry_left _).symm }
end

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem cont_diff_on.ftaylor_series_within
  (h : cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) :
  has_ftaylor_series_up_to_on n f (ftaylor_series_within 𝕜 f s) s :=
begin
  split,
  { assume x hx,
    simp only [ftaylor_series_within, continuous_multilinear_map.uncurry0_apply,
               iterated_fderiv_within_zero_apply] },
  { assume m hm x hx,
    rcases (h x hx) m.succ (enat.add_one_le_of_lt hm) with ⟨u, hu, p, Hp⟩,
    rw insert_eq_of_mem hx at hu,
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
    rw inter_comm at ho,
    have : p x m.succ = ftaylor_series_within 𝕜 f s x m.succ,
    { change p x m.succ = iterated_fderiv_within 𝕜 m.succ f s x,
      rw ← iterated_fderiv_within_inter (is_open.mem_nhds o_open xo) hs hx,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on le_rfl
        (hs.inter o_open) ⟨hx, xo⟩ },
    rw [← this, ← has_fderiv_within_at_inter (is_open.mem_nhds o_open xo)],
    have A : ∀ y ∈ s ∩ o, p y m = ftaylor_series_within 𝕜 f s y m,
    { rintros y ⟨hy, yo⟩,
      change p y m = iterated_fderiv_within 𝕜 m f s y,
      rw ← iterated_fderiv_within_inter (is_open.mem_nhds o_open yo) hs hy,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (with_top.coe_le_coe.2 (nat.le_succ m))
        (hs.inter o_open) ⟨hy, yo⟩ },
    exact ((Hp.mono ho).fderiv_within m (with_top.coe_lt_coe.2 (lt_add_one m)) x ⟨hx, xo⟩).congr
      (λ y hy, (A y hy).symm) (A x ⟨hx, xo⟩).symm },
  { assume m hm,
    apply continuous_on_of_locally_continuous_on,
    assume x hx,
    rcases h x hx m hm with ⟨u, hu, p, Hp⟩,
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
    rw insert_eq_of_mem hx at ho,
    rw inter_comm at ho,
    refine ⟨o, o_open, xo, _⟩,
    have A : ∀ y ∈ s ∩ o, p y m = ftaylor_series_within 𝕜 f s y m,
    { rintros y ⟨hy, yo⟩,
      change p y m = iterated_fderiv_within 𝕜 m f s y,
      rw ← iterated_fderiv_within_inter (is_open.mem_nhds o_open yo) hs hy,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on le_rfl
        (hs.inter o_open) ⟨hy, yo⟩ },
    exact ((Hp.mono ho).cont m le_rfl).congr (λ y hy, (A y hy).symm) }
end

lemma cont_diff_on_of_continuous_on_differentiable_on
  (Hcont : ∀ (m : ℕ), (m : ℕ∞) ≤ n →
    continuous_on (λ x, iterated_fderiv_within 𝕜 m f s x) s)
  (Hdiff : ∀ (m : ℕ), (m : ℕ∞) < n →
    differentiable_on 𝕜 (λ x, iterated_fderiv_within 𝕜 m f s x) s) :
  cont_diff_on 𝕜 n f s :=
begin
  assume x hx m hm,
  rw insert_eq_of_mem hx,
  refine ⟨s, self_mem_nhds_within, ftaylor_series_within 𝕜 f s, _⟩,
  split,
  { assume y hy,
    simp only [ftaylor_series_within, continuous_multilinear_map.uncurry0_apply,
                iterated_fderiv_within_zero_apply] },
  { assume k hk y hy,
    convert (Hdiff k (lt_of_lt_of_le hk hm) y hy).has_fderiv_within_at,
    simp only [ftaylor_series_within, iterated_fderiv_within_succ_eq_comp_left,
                continuous_linear_equiv.coe_apply, function.comp_app, coe_fn_coe_base],
    exact continuous_linear_map.curry_uncurry_left _ },
  { assume k hk,
    exact Hcont k (le_trans hk hm) }
end

lemma cont_diff_on_of_differentiable_on
  (h : ∀(m : ℕ), (m : ℕ∞) ≤ n → differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s) :
  cont_diff_on 𝕜 n f s :=
cont_diff_on_of_continuous_on_differentiable_on
  (λ m hm, (h m hm).continuous_on) (λ m hm, (h m (le_of_lt hm)))

lemma cont_diff_on.continuous_on_iterated_fderiv_within {m : ℕ}
  (h : cont_diff_on 𝕜 n f s) (hmn : (m : ℕ∞) ≤ n) (hs : unique_diff_on 𝕜 s) :
  continuous_on (iterated_fderiv_within 𝕜 m f s) s :=
(h.ftaylor_series_within hs).cont m hmn

lemma cont_diff_on.differentiable_on_iterated_fderiv_within {m : ℕ}
  (h : cont_diff_on 𝕜 n f s) (hmn : (m : ℕ∞) < n) (hs : unique_diff_on 𝕜 s) :
  differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s :=
λ x hx, ((h.ftaylor_series_within hs).fderiv_within m hmn x hx).differentiable_within_at

lemma cont_diff_on_iff_continuous_on_differentiable_on
  (hs : unique_diff_on 𝕜 s) :
  cont_diff_on 𝕜 n f s ↔
  (∀ (m : ℕ), (m : ℕ∞) ≤ n →
    continuous_on (λ x, iterated_fderiv_within 𝕜 m f s x) s)
  ∧ (∀ (m : ℕ), (m : ℕ∞) < n →
    differentiable_on 𝕜 (λ x, iterated_fderiv_within 𝕜 m f s x) s) :=
begin
  split,
  { assume h,
    split,
    { assume m hm, exact h.continuous_on_iterated_fderiv_within hm hs },
    { assume m hm, exact h.differentiable_on_iterated_fderiv_within hm hs } },
  { assume h,
    exact cont_diff_on_of_continuous_on_differentiable_on h.1 h.2 }
end

lemma cont_diff_on_succ_of_fderiv_within {n : ℕ} (hf : differentiable_on 𝕜 f s)
  (h : cont_diff_on 𝕜 n (λ y, fderiv_within 𝕜 f s y) s) :
  cont_diff_on 𝕜 ((n + 1) : ℕ) f s :=
begin
  intros x hx,
  rw [cont_diff_within_at_succ_iff_has_fderiv_within_at, insert_eq_of_mem hx],
  exact ⟨s, self_mem_nhds_within, fderiv_within 𝕜 f s,
    λ y hy, (hf y hy).has_fderiv_within_at, h x hx⟩
end

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is
differentiable there, and its derivative (expressed with `fderiv_within`) is `C^n`. -/
theorem cont_diff_on_succ_iff_fderiv_within {n : ℕ} (hs : unique_diff_on 𝕜 s) :
  cont_diff_on 𝕜 ((n + 1) : ℕ) f s ↔
  differentiable_on 𝕜 f s ∧ cont_diff_on 𝕜 n (λ y, fderiv_within 𝕜 f s y) s :=
begin
  refine ⟨λ H, _, λ h, cont_diff_on_succ_of_fderiv_within h.1 h.2⟩,
  refine ⟨H.differentiable_on (with_top.coe_le_coe.2 (nat.le_add_left 1 n)), λ x hx, _⟩,
  rcases cont_diff_within_at_succ_iff_has_fderiv_within_at.1 (H x hx)
    with ⟨u, hu, f', hff', hf'⟩,
  rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
  rw [inter_comm, insert_eq_of_mem hx] at ho,
  have := hf'.mono ho,
  rw cont_diff_within_at_inter' (mem_nhds_within_of_mem_nhds (is_open.mem_nhds o_open xo))
    at this,
  apply this.congr_of_eventually_eq' _ hx,
  have : o ∩ s ∈ 𝓝[s] x := mem_nhds_within.2 ⟨o, o_open, xo, subset.refl _⟩,
  rw inter_comm at this,
  apply filter.eventually_eq_of_mem this (λ y hy, _),
  have A : fderiv_within 𝕜 f (s ∩ o) y = f' y :=
    ((hff' y (ho hy)).mono ho).fderiv_within (hs.inter o_open y hy),
  rwa fderiv_within_inter (is_open.mem_nhds o_open hy.2) (hs y hy.1) at A
end

/-- A function is `C^(n + 1)` on an open domain if and only if it is
differentiable there, and its derivative (expressed with `fderiv`) is `C^n`. -/
theorem cont_diff_on_succ_iff_fderiv_of_open {n : ℕ} (hs : is_open s) :
  cont_diff_on 𝕜 ((n + 1) : ℕ) f s ↔
  differentiable_on 𝕜 f s ∧ cont_diff_on 𝕜 n (λ y, fderiv 𝕜 f y) s :=
begin
  rw cont_diff_on_succ_iff_fderiv_within hs.unique_diff_on,
  congrm _ ∧ _,
  apply cont_diff_on_congr,
  assume x hx,
  exact fderiv_within_of_open hs hx
end

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative (expressed with `fderiv_within`) is `C^∞`. -/
theorem cont_diff_on_top_iff_fderiv_within (hs : unique_diff_on 𝕜 s) :
  cont_diff_on 𝕜 ∞ f s ↔
  differentiable_on 𝕜 f s ∧ cont_diff_on 𝕜 ∞ (λ y, fderiv_within 𝕜 f s y) s :=
begin
  split,
  { assume h,
    refine ⟨h.differentiable_on le_top, _⟩,
    apply cont_diff_on_top.2 (λ n, ((cont_diff_on_succ_iff_fderiv_within hs).1 _).2),
    exact h.of_le le_top },
  { assume h,
    refine cont_diff_on_top.2 (λ n, _),
    have A : (n : ℕ∞) ≤ ∞ := le_top,
    apply ((cont_diff_on_succ_iff_fderiv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le,
    exact with_top.coe_le_coe.2 (nat.le_succ n) }
end

/-- A function is `C^∞` on an open domain if and only if it is differentiable there, and its
derivative (expressed with `fderiv`) is `C^∞`. -/
theorem cont_diff_on_top_iff_fderiv_of_open (hs : is_open s) :
  cont_diff_on 𝕜 ∞ f s ↔
  differentiable_on 𝕜 f s ∧ cont_diff_on 𝕜 ∞ (λ y, fderiv 𝕜 f y) s :=
begin
  rw cont_diff_on_top_iff_fderiv_within hs.unique_diff_on,
  congrm _ ∧ _,
  apply cont_diff_on_congr,
  assume x hx,
  exact fderiv_within_of_open hs hx
end

lemma cont_diff_on.fderiv_within
  (hf : cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) :
  cont_diff_on 𝕜 m (λ y, fderiv_within 𝕜 f s y) s :=
begin
  cases m,
  { change ∞ + 1 ≤ n at hmn,
    have : n = ∞, by simpa using hmn,
    rw this at hf,
    exact ((cont_diff_on_top_iff_fderiv_within hs).1 hf).2 },
  { change (m.succ : ℕ∞) ≤ n at hmn,
    exact ((cont_diff_on_succ_iff_fderiv_within hs).1 (hf.of_le hmn)).2 }
end

lemma cont_diff_on.fderiv_of_open
  (hf : cont_diff_on 𝕜 n f s) (hs : is_open s) (hmn : m + 1 ≤ n) :
  cont_diff_on 𝕜 m (λ y, fderiv 𝕜 f y) s :=
(hf.fderiv_within hs.unique_diff_on hmn).congr (λ x hx, (fderiv_within_of_open hs hx).symm)

lemma cont_diff_on.continuous_on_fderiv_within
  (h : cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hn : 1 ≤ n) :
  continuous_on (λ x, fderiv_within 𝕜 f s x) s :=
((cont_diff_on_succ_iff_fderiv_within hs).1 (h.of_le hn)).2.continuous_on

lemma cont_diff_on.continuous_on_fderiv_of_open
  (h : cont_diff_on 𝕜 n f s) (hs : is_open s) (hn : 1 ≤ n) :
  continuous_on (λ x, fderiv 𝕜 f x) s :=
((cont_diff_on_succ_iff_fderiv_of_open hs).1 (h.of_le hn)).2.continuous_on

/-! ### Functions with a Taylor series on the whole space -/

/-- `has_ftaylor_series_up_to n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_at` but for higher order derivatives. -/
structure has_ftaylor_series_up_to (n : ℕ∞)
  (f : E → F) (p : E → formal_multilinear_series 𝕜 E F) : Prop :=
(zero_eq : ∀ x, (p x 0).uncurry0 = f x)
(fderiv  : ∀ (m : ℕ) (hm : (m : ℕ∞) < n), ∀ x,
    has_fderiv_at (λ y, p y m) (p x m.succ).curry_left x)
(cont    : ∀ (m : ℕ) (hm : (m : ℕ∞) ≤ n), continuous (λ x, p x m))

lemma has_ftaylor_series_up_to.zero_eq'
  (h : has_ftaylor_series_up_to n f p) (x : E) :
  p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x) :=
by { rw ← h.zero_eq x, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ }

lemma has_ftaylor_series_up_to_on_univ_iff :
  has_ftaylor_series_up_to_on n f p univ ↔ has_ftaylor_series_up_to n f p :=
begin
  split,
  { assume H,
    split,
    { exact λ x, H.zero_eq x (mem_univ x) },
    { assume m hm x,
      rw ← has_fderiv_within_at_univ,
      exact H.fderiv_within m hm x (mem_univ x) },
    { assume m hm,
      rw continuous_iff_continuous_on_univ,
      exact H.cont m hm } },
  { assume H,
    split,
    { exact λ x hx, H.zero_eq x },
    { assume m hm x hx,
      rw has_fderiv_within_at_univ,
      exact H.fderiv m hm x },
    { assume m hm,
      rw ← continuous_iff_continuous_on_univ,
      exact H.cont m hm } }
end

lemma has_ftaylor_series_up_to.has_ftaylor_series_up_to_on
  (h : has_ftaylor_series_up_to n f p) (s : set E) :
  has_ftaylor_series_up_to_on n f p s :=
(has_ftaylor_series_up_to_on_univ_iff.2 h).mono (subset_univ _)

lemma has_ftaylor_series_up_to.of_le
  (h : has_ftaylor_series_up_to n f p) (hmn : m ≤ n) :
  has_ftaylor_series_up_to m f p :=
by { rw ← has_ftaylor_series_up_to_on_univ_iff at h ⊢, exact h.of_le hmn }

lemma has_ftaylor_series_up_to.continuous
  (h : has_ftaylor_series_up_to n f p) : continuous f :=
begin
  rw ← has_ftaylor_series_up_to_on_univ_iff at h,
  rw continuous_iff_continuous_on_univ,
  exact h.continuous_on
end

lemma has_ftaylor_series_up_to_zero_iff :
  has_ftaylor_series_up_to 0 f p ↔ continuous f ∧ (∀ x, (p x 0).uncurry0 = f x) :=
by simp [has_ftaylor_series_up_to_on_univ_iff.symm, continuous_iff_continuous_on_univ,
         has_ftaylor_series_up_to_on_zero_iff]

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
lemma has_ftaylor_series_up_to.has_fderiv_at
  (h : has_ftaylor_series_up_to n f p) (hn : 1 ≤ n) (x : E) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) x :=
begin
  rw [← has_fderiv_within_at_univ],
  exact (has_ftaylor_series_up_to_on_univ_iff.2 h).has_fderiv_within_at hn (mem_univ _)
end

lemma has_ftaylor_series_up_to.differentiable
  (h : has_ftaylor_series_up_to n f p) (hn : 1 ≤ n) : differentiable 𝕜 f :=
λ x, (h.has_fderiv_at hn x).differentiable_at

/-- `p` is a Taylor series of `f` up to `n+1` if and only if `p.shift` is a Taylor series up to `n`
for `p 1`, which is a derivative of `f`. -/
theorem has_ftaylor_series_up_to_succ_iff_right {n : ℕ} :
  has_ftaylor_series_up_to ((n + 1) : ℕ) f p ↔
  (∀ x, (p x 0).uncurry0 = f x)
  ∧ (∀ x, has_fderiv_at (λ y, p y 0) (p x 1).curry_left x)
  ∧ has_ftaylor_series_up_to n
    (λ x, continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) (λ x, (p x).shift) :=
by simp only [has_ftaylor_series_up_to_on_succ_iff_right, ← has_ftaylor_series_up_to_on_univ_iff,
  mem_univ, forall_true_left, has_fderiv_within_at_univ]

/-! ### Smooth functions at a point -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` at a point `x` if, for any integer `k ≤ n`,
there is a neighborhood of `x` where `f` admits derivatives up to order `n`, which are continuous.
-/
def cont_diff_at (n : ℕ∞) (f : E → F) (x : E) : Prop :=
cont_diff_within_at 𝕜 n f univ x

variable {𝕜}

theorem cont_diff_within_at_univ :
  cont_diff_within_at 𝕜 n f univ x ↔ cont_diff_at 𝕜 n f x :=
iff.rfl

lemma cont_diff_at_top :
  cont_diff_at 𝕜 ∞ f x ↔ ∀ (n : ℕ), cont_diff_at 𝕜 n f x :=
by simp [← cont_diff_within_at_univ, cont_diff_within_at_top]

lemma cont_diff_at.cont_diff_within_at
  (h : cont_diff_at 𝕜 n f x) : cont_diff_within_at 𝕜 n f s x :=
h.mono (subset_univ _)

lemma cont_diff_within_at.cont_diff_at
  (h : cont_diff_within_at 𝕜 n f s x) (hx : s ∈ 𝓝 x) :
  cont_diff_at 𝕜 n f x :=
by rwa [cont_diff_at, ← cont_diff_within_at_inter hx, univ_inter]

lemma cont_diff_at.congr_of_eventually_eq
  (h : cont_diff_at 𝕜 n f x) (hg : f₁ =ᶠ[𝓝 x] f) :
  cont_diff_at 𝕜 n f₁ x :=
h.congr_of_eventually_eq' (by rwa nhds_within_univ) (mem_univ x)

lemma cont_diff_at.of_le
  (h : cont_diff_at 𝕜 n f x) (hmn : m ≤ n) :
  cont_diff_at 𝕜 m f x :=
h.of_le hmn

lemma cont_diff_at.continuous_at
  (h : cont_diff_at 𝕜 n f x) : continuous_at f x :=
by simpa [continuous_within_at_univ] using h.continuous_within_at

/-- If a function is `C^n` with `n ≥ 1` at a point, then it is differentiable there. -/
lemma cont_diff_at.differentiable_at
  (h : cont_diff_at 𝕜 n f x) (hn : 1 ≤ n) : differentiable_at 𝕜 f x :=
by simpa [hn, differentiable_within_at_univ] using h.differentiable_within_at

/-- A function is `C^(n + 1)` at a point iff locally, it has a derivative which is `C^n`. -/
theorem cont_diff_at_succ_iff_has_fderiv_at {n : ℕ} :
  cont_diff_at 𝕜 ((n + 1) : ℕ) f x
  ↔ (∃ f' : E → E →L[𝕜] F, (∃ u ∈ 𝓝 x, ∀ x ∈ u, has_fderiv_at f (f' x) x)
      ∧ cont_diff_at 𝕜 n f' x) :=
begin
  rw [← cont_diff_within_at_univ, cont_diff_within_at_succ_iff_has_fderiv_within_at],
  simp only [nhds_within_univ, exists_prop, mem_univ, insert_eq_of_mem],
  split,
  { rintros ⟨u, H, f', h_fderiv, h_cont_diff⟩,
    rcases mem_nhds_iff.mp H with ⟨t, htu, ht, hxt⟩,
    refine ⟨f', ⟨t, _⟩, h_cont_diff.cont_diff_at H⟩,
    refine ⟨mem_nhds_iff.mpr ⟨t, subset.rfl, ht, hxt⟩, _⟩,
    intros y hyt,
    refine (h_fderiv y (htu hyt)).has_fderiv_at _,
    exact mem_nhds_iff.mpr ⟨t, htu, ht, hyt⟩ },
  { rintros ⟨f', ⟨u, H, h_fderiv⟩, h_cont_diff⟩,
    refine ⟨u, H, f', _, h_cont_diff.cont_diff_within_at⟩,
    intros x hxu,
    exact (h_fderiv x hxu).has_fderiv_within_at }
end

protected theorem cont_diff_at.eventually {n : ℕ} (h : cont_diff_at 𝕜 n f x) :
  ∀ᶠ y in 𝓝 x, cont_diff_at 𝕜 n f y :=
by simpa [nhds_within_univ] using h.eventually

/-! ### Smooth functions -/

variable (𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
def cont_diff (n : ℕ∞) (f : E → F) : Prop :=
∃ p : E → formal_multilinear_series 𝕜 E F, has_ftaylor_series_up_to n f p

variable {𝕜}

/-- If `f` has a Taylor series up to `n`, then it is `C^n`. -/
lemma has_ftaylor_series_up_to.cont_diff {f' : E → formal_multilinear_series 𝕜 E F}
  (hf : has_ftaylor_series_up_to n f f') : cont_diff 𝕜 n f := ⟨f', hf⟩

theorem cont_diff_on_univ : cont_diff_on 𝕜 n f univ ↔ cont_diff 𝕜 n f :=
begin
  split,
  { assume H,
    use ftaylor_series_within 𝕜 f univ,
    rw ← has_ftaylor_series_up_to_on_univ_iff,
    exact H.ftaylor_series_within unique_diff_on_univ },
  { rintros ⟨p, hp⟩ x hx m hm,
    exact ⟨univ, filter.univ_sets _, p, (hp.has_ftaylor_series_up_to_on univ).of_le hm⟩ }
end

lemma cont_diff_iff_cont_diff_at : cont_diff 𝕜 n f ↔ ∀ x, cont_diff_at 𝕜 n f x :=
by simp [← cont_diff_on_univ, cont_diff_on, cont_diff_at]

lemma cont_diff.cont_diff_at (h : cont_diff 𝕜 n f) : cont_diff_at 𝕜 n f x :=
cont_diff_iff_cont_diff_at.1 h x

lemma cont_diff.cont_diff_within_at (h : cont_diff 𝕜 n f) : cont_diff_within_at 𝕜 n f s x :=
h.cont_diff_at.cont_diff_within_at

lemma cont_diff_top : cont_diff 𝕜 ∞ f ↔ ∀ (n : ℕ), cont_diff 𝕜 n f :=
by simp [cont_diff_on_univ.symm, cont_diff_on_top]

lemma cont_diff_all_iff_nat : (∀ n, cont_diff 𝕜 n f) ↔ (∀ n : ℕ, cont_diff 𝕜 n f) :=
by simp only [← cont_diff_on_univ, cont_diff_on_all_iff_nat]

lemma cont_diff.cont_diff_on (h : cont_diff 𝕜 n f) : cont_diff_on 𝕜 n f s :=
(cont_diff_on_univ.2 h).mono (subset_univ _)

@[simp] lemma cont_diff_zero : cont_diff 𝕜 0 f ↔ continuous f :=
begin
  rw [← cont_diff_on_univ, continuous_iff_continuous_on_univ],
  exact cont_diff_on_zero
end

lemma cont_diff_at_zero : cont_diff_at 𝕜 0 f x ↔ ∃ u ∈ 𝓝 x, continuous_on f u :=
by { rw ← cont_diff_within_at_univ, simp [cont_diff_within_at_zero, nhds_within_univ] }

theorem cont_diff_at_one_iff : cont_diff_at 𝕜 1 f x ↔
  ∃ f' : E → (E →L[𝕜] F), ∃ u ∈ 𝓝 x, continuous_on f' u ∧ ∀ x ∈ u, has_fderiv_at f (f' x) x :=
by simp_rw [show (1 : ℕ∞) = (0 + 1 : ℕ), from (zero_add 1).symm,
  cont_diff_at_succ_iff_has_fderiv_at, show ((0 : ℕ) : ℕ∞) = 0, from rfl,
  cont_diff_at_zero, exists_mem_and_iff antitone_bforall antitone_continuous_on, and_comm]

lemma cont_diff.of_le (h : cont_diff 𝕜 n f) (hmn : m ≤ n) : cont_diff 𝕜 m f :=
cont_diff_on_univ.1 $ (cont_diff_on_univ.2 h).of_le hmn

lemma cont_diff.of_succ {n : ℕ} (h : cont_diff 𝕜 (n + 1) f) : cont_diff 𝕜 n f :=
h.of_le $ with_top.coe_le_coe.mpr le_self_add

lemma cont_diff.one_of_succ {n : ℕ} (h : cont_diff 𝕜 (n + 1) f) : cont_diff 𝕜 1 f :=
h.of_le $ with_top.coe_le_coe.mpr le_add_self

lemma cont_diff.continuous (h : cont_diff 𝕜 n f) : continuous f :=
cont_diff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
lemma cont_diff.differentiable (h : cont_diff 𝕜 n f) (hn : 1 ≤ n) : differentiable 𝕜 f :=
differentiable_on_univ.1 $ (cont_diff_on_univ.2 h).differentiable_on hn

lemma cont_diff_iff_forall_nat_le :
  cont_diff 𝕜 n f ↔ ∀ m : ℕ, ↑m ≤ n → cont_diff 𝕜 m f :=
by { simp_rw [← cont_diff_on_univ], exact cont_diff_on_iff_forall_nat_le }

/-! ### Iterated derivative -/

variable (𝕜)

/-- The `n`-th derivative of a function, as a multilinear map, defined inductively. -/
noncomputable def iterated_fderiv (n : ℕ) (f : E → F) :
  E → (E [×n]→L[𝕜] F) :=
nat.rec_on n
  (λ x, continuous_multilinear_map.curry0 𝕜 E (f x))
  (λ n rec x, continuous_linear_map.uncurry_left (fderiv 𝕜 rec x))

/-- Formal Taylor series associated to a function within a set. -/
def ftaylor_series (f : E → F) (x : E) : formal_multilinear_series 𝕜 E F :=
λ n, iterated_fderiv 𝕜 n f x

variable {𝕜}

@[simp] lemma iterated_fderiv_zero_apply (m : (fin 0) → E) :
  (iterated_fderiv 𝕜 0 f x : ((fin 0) →  E) → F) m = f x := rfl

lemma iterated_fderiv_zero_eq_comp :
  iterated_fderiv 𝕜 0 f = (continuous_multilinear_curry_fin0 𝕜 E F).symm ∘ f := rfl

@[simp] lemma norm_iterated_fderiv_zero :
  ‖iterated_fderiv 𝕜 0 f x‖ = ‖f x‖ :=
by rw [iterated_fderiv_zero_eq_comp, linear_isometry_equiv.norm_map]

lemma iterated_fderiv_with_zero_eq :
  iterated_fderiv_within 𝕜 0 f s = iterated_fderiv 𝕜 0 f :=
by { ext, refl }

lemma iterated_fderiv_succ_apply_left {n : ℕ} (m : fin (n + 1) → E):
  (iterated_fderiv 𝕜 (n + 1) f x : (fin (n + 1) → E) → F) m
  = (fderiv 𝕜 (iterated_fderiv 𝕜 n f) x : E → (E [×n]→L[𝕜] F)) (m 0) (tail m) := rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
lemma iterated_fderiv_succ_eq_comp_left {n : ℕ} :
  iterated_fderiv 𝕜 (n + 1) f =
  (continuous_multilinear_curry_left_equiv 𝕜 (λ (i : fin (n + 1)), E) F)
    ∘ (fderiv 𝕜 (iterated_fderiv 𝕜 n f)) := rfl

/-- Writing explicitly the derivative of the `n`-th derivative as the composition of a currying
linear equiv, and the `n + 1`-th derivative. -/
lemma fderiv_iterated_fderiv {n : ℕ} :
  fderiv 𝕜 (iterated_fderiv 𝕜 n f) =
  (continuous_multilinear_curry_left_equiv 𝕜 (λ (i : fin (n + 1)), E) F).symm
    ∘ (iterated_fderiv 𝕜 (n + 1) f) :=
begin
  rw iterated_fderiv_succ_eq_comp_left,
  ext1 x,
  simp only [function.comp_app, linear_isometry_equiv.symm_apply_apply],
end

lemma has_compact_support.iterated_fderiv (hf : has_compact_support f) (n : ℕ) :
  has_compact_support (iterated_fderiv 𝕜 n f) :=
begin
  induction n with n IH,
  { rw [iterated_fderiv_zero_eq_comp],
    apply hf.comp_left,
    exact linear_isometry_equiv.map_zero _ },
  { rw iterated_fderiv_succ_eq_comp_left,
    apply (IH.fderiv 𝕜).comp_left,
    exact linear_isometry_equiv.map_zero _ }
end
lemma norm_fderiv_iterated_fderiv {n : ℕ} :
  ‖fderiv 𝕜 (iterated_fderiv 𝕜 n f) x‖ = ‖iterated_fderiv 𝕜 (n + 1) f x‖ :=
by rw [iterated_fderiv_succ_eq_comp_left, linear_isometry_equiv.norm_map]

lemma iterated_fderiv_within_univ {n : ℕ} :
  iterated_fderiv_within 𝕜 n f univ = iterated_fderiv 𝕜 n f :=
begin
  induction n with n IH,
  { ext x, simp },
  { ext x m,
    rw [iterated_fderiv_succ_apply_left, iterated_fderiv_within_succ_apply_left, IH,
        fderiv_within_univ] }
end

/-- In an open set, the iterated derivative within this set coincides with the global iterated
derivative. -/
lemma iterated_fderiv_within_of_is_open (n : ℕ) (hs : is_open s) :
  eq_on (iterated_fderiv_within 𝕜 n f s) (iterated_fderiv 𝕜 n f) s :=
begin
  induction n with n IH,
  { assume x hx,
    ext1 m,
    simp only [iterated_fderiv_within_zero_apply, iterated_fderiv_zero_apply] },
  { assume x hx,
    rw [iterated_fderiv_succ_eq_comp_left, iterated_fderiv_within_succ_eq_comp_left],
    dsimp,
    congr' 1,
    rw fderiv_within_of_open hs hx,
    apply filter.eventually_eq.fderiv_eq,
    filter_upwards [hs.mem_nhds hx],
    exact IH }
end

lemma ftaylor_series_within_univ :
  ftaylor_series_within 𝕜 f univ = ftaylor_series 𝕜 f :=
begin
  ext1 x, ext1 n,
  change iterated_fderiv_within 𝕜 n f univ x = iterated_fderiv 𝕜 n f x,
  rw iterated_fderiv_within_univ
end

theorem iterated_fderiv_succ_apply_right {n : ℕ} (m : fin (n + 1) → E) :
  (iterated_fderiv 𝕜 (n + 1) f x : (fin (n + 1) → E) → F) m
    = iterated_fderiv 𝕜 n (λy, fderiv 𝕜 f y) x (init m) (m (last n)) :=
begin
  rw [← iterated_fderiv_within_univ, ← iterated_fderiv_within_univ, ← fderiv_within_univ],
  exact iterated_fderiv_within_succ_apply_right unique_diff_on_univ (mem_univ _) _
end

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the `n`-th derivative of the derivative. -/
lemma iterated_fderiv_succ_eq_comp_right {n : ℕ} :
  iterated_fderiv 𝕜 (n + 1) f x =
  ((continuous_multilinear_curry_right_equiv' 𝕜 n E F)
    ∘ (iterated_fderiv 𝕜 n (λy, fderiv 𝕜 f y))) x :=
by { ext m, rw iterated_fderiv_succ_apply_right, refl }

lemma norm_iterated_fderiv_fderiv {n : ℕ} :
  ‖iterated_fderiv 𝕜 n (fderiv 𝕜 f) x‖ = ‖iterated_fderiv 𝕜 (n + 1) f x‖ :=
by rw [iterated_fderiv_succ_eq_comp_right, linear_isometry_equiv.norm_map]

@[simp] lemma iterated_fderiv_one_apply (m : (fin 1) → E) :
  (iterated_fderiv 𝕜 1 f x : ((fin 1) → E) → F) m
  = (fderiv 𝕜 f x : E → F) (m 0) :=
by { rw [iterated_fderiv_succ_apply_right, iterated_fderiv_zero_apply], refl }

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem cont_diff_iff_ftaylor_series :
  cont_diff 𝕜 n f ↔ has_ftaylor_series_up_to n f (ftaylor_series 𝕜 f) :=
begin
  split,
  { rw [← cont_diff_on_univ, ← has_ftaylor_series_up_to_on_univ_iff,
        ← ftaylor_series_within_univ],
    exact λ h, cont_diff_on.ftaylor_series_within h unique_diff_on_univ },
  { assume h, exact ⟨ftaylor_series 𝕜 f, h⟩ }
end

lemma cont_diff_iff_continuous_differentiable :
  cont_diff 𝕜 n f ↔
  (∀ (m : ℕ), (m : ℕ∞) ≤ n → continuous (λ x, iterated_fderiv 𝕜 m f x))
  ∧ (∀ (m : ℕ), (m : ℕ∞) < n → differentiable 𝕜 (λ x, iterated_fderiv 𝕜 m f x)) :=
by simp [cont_diff_on_univ.symm, continuous_iff_continuous_on_univ,
    differentiable_on_univ.symm, iterated_fderiv_within_univ,
    cont_diff_on_iff_continuous_on_differentiable_on unique_diff_on_univ]

/-- If `f` is `C^n` then its `m`-times iterated derivative is continuous for `m ≤ n`. -/
lemma cont_diff.continuous_iterated_fderiv {m : ℕ} (hm : (m : ℕ∞) ≤ n)
  (hf : cont_diff 𝕜 n f) : continuous (λ x, iterated_fderiv 𝕜 m f x) :=
(cont_diff_iff_continuous_differentiable.mp hf).1 m hm

/-- If `f` is `C^n` then its `m`-times iterated derivative is differentiable for `m < n`. -/
lemma cont_diff.differentiable_iterated_fderiv {m : ℕ} (hm : (m : ℕ∞) < n)
  (hf : cont_diff 𝕜 n f) : differentiable 𝕜 (λ x, iterated_fderiv 𝕜 m f x) :=
(cont_diff_iff_continuous_differentiable.mp hf).2 m hm

lemma cont_diff_of_differentiable_iterated_fderiv
  (h : ∀(m : ℕ), (m : ℕ∞) ≤ n → differentiable 𝕜 (iterated_fderiv 𝕜 m f)) :
  cont_diff 𝕜 n f :=
cont_diff_iff_continuous_differentiable.2
⟨λ m hm, (h m hm).continuous, λ m hm, (h m (le_of_lt hm))⟩

/-- A function is `C^(n + 1)` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^n`. -/
theorem cont_diff_succ_iff_fderiv {n : ℕ} :
  cont_diff 𝕜 ((n + 1) : ℕ) f ↔
  differentiable 𝕜 f ∧ cont_diff 𝕜 n (λ y, fderiv 𝕜 f y) :=
by simp only [← cont_diff_on_univ, ← differentiable_on_univ, ← fderiv_within_univ,
  cont_diff_on_succ_iff_fderiv_within unique_diff_on_univ]

theorem cont_diff_one_iff_fderiv :
  cont_diff 𝕜 1 f ↔ differentiable 𝕜 f ∧ continuous (fderiv 𝕜 f) :=
cont_diff_succ_iff_fderiv.trans $ iff.rfl.and cont_diff_zero

/-- A function is `C^∞` if and only if it is differentiable,
and its derivative (formulated in terms of `fderiv`) is `C^∞`. -/
theorem cont_diff_top_iff_fderiv :
  cont_diff 𝕜 ∞ f ↔
  differentiable 𝕜 f ∧ cont_diff 𝕜 ∞ (λ y, fderiv 𝕜 f y) :=
begin
  simp only [← cont_diff_on_univ, ← differentiable_on_univ, ← fderiv_within_univ],
  rw cont_diff_on_top_iff_fderiv_within unique_diff_on_univ,
end

lemma cont_diff.continuous_fderiv
  (h : cont_diff 𝕜 n f) (hn : 1 ≤ n) :
  continuous (λ x, fderiv 𝕜 f x) :=
((cont_diff_succ_iff_fderiv).1 (h.of_le hn)).2.continuous

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
lemma cont_diff.continuous_fderiv_apply
  (h : cont_diff 𝕜 n f) (hn : 1 ≤ n) :
  continuous (λp : E × E, (fderiv 𝕜 f p.1 : E → F) p.2) :=
have A : continuous (λq : (E →L[𝕜] F) × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
have B : continuous (λp : E × E, (fderiv 𝕜 f p.1, p.2)) :=
  ((h.continuous_fderiv hn).comp continuous_fst).prod_mk continuous_snd,
A.comp B
