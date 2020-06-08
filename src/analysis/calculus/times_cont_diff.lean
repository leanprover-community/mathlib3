/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import analysis.calculus.fderiv

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
as well as predicates `times_cont_diff 𝕜 n f` and `times_cont_diff_on 𝕜 n f s` saying that the
function is `C^n`, respectively in the whole space or on the set `s`.

To avoid the issue of choice when choosing a derivative in sets where the derivative is not
necessarily unique, `times_cont_diff_on` is not defined directly in terms of the
regularity of the specific choice `iterated_fderiv_within 𝕜 n f s` inside `s`, but in terms of the
existence of a nice sequence of derivatives, expressed with a predicate
`has_ftaylor_series_up_to_on`.

We prove basic properties of these notions.

## Main definitions and results
Let `f : E → F` be a map between normed vector spaces over a nondiscrete normed field `𝕜`.

* `formal_multilinear_series 𝕜 E F`: a family of `n`-multilinear maps for all `n`, designed to
  model the sequence of derivatives of a function.
* `has_ftaylor_series_up_to n f p`: expresses that the formal multilinear series `p` is a sequence
  of iterated derivatives of `f`, up to the `n`-th term (where `n` is a natural number or `∞`).
* `has_ftaylor_series_up_to_on n f p s`: same thing, but inside a set `s`. The notion of derivative
  is now taken inside `s`. In particular, derivatives don't have to be unique.
* `times_cont_diff 𝕜 n f`: expresses that `f` is `C^n`, i.e., it admits a Taylor series up to
  rank `n`.
* `times_cont_diff_on 𝕜 n f s`: expresses that `f` is `C^n` in `s`.
* `iterated_fderiv_within 𝕜 n f s x` is an `n`-th derivative of `f` over the field `𝕜` on the
  set `s` at the point `x`. It is a continuous multilinear map from `E^n` to `F`, defined as a
  derivative within `s` of `iterated_fderiv_within 𝕜 (n-1) f s` if one exists, and `0` otherwise.
* `iterated_fderiv 𝕜 n f x` is the `n`-th derivative of `f` over the field `𝕜` at the point `x`.
  It is a continuous multilinear map from `E^n` to `F`, defined as a derivative of
  `iterated_fderiv 𝕜 (n-1) f` if one exists, and `0` otherwise.

In sets of unique differentiability, `times_cont_diff_on 𝕜 n f s` can be expressed in terms of the
properties of `iterated_fderiv_within 𝕜 m f s` for `m ≤ n`. In the whole space,
`times_cont_diff 𝕜 n f` can be expressed in terms of the properties of `iterated_fderiv 𝕜 m f`
for `m ≤ n`.

We also prove that the usual operations (addition, multiplication, difference, composition, and
so on) preserve `C^n` functions.

## Implementation notes

### Definition of `C^n` functions in domains

One could define `C^n` functions in a domain `s` by fixing an arbitrary choice of derivatives (this
is what we do with `iterated_fderiv_within`) and requiring that all these derivatives up to `n` are
continuous. If the derivative is not unique, this could lead to strange behavior like two `C^n`
functions `f` and `g` on `s` whose sum is not `C^n`. A better definition is thus to say that a
function is `C^n` inside `s` if it admits a sequence of derivatives up to `n` inside `s`. This
definition still has the problem that a function which is locally `C^n` would not need to be `C^n`,
as different choices of sequences of derivatives around different points might possibly not be glued
together to give a globally defined sequence of derivatives. Also, there are locality problems in
time: one could image a function which, for each `n`, has a nice sequence of derivatives up to order
`n`, but they do not coincide for varying `n` and can therefore not be glued to give rise to an
infinite sequence of derivatives. This would give a function which is `C^n` for all `n`, but not
`C^∞`. We solve this issue by putting locality conditions in space and time in our definition of
`times_cont_diff_on`. The resulting definition is slightly more complicated to work with (in fact
not so much), but it gives rise to completely satisfactory theorems.

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

## Tags

derivative, differentiability, higher derivative, `C^n`, multilinear, Taylor series, formal series
-/

noncomputable theory
open_locale classical

universes u v w

local attribute [instance, priority 1001]
normed_group.to_add_comm_group normed_space.to_semimodule add_comm_group.to_add_comm_monoid

open set fin
open_locale topological_space

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [normed_group G] [normed_space 𝕜 G]
{s s₁ t u : set E} {f f₁ : E → F} {g : F → G} {x : E} {c : F}
{b : E × F → G}


/-- A formal multilinear series over a field `𝕜`, from `E` to `F`, is given by a family of
multilinear maps from `E^n` to `F` for all `n`. -/
@[derive add_comm_group]
def formal_multilinear_series
  (𝕜 : Type*) [nondiscrete_normed_field 𝕜]
  (E : Type*) [normed_group E] [normed_space 𝕜 E]
  (F : Type*) [normed_group F] [normed_space 𝕜 F] :=
Π (n : ℕ), (E [×n]→L[𝕜] F)

instance : inhabited (formal_multilinear_series 𝕜 E F) := ⟨0⟩

section module
/- `derive` is not able to find the module structure, probably because Lean is confused by the
dependent types. We register it explicitly. -/
local attribute [reducible] formal_multilinear_series

instance : module 𝕜 (formal_multilinear_series 𝕜 E F) :=
begin
  letI : ∀ n, module 𝕜 (continuous_multilinear_map 𝕜 (λ (i : fin n), E) F) :=
    λ n, by apply_instance,
  apply_instance
end

end module

namespace formal_multilinear_series

variables (p : formal_multilinear_series 𝕜 E F)

/-- Forgetting the zeroth term in a formal multilinear series, and interpreting the following terms
as multilinear maps into `E →L[𝕜] F`. If `p` corresponds to the Taylor series of a function, then
`p.shift` is the Taylor series of the derivative of the function. -/
def shift : formal_multilinear_series 𝕜 E (E →L[𝕜] F) :=
λn, (p n.succ).curry_right

/-- Adding a zeroth term to a formal multilinear series taking values in `E →L[𝕜] F`. This
corresponds to starting from a Taylor series for the derivative of a function, and building a Taylor
series for the function itself. -/
def unshift (q : formal_multilinear_series 𝕜 E (E →L[𝕜] F)) (z : F) :
  formal_multilinear_series 𝕜 E F
| 0       := (continuous_multilinear_curry_fin0 𝕜 E F).symm z
| (n + 1) := (continuous_multilinear_curry_right_equiv 𝕜 (λ (i : fin (n + 1)), E) F) (q n)

/-- Convenience congruence lemma stating in a dependent setting that, if the arguments to a formal
multilinear series are equal, then the values are also equal. -/
lemma congr (p : formal_multilinear_series 𝕜 E F) {m n : ℕ} {v : fin m → E} {w : fin n → E}
  (h1 : m = n) (h2 : ∀ (i : ℕ) (him : i < m) (hin : i < n), v ⟨i, him⟩ = w ⟨i, hin⟩) :
  p m v = p n w :=
by { cases h1, congr, funext i, cases i with i hi, exact h2 i hi hi }

end formal_multilinear_series

variable {p : E → formal_multilinear_series 𝕜 E F}

/-- `has_ftaylor_series_up_to_on n f p s` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_within_at` but for higher order derivatives. -/
structure has_ftaylor_series_up_to_on (n : with_top ℕ)
  (f : E → F) (p : E → formal_multilinear_series 𝕜 E F) (s : set E) : Prop :=
(zero_eq       : ∀ x ∈ s, (p x 0).uncurry0 = f x)
(fderiv_within : ∀ (m : ℕ) (hm : (m : with_top ℕ) < n), ∀ x ∈ s,
   has_fderiv_within_at (λ y, p y m) (p x m.succ).curry_left s x)
(cont          : ∀ (m : ℕ) (hm : (m : with_top ℕ) ≤ n), continuous_on (λ x, p x m) s)

lemma has_ftaylor_series_up_to_on.zero_eq' {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) {x : E} (hx : x ∈ s) :
  p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x) :=
by { rw ← h.zero_eq x hx, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ }

/-- If two functions coincide on a set `s`, then a Taylor series for the first one is as well a
Taylor series for the second one. -/
lemma has_ftaylor_series_up_to_on.congr {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
  has_ftaylor_series_up_to_on n f₁ p s :=
begin
  refine ⟨λ x hx, _, h.fderiv_within, h.cont⟩,
  rw h₁ x hx,
  exact h.zero_eq x hx
end

lemma has_ftaylor_series_up_to_on.mono {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) {t : set E} (hst : t ⊆ s) :
  has_ftaylor_series_up_to_on n f p t :=
⟨λ x hx, h.zero_eq x (hst hx),
λ m hm x hx, (h.fderiv_within m hm x (hst hx)).mono hst,
λ m hm, (h.cont m hm).mono hst⟩

lemma has_ftaylor_series_up_to_on.of_le {m n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) (hmn : m ≤ n) :
  has_ftaylor_series_up_to_on m f p s :=
⟨h.zero_eq,
λ k hk x hx, h.fderiv_within k (lt_of_lt_of_le hk hmn) x hx,
λ k hk, h.cont k (le_trans hk hmn)⟩

lemma has_ftaylor_series_up_to_on.continuous_on {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) : continuous_on f s :=
begin
  have := (h.cont 0 bot_le).congr (λ x hx, (h.zero_eq' hx).symm),
  rwa continuous_linear_equiv.comp_continuous_on_iff at this
end

lemma has_ftaylor_series_up_to_on_zero_iff :
  has_ftaylor_series_up_to_on 0 f p s ↔ continuous_on f s ∧ (∀ x ∈ s, (p x 0).uncurry0 = f x) :=
begin
  refine ⟨λ H, ⟨H.continuous_on, H.zero_eq⟩,
          λ H, ⟨H.2, λ m hm, false.elim (not_le.2 hm bot_le), _⟩⟩,
  assume m hm,
  have : (m : with_top ℕ) = ((0 : ℕ) : with_bot ℕ) := le_antisymm hm bot_le,
  rw with_top.coe_eq_coe at this,
  rw this,
  have : ∀ x ∈ s, p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x),
    by { assume x hx, rw ← H.2 x hx, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ },
  rw [continuous_on_congr this, continuous_linear_equiv.comp_continuous_on_iff],
  exact H.1
end

lemma has_ftaylor_series_up_to_on_top_iff :
  (has_ftaylor_series_up_to_on ⊤ f p s) ↔ (∀ (n : ℕ), has_ftaylor_series_up_to_on n f p s) :=
begin
  split,
  { assume H n, exact H.of_le le_top },
  { assume H,
    split,
    { exact (H 0).zero_eq },
    { assume m hm,
      apply (H m.succ).fderiv_within m (with_top.coe_lt_coe.2 (lt_add_one m)) },
    { assume m hm,
      apply (H m).cont m (le_refl _) } }
end

/-- If a function has a Taylor series at order at least `1`, then the term of order `1` of this
series is a derivative of `f`. -/
lemma has_ftaylor_series_up_to_on.has_fderiv_within_at {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) (hx : x ∈ s) :
  has_fderiv_within_at f (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) s x :=
begin
  have A : ∀ y ∈ s, f y = (continuous_multilinear_curry_fin0 𝕜 E F) (p y 0),
  { assume y hy, rw ← h.zero_eq y hy, refl },
  suffices H : has_fderiv_within_at
      (λ y, continuous_multilinear_curry_fin0 𝕜 E F (p y 0))
      (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) s x,
    by exact H.congr A (A x hx),
  rw continuous_linear_equiv.comp_has_fderiv_within_at_iff',
  have : ((0 : ℕ) : with_top ℕ) < n :=
    lt_of_lt_of_le (with_top.coe_lt_coe.2 zero_lt_one) hn,
  convert h.fderiv_within _ this x hx,
  ext y v,
  change (p x 1) (snoc 0 y) = (p x 1) (cons y v),
  unfold_coes,
  congr,
  ext i,
  have : i = 0 := subsingleton.elim i 0,
  rw this,
  refl
end

lemma has_ftaylor_series_up_to_on.differentiable_on {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s) (hn : 1 ≤ n) : differentiable_on 𝕜 f s :=
λ x hx, (h.has_fderiv_within_at hn hx).differentiable_within_at

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
           h.cont (n + 1) (le_refl _)⟩ },
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
    { assume m (hm : (m : with_top ℕ) < n) x (hx : x ∈ s),
      have A : (m.succ : with_top ℕ) < n.succ,
        by { rw with_top.coe_lt_coe at ⊢ hm, exact nat.lt_succ_iff.mpr hm },
      change has_fderiv_within_at
        ((continuous_multilinear_curry_right_equiv 𝕜 (λ i : fin m.succ, E) F).symm
           ∘ (λ (y : E), p y m.succ))
        (p x m.succ.succ).curry_right.curry_left s x,
      rw continuous_linear_equiv.comp_has_fderiv_within_at_iff',
      convert H.fderiv_within _ A x hx,
      ext y v,
      change (p x m.succ.succ) (snoc (cons y (init v)) (v (last _)))
        = (p x (nat.succ (nat.succ m))) (cons y v),
      rw [← cons_snoc_eq_snoc_cons, snoc_init_self] },
    { assume m (hm : (m : with_top ℕ) ≤ n),
      have A : (m.succ : with_top ℕ) ≤ n.succ,
        by { rw with_top.coe_le_coe at ⊢ hm, exact nat.pred_le_iff.mp hm },
      change continuous_on ((continuous_multilinear_curry_right_equiv 𝕜 (λ i : fin m.succ, E) F).symm
           ∘ (λ (y : E), p y m.succ)) s,
      rw continuous_linear_equiv.comp_continuous_on_iff,
      exact H.cont _ A } },
  { rintros ⟨Hzero_eq, Hfderiv_zero, Htaylor⟩,
    split,
    { exact Hzero_eq },
    { assume m (hm : (m : with_top ℕ) < n.succ) x (hx : x ∈ s),
      cases m,
      { exact Hfderiv_zero x hx },
      { have A : (m : with_top ℕ) < n,
          by { rw with_top.coe_lt_coe at hm ⊢, exact nat.lt_of_succ_lt_succ hm },
        have : has_fderiv_within_at ((continuous_multilinear_curry_right_equiv 𝕜 (λ i : fin m.succ, E) F).symm
           ∘ (λ (y : E), p y m.succ)) ((p x).shift m.succ).curry_left s x :=
        Htaylor.fderiv_within _ A x hx,
        rw continuous_linear_equiv.comp_has_fderiv_within_at_iff' at this,
        convert this,
        ext y v,
        change (p x (nat.succ (nat.succ m))) (cons y v)
          = (p x m.succ.succ) (snoc (cons y (init v)) (v (last _))),
        rw [← cons_snoc_eq_snoc_cons, snoc_init_self] } },
    { assume m (hm : (m : with_top ℕ) ≤ n.succ),
      cases m,
      { have : differentiable_on 𝕜 (λ x, p x 0) s :=
          λ x hx, (Hfderiv_zero x hx).differentiable_within_at,
        exact this.continuous_on },
      { have A : (m : with_top ℕ) ≤ n,
          by { rw with_top.coe_le_coe at hm ⊢, exact nat.lt_succ_iff.mp hm },
        have : continuous_on ((continuous_multilinear_curry_right_equiv 𝕜 (λ i : fin m.succ, E) F).symm
           ∘ (λ (y : E), p y m.succ)) s :=
        Htaylor.cont _ A,
        rwa continuous_linear_equiv.comp_continuous_on_iff at this } } }
end

variable (𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives within `s` up to
order `n`, which are continuous. There is a subtlety on sets where derivatives are not unique, that
choices of derivatives around different points might not match. To ensure that being `C^n` is a
local property, we therefore require it locally around each point. There is another subtlety that
one might be able to find nice derivatives up to `n` for any finite `n`, but that they don't match
so that one can not find them up to infinity. To get a good notion for `n = ∞`, we only require that
for any finite `n` we may find such matching derivatives.
-/
definition times_cont_diff_on (n : with_top ℕ) (f : E → F) (s : set E) :=
∀ (m : ℕ), (m : with_top ℕ) ≤ n →
∀ x ∈ s, ∃ u ∈ nhds_within x s, ∃ p : E → formal_multilinear_series 𝕜 E F,
  has_ftaylor_series_up_to_on m f p u

variable {𝕜}

lemma times_cont_diff_on_nat {n : ℕ} :
  times_cont_diff_on 𝕜 n f s ↔
  ∀ x ∈ s, ∃ u ∈ nhds_within x s, ∃ p : E → formal_multilinear_series 𝕜 E F,
  has_ftaylor_series_up_to_on n f p u :=
begin
  refine ⟨λ H, H n (le_refl _), λ H m hm x hx, _⟩,
  rcases H x hx with ⟨u, hu, p, hp⟩,
  exact ⟨u, hu, p, hp.of_le hm⟩
end

lemma times_cont_diff_on_top :
  times_cont_diff_on 𝕜 ⊤ f s ↔ ∀ (n : ℕ), times_cont_diff_on 𝕜 n f s :=
begin
  split,
  { assume H n m hm x hx,
    rcases H m le_top x hx with ⟨u, hu, p, hp⟩,
    exact ⟨u, hu, p, hp⟩ },
  { assume H m hm x hx,
    rcases H m m (le_refl _) x hx with ⟨u, hu, p, hp⟩,
    exact ⟨u, hu, p, hp⟩ }
end

lemma times_cont_diff_on.continuous_on {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) : continuous_on f s :=
begin
  apply continuous_on_of_locally_continuous_on (λ x hx, _),
  rcases h 0 bot_le x hx with ⟨u, hu, p, H⟩,
  rcases mem_nhds_within.1 hu with ⟨t, t_open, xt, tu⟩,
  refine ⟨t, t_open, xt, _⟩,
  rw inter_comm at tu,
  exact (H.mono tu).continuous_on
end

lemma times_cont_diff_on.congr {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (h₁ : ∀ x ∈ s, f₁ x = f x) :
  times_cont_diff_on 𝕜 n f₁ s :=
begin
  assume m hm x hx,
  rcases h m hm x hx with ⟨u, hu, p, H⟩,
  refine ⟨u ∩ s, filter.inter_mem_sets hu self_mem_nhds_within, p, _⟩,
  exact (H.mono (inter_subset_left u s)).congr (λ x hx, h₁ x hx.2)
end

lemma times_cont_diff_on_congr {n : with_top ℕ} (h₁ : ∀ x ∈ s, f₁ x = f x) :
  times_cont_diff_on 𝕜 n f₁ s ↔ times_cont_diff_on 𝕜 n f s :=
⟨λ H, H.congr (λ x hx, (h₁ x hx).symm), λ H, H.congr h₁⟩

lemma times_cont_diff_on.mono {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) {t : set E} (hst : t ⊆ s) :
  times_cont_diff_on 𝕜 n f t :=
begin
  assume m hm x hx,
  rcases h m hm x (hst hx) with ⟨u, hu, p, H⟩,
  exact ⟨u, nhds_within_mono x hst hu, p, H⟩
end

lemma times_cont_diff_on.congr_mono {n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (h₁ : ∀ x ∈ s₁, f₁ x = f x) (hs : s₁ ⊆ s) :
  times_cont_diff_on 𝕜 n f₁ s₁ :=
(hf.mono hs).congr h₁

lemma times_cont_diff_on.of_le {m n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hmn : m ≤ n) :
  times_cont_diff_on 𝕜 m f s :=
begin
  assume k hk x hx,
  rcases h k (le_trans hk hmn) x hx with ⟨u, hu, p, H⟩,
  exact ⟨u, hu, p, H⟩
end

/-- If a function is `C^n` on a set with `n ≥ 1`, then it is differentiable there. -/
lemma times_cont_diff_on.differentiable_on {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hn : 1 ≤ n) : differentiable_on 𝕜 f s :=
begin
  apply differentiable_on_of_locally_differentiable_on (λ x hx, _),
  rcases h 1 hn x hx with ⟨u, hu, p, H⟩,
  rcases mem_nhds_within.1 hu with ⟨t, t_open, xt, tu⟩,
  rw inter_comm at tu,
  exact ⟨t, t_open, xt, (H.mono tu).differentiable_on (le_refl _)⟩
end

/-- If a function is `C^n` around each point in a set, then it is `C^n` on the set. -/
lemma times_cont_diff_on_of_locally_times_cont_diff_on {n : with_top ℕ}
  (h : ∀ x ∈ s, ∃u, is_open u ∧ x ∈ u ∧ times_cont_diff_on 𝕜 n f (s ∩ u)) :
  times_cont_diff_on 𝕜 n f s :=
begin
  assume m hm x hx,
  rcases h x hx with ⟨u, u_open, xu, Hu⟩,
  rcases Hu m hm x ⟨hx, xu⟩ with ⟨v, hv, p, H⟩,
  rw ← nhds_within_restrict s xu u_open at hv,
  exact ⟨v, hv, p, H⟩,
end

/-- A function is `C^(n + 1)` on a domain iff locally, it has a derivative which is `C^n`. -/
theorem times_cont_diff_on_succ_iff_has_fderiv_within_at {n : ℕ} :
  times_cont_diff_on 𝕜 ((n + 1) : ℕ) f s
  ↔ ∀ x ∈ s, ∃ u ∈ nhds_within x s, ∃ f' : E → (E →L[𝕜] F),
    (∀ x ∈ u, has_fderiv_within_at f (f' x) u x)
    ∧ (times_cont_diff_on 𝕜 n f' u) :=
begin
  split,
  { assume h x hx,
    rcases h n.succ (le_refl _) x hx with ⟨u, hu, p, Hp⟩,
    refine ⟨u, hu, λ y, (continuous_multilinear_curry_fin1 𝕜 E F) (p y 1),
      λ y hy, Hp.has_fderiv_within_at (with_top.coe_le_coe.2 (nat.le_add_left 1 n)) hy, _⟩,
    rw has_ftaylor_series_up_to_on_succ_iff_right at Hp,
    assume m hm z hz,
    exact ⟨u, self_mem_nhds_within, λ (x : E), (p x).shift, Hp.2.2.of_le hm⟩ },
  { assume h,
    rw times_cont_diff_on_nat,
    assume x hx,
    rcases h x hx with ⟨u, hu, f', f'_eq_deriv, Hf'⟩,
    have xu : x ∈ u := mem_of_mem_nhds_within hx hu,
    rcases Hf' n (le_refl _) x xu with ⟨v, hv, p', Hp'⟩,
    refine ⟨v ∩ u, filter.inter_mem_sets (nhds_within_le_of_mem hu hv) hu,
            λ x, (p' x).unshift (f x), _⟩,
    rw has_ftaylor_series_up_to_on_succ_iff_right,
    refine ⟨λ y hy, rfl, λ y hy, _, _⟩,
    { change has_fderiv_within_at (λ (z : E), (continuous_multilinear_curry_fin0 𝕜 E F).symm (f z))
        ((formal_multilinear_series.unshift (p' y) (f y) 1).curry_left) (v ∩ u) y,
      rw continuous_linear_equiv.comp_has_fderiv_within_at_iff',
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
        rw [snoc_last, init_snoc] } } }
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

lemma iterated_fderiv_within_succ_apply_left {n : ℕ} (m : fin (n + 1) → E):
  (iterated_fderiv_within 𝕜 (n + 1) f s x : (fin (n + 1) → E) → F) m
  = (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s x : E → (E [×n]→L[𝕜] F)) (m 0) (tail m) := rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
lemma iterated_fderiv_within_succ_eq_comp_left {n : ℕ} :
  iterated_fderiv_within 𝕜 (n + 1) f s =
  (continuous_multilinear_curry_left_equiv 𝕜 (λ(i : fin (n + 1)), E) F)
    ∘ (fderiv_within 𝕜 (iterated_fderiv_within 𝕜 n f s) s) := rfl

theorem iterated_fderiv_within_succ_apply_right {n : ℕ}
  (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) (m : fin (n + 1) → E) :
  (iterated_fderiv_within 𝕜 (n + 1) f s x : (fin (n + 1) → E) → F) m
    = iterated_fderiv_within 𝕜 n (λy, fderiv_within 𝕜 f s y) s x (init m) (m (last n)) :=
begin
  induction n with n IH generalizing x,
  { rw [iterated_fderiv_within_succ_eq_comp_left, iterated_fderiv_within_zero_eq_comp,
        iterated_fderiv_within_zero_apply,
        function.comp_apply, continuous_linear_equiv.comp_fderiv_within _ (hs x hx)],
    refl },
  { let I := (continuous_multilinear_curry_right_equiv 𝕜 (λ (i : fin (n + 1)), E) F),
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
      by { rw continuous_linear_equiv.comp_fderiv_within _ (hs x hx), refl }
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
  ((continuous_multilinear_curry_right_equiv 𝕜 (λ(i : fin (n + 1)), E) F)
    ∘ (iterated_fderiv_within 𝕜 n (λy, fderiv_within 𝕜 f s y) s)) x :=
by { ext m, rw iterated_fderiv_within_succ_apply_right hs hx, refl }

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
      fderiv_within_inter (mem_nhds_sets hu hx.2)
        ((unique_diff_within_at_inter (mem_nhds_sets hu hx.2)).1 (hs x hx)),
    ext m,
    rw [iterated_fderiv_within_succ_apply_left, iterated_fderiv_within_succ_apply_left, A, B] }
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x` within `s`. -/
lemma iterated_fderiv_within_inter' {n : ℕ}
  (hu : u ∈ nhds_within x s) (hs : unique_diff_on 𝕜 s) (xs : x ∈ s) :
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
  { refine iterated_fderiv_within_inter_open v_open  _ ⟨⟨xs, vu ⟨xv, xs⟩⟩, xv⟩,
    rw A,
    exact hs.inter v_open },
  rw A at this,
  rw ← this
end

/-- The iterated differential within a set `s` at a point `x` is not modified if one intersects
`s` with a neighborhood of `x`. -/
lemma iterated_fderiv_within_inter {n : ℕ}
  (hu : u ∈ nhds x) (hs : unique_diff_on 𝕜 s) (xs : x ∈ s) :
  iterated_fderiv_within 𝕜 n f (s ∩ u) x = iterated_fderiv_within 𝕜 n f s x :=
iterated_fderiv_within_inter' (mem_nhds_within_of_mem_nhds hu) hs xs

@[simp] lemma times_cont_diff_on_zero :
  times_cont_diff_on 𝕜 0 f s ↔ continuous_on f s :=
begin
  refine ⟨λ H, H.continuous_on, λ H, _⟩,
  assume m hm x hx,
  have : (m : with_top ℕ) = 0 := le_antisymm hm bot_le,
  rw this,
  refine ⟨s, self_mem_nhds_within, ftaylor_series_within 𝕜 f s, _⟩,
  rw has_ftaylor_series_up_to_on_zero_iff,
  exact ⟨H, λ x hx, by simp [ftaylor_series_within]⟩
end

/-- On a set with unique differentiability, any choice of iterated differential has to coincide
with the one we have chosen in `iterated_fderiv_within 𝕜 m f s`. -/
theorem has_ftaylor_series_up_to_on.eq_ftaylor_series_of_unique_diff_on {n : with_top ℕ}
  (h : has_ftaylor_series_up_to_on n f p s)
  {m : ℕ} (hmn : (m : with_top ℕ) ≤ n) (hs : unique_diff_on 𝕜 s) (hx : x ∈ s) :
  p x m = iterated_fderiv_within 𝕜 m f s x :=
begin
  induction m with m IH generalizing x,
  { rw [h.zero_eq' hx, iterated_fderiv_within_zero_eq_comp] },
  { have A : (m : with_top ℕ) < n := lt_of_lt_of_le (with_top.coe_lt_coe.2 (lt_add_one m)) hmn,
    have : has_fderiv_within_at (λ (y : E), iterated_fderiv_within 𝕜 m f s y)
      (continuous_multilinear_map.curry_left (p x (nat.succ m))) s x :=
    (h.fderiv_within m A x hx).congr (λ y hy, (IH (le_of_lt A) hy).symm) (IH (le_of_lt A) hx).symm,
    rw [iterated_fderiv_within_succ_eq_comp_left, function.comp_apply, this.fderiv_within (hs x hx)],
    exact (continuous_multilinear_map.uncurry_curry_left _).symm }
end

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem times_cont_diff_on.ftaylor_series_within {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) :
has_ftaylor_series_up_to_on n f (ftaylor_series_within 𝕜 f s) s :=
begin
  split,
  { assume x hx,
    simp only [ftaylor_series_within, continuous_multilinear_map.uncurry0_apply,
               iterated_fderiv_within_zero_apply] },
  { assume m hm x hx,
    rcases h m.succ (with_top.add_one_le_of_lt hm) x hx with ⟨u, hu, p, Hp⟩,
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
    rw inter_comm at ho,
    have : p x m.succ = ftaylor_series_within 𝕜 f s x m.succ,
    { change p x m.succ = iterated_fderiv_within 𝕜 m.succ f s x,
      rw ← iterated_fderiv_within_inter (mem_nhds_sets o_open xo) hs hx,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (le_refl _)
        (hs.inter o_open) ⟨hx, xo⟩ },
    rw [← this, ← has_fderiv_within_at_inter (mem_nhds_sets o_open xo)],
    have A : ∀ y ∈ s ∩ o, p y m = ftaylor_series_within 𝕜 f s y m,
    { rintros y ⟨hy, yo⟩,
      change p y m = iterated_fderiv_within 𝕜 m f s y,
      rw ← iterated_fderiv_within_inter (mem_nhds_sets o_open yo) hs hy,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (with_top.coe_le_coe.2 (nat.le_succ m))
        (hs.inter o_open) ⟨hy, yo⟩ },
    exact ((Hp.mono ho).fderiv_within m (with_top.coe_lt_coe.2 (lt_add_one m)) x ⟨hx, xo⟩).congr
      (λ y hy, (A y hy).symm) (A x ⟨hx, xo⟩).symm },
  { assume m hm,
    apply continuous_on_of_locally_continuous_on,
    assume x hx,
    rcases h m hm x hx with ⟨u, hu, p, Hp⟩,
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
    rw inter_comm at ho,
    refine ⟨o, o_open, xo, _⟩,
    have A : ∀ y ∈ s ∩ o, p y m = ftaylor_series_within 𝕜 f s y m,
    { rintros y ⟨hy, yo⟩,
      change p y m = iterated_fderiv_within 𝕜 m f s y,
      rw ← iterated_fderiv_within_inter (mem_nhds_sets o_open yo) hs hy,
      exact (Hp.mono ho).eq_ftaylor_series_of_unique_diff_on (le_refl _)
        (hs.inter o_open) ⟨hy, yo⟩ },
    exact ((Hp.mono ho).cont m (le_refl _)).congr (λ y hy, (A y hy).symm) }
end

lemma times_cont_diff_on_of_continuous_on_differentiable_on {n : with_top ℕ}
  (Hcont : ∀ (m : ℕ), (m : with_top ℕ) ≤ n →
    continuous_on (λ x, iterated_fderiv_within 𝕜 m f s x) s)
  (Hdiff : ∀ (m : ℕ), (m : with_top ℕ) < n →
    differentiable_on 𝕜 (λ x, iterated_fderiv_within 𝕜 m f s x) s) :
  times_cont_diff_on 𝕜 n f s :=
begin
  assume m hm x hx,
  refine ⟨s, self_mem_nhds_within, ftaylor_series_within 𝕜 f s, _⟩,
  split,
  { assume x hx,
    simp only [ftaylor_series_within, continuous_multilinear_map.uncurry0_apply,
                iterated_fderiv_within_zero_apply] },
  { assume k hk x hx,
    convert (Hdiff k (lt_of_lt_of_le hk hm) x hx).has_fderiv_within_at,
    simp only [ftaylor_series_within, iterated_fderiv_within_succ_eq_comp_left,
                continuous_linear_equiv.coe_apply, function.comp_app, coe_fn_coe_base],
    exact continuous_linear_map.curry_uncurry_left _ },
  { assume k hk,
    exact Hcont k (le_trans hk hm) }
end

lemma times_cont_diff_on_of_differentiable_on {n : with_top ℕ}
  (h : ∀(m : ℕ), (m : with_top ℕ) ≤ n → differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s) :
  times_cont_diff_on 𝕜 n f s :=
times_cont_diff_on_of_continuous_on_differentiable_on
  (λ m hm, (h m hm).continuous_on) (λ m hm, (h m (le_of_lt hm)))

lemma times_cont_diff_on.continuous_on_iterated_fderiv_within {n : with_top ℕ} {m : ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hmn : (m : with_top ℕ) ≤ n) (hs : unique_diff_on 𝕜 s) :
  continuous_on (iterated_fderiv_within 𝕜 m f s) s :=
(h.ftaylor_series_within hs).cont m hmn

lemma times_cont_diff_on.differentiable_on_iterated_fderiv_within {n : with_top ℕ} {m : ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hmn : (m : with_top ℕ) < n) (hs : unique_diff_on 𝕜 s) :
  differentiable_on 𝕜 (iterated_fderiv_within 𝕜 m f s) s :=
λ x hx, ((h.ftaylor_series_within hs).fderiv_within m hmn x hx).differentiable_within_at

lemma times_cont_diff_on_iff_continuous_on_differentiable_on {n : with_top ℕ}
  (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 n f s ↔
  (∀ (m : ℕ), (m : with_top ℕ) ≤ n →
    continuous_on (λ x, iterated_fderiv_within 𝕜 m f s x) s)
  ∧ (∀ (m : ℕ), (m : with_top ℕ) < n →
    differentiable_on 𝕜 (λ x, iterated_fderiv_within 𝕜 m f s x) s) :=
begin
  split,
  { assume h,
    split,
    { assume m hm, exact h.continuous_on_iterated_fderiv_within hm hs },
    { assume m hm, exact h.differentiable_on_iterated_fderiv_within hm hs } },
  { assume h,
    exact times_cont_diff_on_of_continuous_on_differentiable_on h.1 h.2 }
end

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^n`. -/
theorem times_cont_diff_on_succ_iff_fderiv_within {n : ℕ} (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 ((n + 1) : ℕ) f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 n (λ y, fderiv_within 𝕜 f s y) s :=
begin
  split,
  { assume H,
    refine ⟨H.differentiable_on (with_top.coe_le_coe.2 (nat.le_add_left 1 n)), _⟩,
    apply times_cont_diff_on_of_locally_times_cont_diff_on,
    assume x hx,
    rcases times_cont_diff_on_succ_iff_has_fderiv_within_at.1 H x hx with ⟨u, hu, f', hff', hf'⟩,
    rcases mem_nhds_within.1 hu with ⟨o, o_open, xo, ho⟩,
    rw inter_comm at ho,
    refine ⟨o, o_open, xo, _⟩,
    apply (hf'.mono ho).congr (λ y hy, _),
    have A : fderiv_within 𝕜 f (s ∩ o) y = f' y :=
      ((hff' y (ho hy)).mono ho).fderiv_within (hs.inter o_open y hy),
    rwa fderiv_within_inter (mem_nhds_sets o_open hy.2) (hs y hy.1) at A },
  { rw times_cont_diff_on_succ_iff_has_fderiv_within_at,
    rintros ⟨hdiff, h⟩ x hx,
    exact ⟨s, self_mem_nhds_within, fderiv_within 𝕜 f s,
           λ x hx, (hdiff x hx).has_fderiv_within_at, h⟩ }
end

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^∞`. -/
theorem times_cont_diff_on_top_iff_fderiv_within (hs : unique_diff_on 𝕜 s) :
  times_cont_diff_on 𝕜 ⊤ f s ↔
  differentiable_on 𝕜 f s ∧ times_cont_diff_on 𝕜 ⊤ (λ y, fderiv_within 𝕜 f s y) s :=
begin
  split,
  { assume h,
    refine ⟨h.differentiable_on le_top, _⟩,
    apply times_cont_diff_on_top.2 (λ n, ((times_cont_diff_on_succ_iff_fderiv_within hs).1 _).2),
    exact h.of_le le_top },
  { assume h,
    refine times_cont_diff_on_top.2 (λ n, _),
    have A : (n : with_top ℕ) ≤ ⊤ := le_top,
    apply ((times_cont_diff_on_succ_iff_fderiv_within hs).2 ⟨h.1, h.2.of_le A⟩).of_le,
    exact with_top.coe_le_coe.2 (nat.le_succ n) }
end

lemma times_cont_diff_on.fderiv_within {m n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (λ y, fderiv_within 𝕜 f s y) s :=
begin
  cases m,
  { change ⊤ + 1 ≤ n at hmn,
    have : n = ⊤, by simpa using hmn,
    rw this at hf,
    exact ((times_cont_diff_on_top_iff_fderiv_within hs).1 hf).2 },
  { change (m.succ : with_top ℕ) ≤ n at hmn,
    exact ((times_cont_diff_on_succ_iff_fderiv_within hs).1 (hf.of_le hmn)).2 }
end

lemma times_cont_diff_on.continuous_on_fderiv_within {n : with_top ℕ}
  (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hn : 1 ≤ n) :
  continuous_on (λ x, fderiv_within 𝕜 f s x) s :=
((times_cont_diff_on_succ_iff_fderiv_within hs).1 (h.of_le hn)).2.continuous_on

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
lemma times_cont_diff_on.continuous_on_fderiv_within_apply
  {n : with_top ℕ} (h : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hn : 1 ≤ n) :
  continuous_on (λp : E × E, (fderiv_within 𝕜 f s p.1 : E → F) p.2) (set.prod s univ) :=
begin
  have A : continuous (λq : (E →L[𝕜] F) × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
  have B : continuous_on (λp : E × E, (fderiv_within 𝕜 f s p.1, p.2)) (set.prod s univ),
  { apply continuous_on.prod _ continuous_snd.continuous_on,
    exact continuous_on.comp (h.continuous_on_fderiv_within hs hn) continuous_fst.continuous_on
      (prod_subset_preimage_fst _ _) },
  exact A.comp_continuous_on B
end

/-- `has_ftaylor_series_up_to n f p` registers the fact that `p 0 = f` and `p (m+1)` is a
derivative of `p m` for `m < n`, and is continuous for `m ≤ n`. This is a predicate analogous to
`has_fderiv_at` but for higher order derivatives. -/
structure has_ftaylor_series_up_to (n : with_top ℕ)
  (f : E → F) (p : E → formal_multilinear_series 𝕜 E F) : Prop :=
(zero_eq : ∀ x, (p x 0).uncurry0 = f x)
(fderiv  : ∀ (m : ℕ) (hm : (m : with_top ℕ) < n), ∀ x,
    has_fderiv_at (λ y, p y m) (p x m.succ).curry_left x)
(cont    : ∀ (m : ℕ) (hm : (m : with_top ℕ) ≤ n), continuous (λ x, p x m))

lemma has_ftaylor_series_up_to.zero_eq' {n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (x : E) :
  p x 0 = (continuous_multilinear_curry_fin0 𝕜 E F).symm (f x) :=
by { rw ← h.zero_eq x, symmetry, exact continuous_multilinear_map.uncurry0_curry0 _ }

lemma has_ftaylor_series_up_to_on_univ_iff {n : with_top ℕ} :
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

lemma has_ftaylor_series_up_to.has_ftaylor_series_up_to_on {n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (s : set E) :
  has_ftaylor_series_up_to_on n f p s :=
(has_ftaylor_series_up_to_on_univ_iff.2 h).mono (subset_univ _)

lemma has_ftaylor_series_up_to.of_le {m n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (hmn : m ≤ n) :
  has_ftaylor_series_up_to m f p :=
by { rw ← has_ftaylor_series_up_to_on_univ_iff at h ⊢, exact h.of_le hmn }

lemma has_ftaylor_series_up_to.continuous {n : with_top ℕ}
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
lemma has_ftaylor_series_up_to.has_fderiv_at {n : with_top ℕ}
  (h : has_ftaylor_series_up_to n f p) (hn : 1 ≤ n) (x : E) :
  has_fderiv_at f (continuous_multilinear_curry_fin1 𝕜 E F (p x 1)) x :=
begin
  rw [← has_fderiv_within_at_univ],
  exact (has_ftaylor_series_up_to_on_univ_iff.2 h).has_fderiv_within_at hn (mem_univ _)
end

lemma has_ftaylor_series_up_to.differentiable {n : with_top ℕ}
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
by simp [has_ftaylor_series_up_to_on_succ_iff_right, has_ftaylor_series_up_to_on_univ_iff.symm,
         -add_comm, -with_bot.coe_add]

variable (𝕜)

/-- A function is continuously differentiable up to `n` if it admits derivatives up to
order `n`, which are continuous. Contrary to the case of definitions in domains (where derivatives
might not be unique) we do not need to localize the definition in space or time.
-/
definition times_cont_diff (n : with_top ℕ) (f : E → F)  :=
∃ p : E → formal_multilinear_series 𝕜 E F, has_ftaylor_series_up_to n f p

variable {𝕜}

theorem times_cont_diff_on_univ {n : with_top ℕ} :
  times_cont_diff_on 𝕜 n f univ ↔ times_cont_diff 𝕜 n f :=
begin
  split,
  { assume H,
    use ftaylor_series_within 𝕜 f univ,
    rw ← has_ftaylor_series_up_to_on_univ_iff,
    exact H.ftaylor_series_within unique_diff_on_univ },
  { rintros ⟨p, hp⟩ m hm x hx,
    exact ⟨univ, self_mem_nhds_within, p, (hp.has_ftaylor_series_up_to_on univ).of_le hm⟩ }
end

lemma times_cont_diff_top :
  times_cont_diff 𝕜 ⊤ f ↔ ∀ (n : ℕ), times_cont_diff 𝕜 n f :=
by simp [times_cont_diff_on_univ.symm, times_cont_diff_on_top]

lemma times_cont_diff.times_cont_diff_on {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) : times_cont_diff_on 𝕜 n f s :=
(times_cont_diff_on_univ.2 h).mono (subset_univ _)

@[simp] lemma times_cont_diff_zero :
  times_cont_diff 𝕜 0 f ↔ continuous f :=
begin
  rw [← times_cont_diff_on_univ, continuous_iff_continuous_on_univ],
  exact times_cont_diff_on_zero
end

lemma times_cont_diff.of_le {m n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) (hmn : m ≤ n) :
  times_cont_diff 𝕜 m f :=
times_cont_diff_on_univ.1 $ (times_cont_diff_on_univ.2 h).of_le hmn

lemma times_cont_diff.continuous {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) : continuous f :=
times_cont_diff_zero.1 (h.of_le bot_le)

/-- If a function is `C^n` with `n ≥ 1`, then it is differentiable. -/
lemma times_cont_diff.differentiable {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) : differentiable 𝕜 f :=
differentiable_on_univ.1 $ (times_cont_diff_on_univ.2 h).differentiable_on hn

variable (𝕜)


/-! ### Iterated derivative -/

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

lemma iterated_fderiv_succ_apply_left {n : ℕ} (m : fin (n + 1) → E):
  (iterated_fderiv 𝕜 (n + 1) f x : (fin (n + 1) → E) → F) m
  = (fderiv 𝕜 (iterated_fderiv 𝕜 n f) x : E → (E [×n]→L[𝕜] F)) (m 0) (tail m) := rfl

/-- Writing explicitly the `n+1`-th derivative as the composition of a currying linear equiv,
and the derivative of the `n`-th derivative. -/
lemma iterated_fderiv_succ_eq_comp_left {n : ℕ} :
  iterated_fderiv 𝕜 (n + 1) f =
  (continuous_multilinear_curry_left_equiv 𝕜 (λ(i : fin (n + 1)), E) F)
    ∘ (fderiv 𝕜 (iterated_fderiv 𝕜 n f)) := rfl

lemma iterated_fderiv_within_univ {n : ℕ} :
  iterated_fderiv_within 𝕜 n f univ = iterated_fderiv 𝕜 n f :=
begin
  induction n with n IH,
  { ext x, simp },
  { ext x m,
    rw [iterated_fderiv_succ_apply_left, iterated_fderiv_within_succ_apply_left, IH,
        fderiv_within_univ] }
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
  ((continuous_multilinear_curry_right_equiv 𝕜 (λ(i : fin (n + 1)), E) F)
    ∘ (iterated_fderiv 𝕜 n (λy, fderiv 𝕜 f y))) x :=
by { ext m, rw iterated_fderiv_succ_apply_right, refl }

@[simp] lemma iterated_fderiv_one_apply (m : (fin 1) → E) :
  (iterated_fderiv 𝕜 1 f x : ((fin 1) → E) → F) m
  = (fderiv 𝕜 f x : E → F) (m 0) :=
by { rw [iterated_fderiv_succ_apply_right, iterated_fderiv_zero_apply], refl }

/-- When a function is `C^n` in a set `s` of unique differentiability, it admits
`ftaylor_series_within 𝕜 f s` as a Taylor series up to order `n` in `s`. -/
theorem times_cont_diff_on_iff_ftaylor_series {n : with_top ℕ} :
  times_cont_diff 𝕜 n f ↔ has_ftaylor_series_up_to n f (ftaylor_series 𝕜 f) :=
begin
  split,
  { rw [← times_cont_diff_on_univ, ← has_ftaylor_series_up_to_on_univ_iff,
        ← ftaylor_series_within_univ],
    exact λ h, times_cont_diff_on.ftaylor_series_within h unique_diff_on_univ },
  { assume h, exact ⟨ftaylor_series 𝕜 f, h⟩ }
end

lemma times_cont_diff_iff_continuous_differentiable {n : with_top ℕ} :
  times_cont_diff 𝕜 n f ↔
  (∀ (m : ℕ), (m : with_top ℕ) ≤ n → continuous (λ x, iterated_fderiv 𝕜 m f x))
  ∧ (∀ (m : ℕ), (m : with_top ℕ) < n → differentiable 𝕜 (λ x, iterated_fderiv 𝕜 m f x)) :=
by simp [times_cont_diff_on_univ.symm, continuous_iff_continuous_on_univ,
    differentiable_on_univ.symm, iterated_fderiv_within_univ,
    times_cont_diff_on_iff_continuous_on_differentiable_on unique_diff_on_univ]

lemma times_cont_diff_of_differentiable_iterated_fderiv {n : with_top ℕ}
  (h : ∀(m : ℕ), (m : with_top ℕ) ≤ n → differentiable 𝕜 (iterated_fderiv 𝕜 m f)) :
  times_cont_diff 𝕜 n f :=
times_cont_diff_iff_continuous_differentiable.2
⟨λ m hm, (h m hm).continuous, λ m hm, (h m (le_of_lt hm))⟩

/-- A function is `C^(n + 1)` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^n`. -/
theorem times_cont_diff_succ_iff_fderiv {n : ℕ} :
  times_cont_diff 𝕜 ((n + 1) : ℕ) f ↔
  differentiable 𝕜 f ∧ times_cont_diff 𝕜 n (λ y, fderiv 𝕜 f y) :=
by simp [times_cont_diff_on_univ.symm, differentiable_on_univ.symm, fderiv_within_univ.symm,
         - fderiv_within_univ, times_cont_diff_on_succ_iff_fderiv_within unique_diff_on_univ,
         -with_bot.coe_add, -add_comm]

/-- A function is `C^∞` on a domain with unique derivatives if and only if it is differentiable
there, and its derivative is `C^∞`. -/
theorem times_cont_diff_top_iff_fderiv :
  times_cont_diff 𝕜 ⊤ f ↔
  differentiable 𝕜 f ∧ times_cont_diff 𝕜 ⊤ (λ y, fderiv 𝕜 f y) :=
begin
  simp [times_cont_diff_on_univ.symm, differentiable_on_univ.symm, fderiv_within_univ.symm,
        - fderiv_within_univ],
  rw times_cont_diff_on_top_iff_fderiv_within unique_diff_on_univ,
end

lemma times_cont_diff.continuous_fderiv {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) :
  continuous (λ x, fderiv 𝕜 f x) :=
((times_cont_diff_succ_iff_fderiv).1 (h.of_le hn)).2.continuous

/-- If a function is at least `C^1`, its bundled derivative (mapping `(x, v)` to `Df(x) v`) is
continuous. -/
lemma times_cont_diff.continuous_fderiv_apply {n : with_top ℕ}
  (h : times_cont_diff 𝕜 n f) (hn : 1 ≤ n) :
  continuous (λp : E × E, (fderiv 𝕜 f p.1 : E → F) p.2) :=
begin
  have A : continuous (λq : (E →L[𝕜] F) × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
  have B : continuous (λp : E × E, (fderiv 𝕜 f p.1, p.2)),
  { apply continuous.prod_mk _ continuous_snd,
    exact continuous.comp (h.continuous_fderiv hn) continuous_fst },
  exact A.comp B
end

/-! ### Constants -/

lemma iterated_fderiv_within_zero_fun {n : ℕ} :
  iterated_fderiv 𝕜 n (λ x : E, (0 : F)) = 0 :=
begin
  induction n with n IH,
  { ext m, simp },
  { ext x m,
    rw [iterated_fderiv_succ_apply_left, IH],
    change (fderiv 𝕜 (λ (x : E), (0 : (E [×n]→L[𝕜] F))) x : E → (E [×n]→L[𝕜] F)) (m 0) (tail m) = _,
    rw fderiv_const,
    refl }
end

lemma times_cont_diff_zero_fun {n : with_top ℕ} :
  times_cont_diff 𝕜 n (λ x : E, (0 : F)) :=
begin
  apply times_cont_diff_of_differentiable_iterated_fderiv (λm hm, _),
  rw iterated_fderiv_within_zero_fun,
  apply differentiable_const (0 : (E [×m]→L[𝕜] F))
end

/--
Constants are `C^∞`.
-/
lemma times_cont_diff_const {n : with_top ℕ} {c : F} : times_cont_diff 𝕜 n (λx : E, c) :=
begin
  suffices h : times_cont_diff 𝕜 ⊤ (λx : E, c), by exact h.of_le le_top,
  rw times_cont_diff_top_iff_fderiv,
  refine ⟨differentiable_const c, _⟩,
  rw fderiv_const,
  exact times_cont_diff_zero_fun
end

lemma times_cont_diff_on_const {n : with_top ℕ} {c : F} {s : set E} :
  times_cont_diff_on 𝕜 n (λx : E, c) s :=
times_cont_diff_const.times_cont_diff_on

/-! ### Linear functions -/

/--
Unbundled bounded linear functions are `C^∞`.
-/
lemma is_bounded_linear_map.times_cont_diff {n : with_top ℕ} (hf : is_bounded_linear_map 𝕜 f) :
  times_cont_diff 𝕜 n f :=
begin
  suffices h : times_cont_diff 𝕜 ⊤ f, by exact h.of_le le_top,
  rw times_cont_diff_top_iff_fderiv,
  refine ⟨hf.differentiable, _⟩,
  simp [hf.fderiv],
  exact times_cont_diff_const
end

lemma continuous_linear_map.times_cont_diff {n : with_top ℕ} (f : E →L[𝕜] F) :
  times_cont_diff 𝕜 n f :=
f.is_bounded_linear_map.times_cont_diff

/--
The first projection in a product is `C^∞`.
-/
lemma times_cont_diff_fst {n : with_top ℕ} : times_cont_diff 𝕜 n (prod.fst : E × F → E) :=
is_bounded_linear_map.times_cont_diff is_bounded_linear_map.fst

/--
The second projection in a product is `C^∞`.
-/
lemma times_cont_diff_snd {n : with_top ℕ} : times_cont_diff 𝕜 n (prod.snd : E × F → F) :=
is_bounded_linear_map.times_cont_diff is_bounded_linear_map.snd

/--
The identity is `C^∞`.
-/
lemma times_cont_diff_id {n : with_top ℕ} : times_cont_diff 𝕜 n (id : E → E) :=
is_bounded_linear_map.id.times_cont_diff

/--
Bilinear functions are `C^∞`.
-/
lemma is_bounded_bilinear_map.times_cont_diff {n : with_top ℕ} (hb : is_bounded_bilinear_map 𝕜 b) :
  times_cont_diff 𝕜 n b :=
begin
  suffices h : times_cont_diff 𝕜 ⊤ b, by exact h.of_le le_top,
  rw times_cont_diff_top_iff_fderiv,
  refine ⟨hb.differentiable, _⟩,
  simp [hb.fderiv],
  exact hb.is_bounded_linear_map_deriv.times_cont_diff
end

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `g ∘ f` admits a Taylor
series whose `k`-th term is given by `g ∘ (p k)`. -/
lemma has_ftaylor_series_up_to_on.continuous_linear_map_comp {n : with_top ℕ} (g : F →L[𝕜] G)
  (hf : has_ftaylor_series_up_to_on n f p s) :
  has_ftaylor_series_up_to_on n (g ∘ f) (λ x k, g.comp_continuous_multilinear_map (p x k)) s :=
begin
  split,
  { assume x hx, simp [(hf.zero_eq x hx).symm] },
  { assume m hm x hx,
    let A : (E [×m]→L[𝕜] F) → (E [×m]→L[𝕜] G) := λ f, g.comp_continuous_multilinear_map f,
    have hA : is_bounded_linear_map 𝕜 A :=
      is_bounded_bilinear_map_comp_multilinear.is_bounded_linear_map_right _,
    have := hf.fderiv_within m hm x hx,
    convert has_fderiv_at.comp_has_fderiv_within_at x (hA.has_fderiv_at) this },
  { assume m hm,
    let A : (E [×m]→L[𝕜] F) → (E [×m]→L[𝕜] G) :=
      λ f, g.comp_continuous_multilinear_map f,
    have hA : is_bounded_linear_map 𝕜 A :=
      is_bounded_bilinear_map_comp_multilinear.is_bounded_linear_map_right _,
    exact hA.continuous.comp_continuous_on (hf.cont m hm) }
end


/-- Composition by continuous linear maps on the left preserves `C^n` functions on domains. -/
lemma times_cont_diff_on.continuous_linear_map_comp {n : with_top ℕ} (g : F →L[𝕜] G)
  (hf : times_cont_diff_on 𝕜 n f s) :
  times_cont_diff_on 𝕜 n (g ∘ f) s :=
begin
  assume m hm x hx,
  rcases hf m hm x hx with ⟨u, hu, p, hp⟩,
  exact ⟨u, hu, _, hp.continuous_linear_map_comp g⟩,
end

/-- Composition by continuous linear maps on the left preserves `C^n` functions. -/
lemma times_cont_diff.continuous_linear_map_comp {n : with_top ℕ} {f : E → F} (g : F →L[𝕜] G)
  (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n (λx, g (f x)) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.continuous_linear_map_comp
  _ (times_cont_diff_on_univ.2 hf)

/-- Composition by continuous linear equivs on the left respects higher differentiability on
domains. -/
lemma continuous_linear_equiv.comp_times_cont_diff_on_iff
  {n : with_top ℕ} (e : F ≃L[𝕜] G) :
  times_cont_diff_on 𝕜 n (e ∘ f) s ↔ times_cont_diff_on 𝕜 n f s :=
begin
  split,
  { assume H,
    have : f = e.symm ∘ (e ∘ f),
      by { ext y, simp only [function.comp_app], rw e.symm_apply_apply (f y) },
    rw this,
    exact H.continuous_linear_map_comp _ },
  { assume H,
    exact H.continuous_linear_map_comp _ }
end

/-- If `f` admits a Taylor series `p` in a set `s`, and `g` is linear, then `f ∘ g` admits a Taylor
series in `g ⁻¹' s`, whose `k`-th term is given by `p k (g v₁, ..., g vₖ)` . -/
lemma has_ftaylor_series_up_to_on.comp_continuous_linear_map {n : with_top ℕ}
  (hf : has_ftaylor_series_up_to_on n f p s) (g : G →L[𝕜] E) :
  has_ftaylor_series_up_to_on n (f ∘ g)
    (λ x k, (p (g x) k).comp_continuous_linear_map 𝕜 E g) (g ⁻¹' s) :=
begin
  split,
  { assume x hx,
    simp only [(hf.zero_eq (g x) hx).symm, function.comp_app],
    change p (g x) 0 (λ (i : fin 0), g 0) = p (g x) 0 0,
    rw continuous_linear_map.map_zero,
    refl },
  { assume m hm x hx,
    let A : (E [×m]→L[𝕜] F) → (G [×m]→L[𝕜] F) := λ h, h.comp_continuous_linear_map 𝕜 E g,
    have hA : is_bounded_linear_map 𝕜 A :=
      is_bounded_linear_map_continuous_multilinear_map_comp_linear g,
    convert (hA.has_fderiv_at).comp_has_fderiv_within_at x
      ((hf.fderiv_within m hm (g x) hx).comp x (g.has_fderiv_within_at) (subset.refl _)),
    ext y v,
    change p (g x) (nat.succ m) (g ∘ (cons y v)) = p (g x) m.succ (cons (g y) (g ∘ v)),
    rw comp_cons },
  { assume m hm,
    let A : (E [×m]→L[𝕜] F) → (G [×m]→L[𝕜] F) := λ h, h.comp_continuous_linear_map 𝕜 E g,
    have hA : is_bounded_linear_map 𝕜 A :=
      is_bounded_linear_map_continuous_multilinear_map_comp_linear g,
    exact hA.continuous.comp_continuous_on
      ((hf.cont m hm).comp g.continuous.continuous_on (subset.refl _)) }
end

/-- Composition by continuous linear maps on the right preserves `C^n` functions on domains. -/
lemma times_cont_diff_on.comp_continuous_linear_map {n : with_top ℕ}
  (hf : times_cont_diff_on 𝕜 n f s) (g : G →L[𝕜] E) :
  times_cont_diff_on 𝕜 n (f ∘ g) (g ⁻¹' s) :=
begin
  assume m hm x hx,
  rcases hf m hm (g x) hx with ⟨u, hu, p, hp⟩,
  refine ⟨g ⁻¹' u, _, _, hp.comp_continuous_linear_map g⟩,
  apply continuous_within_at.preimage_mem_nhds_within',
  { exact g.continuous.continuous_within_at },
  { exact nhds_within_mono (g x) (image_preimage_subset g s) hu }
end

/-- Composition by continuous linear maps on the right preserves `C^n` functions. -/
lemma times_cont_diff.comp_continuous_linear_map {n : with_top ℕ} {f : E → F} {g : G →L[𝕜] E}
  (hf : times_cont_diff 𝕜 n f) : times_cont_diff 𝕜 n (f ∘ g) :=
times_cont_diff_on_univ.1 $
times_cont_diff_on.comp_continuous_linear_map (times_cont_diff_on_univ.2 hf) _

/-- Composition by continuous linear equivs on the right respects higher differentiability on
domains. -/
lemma continuous_linear_equiv.times_cont_diff_on_comp_iff {n : with_top ℕ} (e : G ≃L[𝕜] E) :
  times_cont_diff_on 𝕜 n (f ∘ e) (e ⁻¹' s) ↔ times_cont_diff_on 𝕜 n f s :=
begin
  refine ⟨λ H, _, λ H, H.comp_continuous_linear_map _⟩,
  have A : f = (f ∘ e) ∘ e.symm,
    by { ext y, simp only [function.comp_app], rw e.apply_symm_apply y },
  have B : e.symm ⁻¹' (e ⁻¹' s) = s,
    by { rw [← preimage_comp, e.self_comp_symm], refl },
  rw [A, ← B],
  exact H.comp_continuous_linear_map _
end

/-- If two functions `f` and `g` admit Taylor series `p` and `q` in a set `s`, then the cartesian
product of `f` and `g` admits the cartesian product of `p` and `q` as a Taylor series. -/
lemma has_ftaylor_series_up_to_on.prod {n : with_top ℕ} (hf : has_ftaylor_series_up_to_on n f p s)
  {g : E → G} {q : E → formal_multilinear_series 𝕜 E G} (hg : has_ftaylor_series_up_to_on n g q s) :
  has_ftaylor_series_up_to_on n (λ y, (f y, g y)) (λ y k, (p y k).prod (q y k)) s :=
begin
  split,
  { assume x hx, rw [← hf.zero_eq x hx, ← hg.zero_eq x hx], refl },
  { assume m hm x hx,
    let A : (E [×m]→L[𝕜] F) × (E [×m]→L[𝕜] G) → (E [×m]→L[𝕜] (F × G)) := λ p, p.1.prod p.2,
    have hA : is_bounded_linear_map 𝕜 A := is_bounded_linear_map_prod_multilinear,
    convert hA.has_fderiv_at.comp_has_fderiv_within_at x
      ((hf.fderiv_within m hm x hx).prod (hg.fderiv_within m hm x hx)) },
  { assume m hm,
    let A : (E [×m]→L[𝕜] F) × (E [×m]→L[𝕜] G) → (E [×m]→L[𝕜] (F × G)) := λ p, p.1.prod p.2,
    have hA : is_bounded_linear_map 𝕜 A := is_bounded_linear_map_prod_multilinear,
    exact hA.continuous.comp_continuous_on ((hf.cont m hm).prod (hg.cont m hm)) }
end

/-- The cartesian product of `C^n` functions on domains is `C^n`. -/
lemma times_cont_diff_on.prod {n : with_top ℕ} {s : set E} {f : E → F} {g : E → G}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) :
  times_cont_diff_on 𝕜 n (λx:E, (f x, g x)) s :=
begin
  assume m hm x hx,
  rcases hf m hm x hx with ⟨u, hu, p, hp⟩,
  rcases hg m hm x hx with ⟨v, hv, q, hq⟩,
  exact ⟨u ∩ v, filter.inter_mem_sets hu hv, _,
        (hp.mono (inter_subset_left u v)).prod (hq.mono (inter_subset_right u v))⟩
end

/--
The cartesian product of `C^n` functions is `C^n`.
-/
lemma times_cont_diff.prod {n : with_top ℕ} {f : E → F} {g : E → G}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (λx:E, (f x, g x)) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.prod (times_cont_diff_on_univ.2 hf)
  (times_cont_diff_on_univ.2 hg)

/-!
### Composition of `C^n` functions

We show that the composition of `C^n` functions is `C^n`. One way to prove it would be to write
the `n`-th derivative of the composition (this is Faà di Bruno's formula) and check its continuity,
but this is very painful. Instead, we go for a simple inductive proof. Assume it is done for `n`.
Then, to check it for `n+1`, one needs to check that the derivative of `g ∘ f` is `C^n`, i.e.,
that `Dg(f x) ⬝ Df(x)` is `C^n`. The term `Dg (f x)` is the composition of two `C^n` functions, so
it is `C^n` by the inductive assumption. The term `Df(x)` is also `C^n`. Then, the matrix
multiplication is the application of a bilinear map (which is `C^∞`, and therefore `C^n`) to
`x ↦ (Dg(f x), Df x)`. As the composition of two `C^n` maps, it is again `C^n`, and we are done.

There is a subtlety in this argument: we apply the inductive assumption to functions on other Banach
spaces. In maths, one would say: prove by induction over `n` that, for all `C^n` maps between all
pairs of Banach spaces, their composition is `C^n`. In Lean, this is fine as long as the spaces
stay in the same universe. This is not the case in the above argument: if `E` lives in universe `u`
and `F` lives in universe `v`, then linear maps from `E` to `F` (to which the derivative of `f`
belongs) is in universe `max u v`. If one could quantify over finitely many universes, the above
proof would work fine, but this is not the case. One could still write the proof considering spaces
in any universe in `u, v, w, max u v, max v w, max u v w`, but it would be extremely tedious and
lead to a lot of duplication. Instead, we formulate the above proof when all spaces live in the same
universe (where everything is fine), and then we deduce the general result by lifting all our spaces
to a common universe. We use the trick that any space `H` is isomorphic through a continuous linear
equiv to `continuous_multilinear_map (λ (i : fin 0), E × F × G) H` to change the universe level,
and then argue that composing with such a linear equiv does not change the fact of being `C^n`,
which we have already proved previously.
-/

/-- Auxiliary lemma proving that the composition of `C^n` functions on domains is `C^n` when all
spaces live in the same universe. Use instead `times_cont_diff_on.comp` which removes the universe
assumption (but is deduced from this one). -/
private lemma times_cont_diff_on.comp_same_univ
  {Eu : Type u} [normed_group Eu] [normed_space 𝕜 Eu]
  {Fu : Type u} [normed_group Fu] [normed_space 𝕜 Fu]
  {Gu : Type u} [normed_group Gu] [normed_space 𝕜 Gu]
  {n : with_top ℕ} {s : set Eu} {t : set Fu} {g : Fu → Gu} {f : Eu → Fu}
  (hg : times_cont_diff_on 𝕜 n g t) (hf : times_cont_diff_on 𝕜 n f s) (st : s ⊆ f ⁻¹' t) :
  times_cont_diff_on 𝕜 n (g ∘ f) s :=
begin
  unfreezeI,
  induction n using with_top.nat_induction with n IH Itop generalizing Eu Fu Gu,
  { rw times_cont_diff_on_zero at hf hg ⊢,
    exact continuous_on.comp hg hf st },
  { rw times_cont_diff_on_succ_iff_has_fderiv_within_at at hg ⊢,
    assume x hx,
    rcases (times_cont_diff_on_succ_iff_has_fderiv_within_at.1 hf) x hx
      with ⟨u, hu, f', hf', f'_diff⟩,
    rcases hg (f x) (st hx) with ⟨v, hv, g', hg', g'_diff⟩,
    have xu : x ∈ u := mem_of_mem_nhds_within hx hu,
    let w := s ∩ (u ∩ f⁻¹' v),
    have wv : w ⊆ f ⁻¹' v := λ y hy, hy.2.2,
    have wu : w ⊆ u := λ y hy, hy.2.1,
    have ws : w ⊆ s := λ y hy, hy.1,
    refine ⟨w, _, λ y, (g' (f y)).comp (f' y), _, _⟩,
    show w ∈ nhds_within x s,
    { apply filter.inter_mem_sets self_mem_nhds_within,
      apply filter.inter_mem_sets hu,
      apply continuous_within_at.preimage_mem_nhds_within',
      { rw ← continuous_within_at_inter' hu,
        exact (hf' x xu).differentiable_within_at.continuous_within_at.mono
          (inter_subset_right _ _) },
      { exact nhds_within_mono _ (image_subset_iff.2 st) hv } },
    show ∀ y ∈ w,
      has_fderiv_within_at (g ∘ f) ((g' (f y)).comp (f' y)) w y,
    { rintros y ⟨ys, yu, yv⟩,
      exact (hg' (f y) yv).comp y ((hf' y yu).mono wu) wv },
    show times_cont_diff_on 𝕜 n (λ y, (g' (f y)).comp (f' y)) w,
    { have A : times_cont_diff_on 𝕜 n (λ y, g' (f y)) w :=
        IH g'_diff ((hf.of_le (with_top.coe_le_coe.2 (nat.le_succ n))).mono ws) wv,
      have B : times_cont_diff_on 𝕜 n f' w := f'_diff.mono wu,
      have C : times_cont_diff_on 𝕜 n (λ y, (f' y, g' (f y))) w :=
        times_cont_diff_on.prod B A,
      have D : times_cont_diff_on 𝕜 n (λ(p : (Eu →L[𝕜] Fu) × (Fu →L[𝕜] Gu)), p.2.comp p.1) univ :=
        is_bounded_bilinear_map_comp.times_cont_diff.times_cont_diff_on,
      exact IH D C (subset_univ _) } },
  { rw times_cont_diff_on_top at hf hg ⊢,
    assume n,
    apply Itop n (hg n) (hf n) st }
end

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma times_cont_diff_on.comp
  {n : with_top ℕ} {s : set E} {t : set F} {g : F → G} {f : E → F}
  (hg : times_cont_diff_on 𝕜 n g t) (hf : times_cont_diff_on 𝕜 n f s) (st : s ⊆ f ⁻¹' t) :
  times_cont_diff_on 𝕜 n (g ∘ f) s :=
begin
  /- we lift all the spaces to a common universe, as we have already proved the result in this
  situation. For the lift, we use the trick that `H` is isomorphic through a
  continuous linear equiv to `continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) H`, and
  continuous linear equivs respect smoothness classes.
  The instances are not found automatically by Lean, so we declare them by hand.
  TODO: fix. -/
  let Eu := continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) E,
  letI : normed_group Eu :=
    @continuous_multilinear_map.to_normed_group 𝕜 (fin 0) (λ (i : fin 0), E × F × G) E _ _ _ _ _ _ _,
  letI : normed_space 𝕜 Eu :=
    @continuous_multilinear_map.to_normed_space 𝕜 (fin 0) (λ (i : fin 0), E × F × G) E _ _ _ _ _ _ _,
  let Fu := continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) F,
  letI : normed_group Fu :=
    @continuous_multilinear_map.to_normed_group 𝕜 (fin 0) (λ (i : fin 0), E × F × G) F _ _ _ _ _ _ _,
  letI : normed_space 𝕜 Fu :=
    @continuous_multilinear_map.to_normed_space 𝕜 (fin 0) (λ (i : fin 0), E × F × G) F _ _ _ _ _ _ _,
  let Gu := continuous_multilinear_map 𝕜 (λ (i : fin 0), (E × F × G)) G,
  letI : normed_group Gu :=
    @continuous_multilinear_map.to_normed_group 𝕜 (fin 0) (λ (i : fin 0), E × F × G) G _ _ _ _ _ _ _,
  letI : normed_space 𝕜 Gu :=
    @continuous_multilinear_map.to_normed_space 𝕜 (fin 0) (λ (i : fin 0), E × F × G) G _ _ _ _ _ _ _,
  -- declare the isomorphisms
  let isoE : Eu ≃L[𝕜] E := continuous_multilinear_curry_fin0 𝕜 (E × F × G) E,
  let isoF : Fu ≃L[𝕜] F := continuous_multilinear_curry_fin0 𝕜 (E × F × G) F,
  let isoG : Gu ≃L[𝕜] G := continuous_multilinear_curry_fin0 𝕜 (E × F × G) G,
  -- lift the functions to the new spaces, check smoothness there, and then go back.
  let fu : Eu → Fu := (isoF.symm ∘ f) ∘ isoE,
  have fu_diff : times_cont_diff_on 𝕜 n fu (isoE ⁻¹' s) :=
    by rwa [isoE.times_cont_diff_on_comp_iff, isoF.symm.comp_times_cont_diff_on_iff],
  let gu : Fu → Gu := (isoG.symm ∘ g) ∘ isoF,
  have gu_diff : times_cont_diff_on 𝕜 n gu (isoF ⁻¹' t) :=
    by rwa [isoF.times_cont_diff_on_comp_iff, isoG.symm.comp_times_cont_diff_on_iff],
  have main : times_cont_diff_on 𝕜 n (gu ∘ fu) (isoE ⁻¹' s),
  { apply times_cont_diff_on.comp_same_univ gu_diff fu_diff,
    assume y hy,
    simp only [fu, continuous_linear_equiv.coe_apply, function.comp_app, mem_preimage],
    rw isoF.apply_symm_apply (f (isoE y)),
    exact st hy },
  have : gu ∘ fu = (isoG.symm ∘ (g ∘ f)) ∘ isoE,
  { ext y,
    simp only [function.comp_apply, gu, fu],
    rw isoF.apply_symm_apply (f (isoE y)) },
  rwa [this, isoE.times_cont_diff_on_comp_iff, isoG.symm.comp_times_cont_diff_on_iff] at main
end

/-- The composition of a `C^n` function on a domain with a `C^n` function is `C^n`. -/
lemma times_cont_diff.comp_times_cont_diff_on {n : with_top ℕ} {s : set E} {g : F → G} {f : E → F}
  (hg : times_cont_diff 𝕜 n g) (hf : times_cont_diff_on 𝕜 n f s) :
  times_cont_diff_on 𝕜 n (g ∘ f) s :=
(times_cont_diff_on_univ.2 hg).comp hf subset_preimage_univ

/-- The composition of `C^n` functions is `C^n`. -/
lemma times_cont_diff.comp {n : with_top ℕ} {g : F → G} {f : E → F}
  (hg : times_cont_diff 𝕜 n g) (hf : times_cont_diff 𝕜 n f) :
  times_cont_diff 𝕜 n (g ∘ f) :=
times_cont_diff_on_univ.1 $ times_cont_diff_on.comp (times_cont_diff_on_univ.2 hg)
  (times_cont_diff_on_univ.2 hf) (subset_univ _)

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
lemma times_cont_diff_on_fderiv_within_apply {m n : with_top  ℕ} {s : set E}
  {f : E → F} (hf : times_cont_diff_on 𝕜 n f s) (hs : unique_diff_on 𝕜 s) (hmn : m + 1 ≤ n) :
  times_cont_diff_on 𝕜 m (λp : E × E, (fderiv_within 𝕜 f s p.1 : E →L[𝕜] F) p.2)
  (set.prod s (univ : set E)) :=
begin
  have A : times_cont_diff 𝕜 m (λp : (E →L[𝕜] F) × E, p.1 p.2),
  { apply is_bounded_bilinear_map.times_cont_diff,
    exact is_bounded_bilinear_map_apply },
  have B : times_cont_diff_on 𝕜 m
    (λ (p : E × E), ((fderiv_within 𝕜 f s p.fst), p.snd)) (set.prod s univ),
  { apply times_cont_diff_on.prod _ _,
    { have I : times_cont_diff_on 𝕜 m (λ (x : E), fderiv_within 𝕜 f s x) s :=
        hf.fderiv_within hs hmn,
      have J : times_cont_diff_on 𝕜 m (λ (x : E × E), x.1) (set.prod s univ) :=
        times_cont_diff_fst.times_cont_diff_on,
      exact times_cont_diff_on.comp I J (prod_subset_preimage_fst _ _) },
    { apply times_cont_diff.times_cont_diff_on _ ,
      apply is_bounded_linear_map.snd.times_cont_diff } },
  exact A.comp_times_cont_diff_on B
end

/-- The bundled derivative of a `C^{n+1}` function is `C^n`. -/
lemma times_cont_diff.times_cont_diff_fderiv_apply {n m : with_top ℕ} {f : E → F}
  (hf : times_cont_diff 𝕜 n f) (hmn : m + 1 ≤ n) :
  times_cont_diff 𝕜 m (λp : E × E, (fderiv 𝕜 f p.1 : E →L[𝕜] F) p.2) :=
begin
  rw ← times_cont_diff_on_univ at ⊢ hf,
  rw [← fderiv_within_univ, ← univ_prod_univ],
  exact times_cont_diff_on_fderiv_within_apply hf unique_diff_on_univ hmn
end

/-- The sum of two `C^n`functions on a domain is `C^n`. -/
lemma times_cont_diff_on.add {n : with_top ℕ} {s : set E} {f g : E → F}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) :
  times_cont_diff_on 𝕜 n (λx, f x + g x) s :=
begin
  have : times_cont_diff 𝕜 n (λp : F × F, p.1 + p.2),
  { apply is_bounded_linear_map.times_cont_diff,
    exact is_bounded_linear_map.add is_bounded_linear_map.fst is_bounded_linear_map.snd },
  exact this.comp_times_cont_diff_on (hf.prod hg)
end

/-- The sum of two `C^n`functions is `C^n`. -/
lemma times_cont_diff.add {n : with_top ℕ} {f g : E → F}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) : times_cont_diff 𝕜 n (λx, f x + g x) :=
begin
  have : times_cont_diff 𝕜 n (λp : F × F, p.1 + p.2),
  { apply is_bounded_linear_map.times_cont_diff,
    exact is_bounded_linear_map.add is_bounded_linear_map.fst is_bounded_linear_map.snd },
  exact this.comp (hf.prod hg)
end

/-- The negative of a `C^n`function on a domain is `C^n`. -/
lemma times_cont_diff_on.neg {n : with_top ℕ} {s : set E} {f : E → F}
  (hf : times_cont_diff_on 𝕜 n f s) : times_cont_diff_on 𝕜 n (λx, -f x) s :=
begin
  have : times_cont_diff 𝕜 n (λp : F, -p),
  { apply is_bounded_linear_map.times_cont_diff,
    exact is_bounded_linear_map.neg is_bounded_linear_map.id },
  exact this.comp_times_cont_diff_on hf
end

/-- The negative of a `C^n`function is `C^n`. -/
lemma times_cont_diff.neg {n : with_top ℕ} {f : E → F} (hf : times_cont_diff 𝕜 n f) :
  times_cont_diff 𝕜 n (λx, -f x) :=
begin
  have : times_cont_diff 𝕜 n (λp : F, -p),
  { apply is_bounded_linear_map.times_cont_diff,
    exact is_bounded_linear_map.neg is_bounded_linear_map.id },
  exact this.comp hf
end

/-- The difference of two `C^n`functions on a domain is `C^n`. -/
lemma times_cont_diff_on.sub {n : with_top ℕ} {s : set E} {f g : E → F}
  (hf : times_cont_diff_on 𝕜 n f s) (hg : times_cont_diff_on 𝕜 n g s) :
  times_cont_diff_on 𝕜 n (λx, f x - g x) s :=
hf.add (hg.neg)

/-- The difference of two `C^n`functions is `C^n`. -/
lemma times_cont_diff.sub {n : with_top ℕ} {f g : E → F}
  (hf : times_cont_diff 𝕜 n f) (hg : times_cont_diff 𝕜 n g) :
  times_cont_diff 𝕜 n (λx, f x - g x) :=
hf.add hg.neg
