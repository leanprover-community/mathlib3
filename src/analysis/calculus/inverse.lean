/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov, Heather Macbeth, Sébastien Gouëzel
-/
import analysis.calculus.times_cont_diff
import analysis.normed_space.banach
import topology.local_homeomorph
import topology.metric_space.contracting
import tactic.ring_exp

/-!
# Inverse function theorem

In this file we prove the inverse function theorem. It says that if a map `f : E → F`
has an invertible strict derivative `f'` at `a`, then it is locally invertible,
and the inverse function has derivative `f' ⁻¹`.

We define `has_strict_deriv_at.to_local_homeomorph` that repacks a function `f`
with a `hf : has_strict_fderiv_at f f' a`, `f' : E ≃L[𝕜] F`, into a `local_homeomorph`.
The `to_fun` of this `local_homeomorph` is `defeq` to `f`, so one can apply theorems
about `local_homeomorph` to `hf.to_local_homeomorph f`, and get statements about `f`.

Then we define `has_strict_fderiv_at.local_inverse` to be the `inv_fun` of this `local_homeomorph`,
and prove two versions of the inverse function theorem:

* `has_strict_fderiv_at.to_local_inverse`: if `f` has an invertible derivative `f'` at `a` in the
  strict sense (`hf`), then `hf.local_inverse f f' a` has derivative `f'.symm` at `f a` in the
  strict sense;

* `has_strict_fderiv_at.to_local_left_inverse`: if `f` has an invertible derivative `f'` at `a` in
  the strict sense and `g` is locally left inverse to `f` near `a`, then `g` has derivative
  `f'.symm` at `f a` in the strict sense.

In the one-dimensional case we reformulate these theorems in terms of `has_strict_deriv_at` and
`f'⁻¹`.

We also reformulate the theorems in terms of `times_cont_diff`, to give that `C^k` (respectively,
smooth) inputs give `C^k` (smooth) inverses.  These versions require that continuous
differentiability implies strict differentiability; this is false over a general field, true over
`ℝ` or `ℂ` and implemented here assuming `is_R_or_C 𝕂`.

Some related theorems, providing the derivative and higher regularity assuming that we already know
the inverse function, are formulated in `fderiv.lean`, `deriv.lean`, and `times_cont_diff.lean`.

## Notations

In the section about `approximates_linear_on` we introduce some `local notation` to make formulas
shorter:

* by `N` we denote `∥f'⁻¹∥`;
* by `g` we denote the auxiliary contracting map `x ↦ x + f'.symm (y - f x)` used to prove that
  `{x | f x = y}` is nonempty.

## Tags

derivative, strictly differentiable, continuously differentiable, smooth, inverse function
-/

open function set filter metric
open_locale topological_space classical nnreal

noncomputable theory

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
variables {E : Type*} [normed_group E] [normed_space 𝕜 E]
variables {F : Type*} [normed_group F] [normed_space 𝕜 F]
variables {G : Type*} [normed_group G] [normed_space 𝕜 G]
variables {G' : Type*} [normed_group G'] [normed_space 𝕜 G']
variables {ε : ℝ}


open asymptotics filter metric set
open continuous_linear_map (id)


/-!
### Non-linear maps close to affine maps

In this section we study a map `f` such that `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` on an open set
`s`, where `f' : E →L[𝕜] F` is a continuous linear map and `c` is suitably small. Maps of this type
behave like `f a + f' (x - a)` near each `a ∈ s`.

When `f'` is onto, we show that `f` is locally onto.

When `f'` is a continuous linear equiv, we show that `f` is a homeomorphism
between `s` and `f '' s`. More precisely, we define `approximates_linear_on.to_local_homeomorph` to
be a `local_homeomorph` with `to_fun = f`, `source = s`, and `target = f '' s`.

Maps of this type naturally appear in the proof of the inverse function theorem (see next section),
and `approximates_linear_on.to_local_homeomorph` will imply that the locally inverse function
exists.

We define this auxiliary notion to split the proof of the inverse function theorem into small
lemmas. This approach makes it possible

- to prove a lower estimate on the size of the domain of the inverse function;

- to reuse parts of the proofs in the case if a function is not strictly differentiable. E.g., for a
  function `f : E × F → G` with estimates on `f x y₁ - f x y₂` but not on `f x₁ y - f x₂ y`.
-/

/-- We say that `f` approximates a continuous linear map `f'` on `s` with constant `c`,
if `∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥` whenever `x, y ∈ s`.

This predicate is defined to facilitate the splitting of the inverse function theorem into small
lemmas. Some of these lemmas can be useful, e.g., to prove that the inverse function is defined
on a specific set. -/
def approximates_linear_on (f : E → F) (f' : E →L[𝕜] F) (s : set E) (c : ℝ≥0) : Prop :=
∀ (x ∈ s) (y ∈ s), ∥f x - f y - f' (x - y)∥ ≤ c * ∥x - y∥

namespace approximates_linear_on

variables [cs : complete_space E] {f : E → F}

/-! First we prove some properties of a function that `approximates_linear_on` a (not necessarily
invertible) continuous linear map. -/

section

variables {f' : E →L[𝕜] F} {s t : set E} {c c' : ℝ≥0}

theorem mono_num (hc : c ≤ c') (hf : approximates_linear_on f f' s c) :
  approximates_linear_on f f' s c' :=
λ x hx y hy, le_trans (hf x hx y hy) (mul_le_mul_of_nonneg_right hc $ norm_nonneg _)

theorem mono_set (hst : s ⊆ t) (hf : approximates_linear_on f f' t c) :
  approximates_linear_on f f' s c :=
λ x hx y hy, hf x (hst hx) y (hst hy)

lemma lipschitz_sub (hf : approximates_linear_on f f' s c) :
  lipschitz_with c (λ x : s, f x - f' x) :=
begin
  refine lipschitz_with.of_dist_le_mul (λ x y, _),
  rw [dist_eq_norm, subtype.dist_eq, dist_eq_norm],
  convert hf x x.2 y y.2 using 2,
  rw [f'.map_sub], abel
end

protected lemma lipschitz (hf : approximates_linear_on f f' s c) :
  lipschitz_with (nnnorm f' + c) (s.restrict f) :=
by simpa only [restrict_apply, add_sub_cancel'_right]
  using (f'.lipschitz.restrict s).add hf.lipschitz_sub

protected lemma continuous (hf : approximates_linear_on f f' s c) :
  continuous (s.restrict f) :=
hf.lipschitz.continuous

protected lemma continuous_on (hf : approximates_linear_on f f' s c) :
  continuous_on f s :=
continuous_on_iff_continuous_restrict.2 hf.continuous

end

section locally_onto
/-!
We prove that a function which is linearly approximated by a continuous linear map with a nonlinear
right inverse is locally onto. This will apply to the case where the approximating map is a linear
equivalence, for the local inverse theorem, but also whenever the approximating map is onto,
by Banach's open mapping theorem. -/

include cs

variables {s : set E} {c : ℝ≥0} {f' : E →L[𝕜] F}

/-- If a function is linearly approximated by a continuous linear map with a (possibly nonlinear)
right inverse, then it is locally onto: a ball of an explicit radius is included in the image
of the map. -/
theorem surj_on_closed_ball_of_nonlinear_right_inverse
  (hf : approximates_linear_on f f' s c)  (f'symm : f'.nonlinear_right_inverse)
  {ε : ℝ} {b : E} (ε0 : 0 ≤ ε) (hε : closed_ball b ε ⊆ s) :
  surj_on f (closed_ball b ε) (closed_ball (f b) (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε)) :=
begin
  assume y hy,
  cases le_or_lt (f'symm.nnnorm : ℝ) ⁻¹ c with hc hc,
  { refine ⟨b, by simp [ε0], _⟩,
    have : dist y (f b) ≤ 0 :=
      (mem_closed_ball.1 hy).trans (mul_nonpos_of_nonpos_of_nonneg (by linarith) ε0),
    simp only [dist_le_zero] at this,
    rw this },
  have If' : (0 : ℝ) < f'symm.nnnorm,
    by { rw [← inv_pos], exact (nnreal.coe_nonneg _).trans_lt hc },
  have Icf' : (c : ℝ) * f'symm.nnnorm < 1, by rwa [inv_eq_one_div, lt_div_iff If'] at hc,
  have Jf' : (f'symm.nnnorm : ℝ) ≠ 0 := ne_of_gt If',
  have Jcf' : (1 : ℝ) - c * f'symm.nnnorm ≠ 0, by { apply ne_of_gt, linarith },
  /- We have to show that `y` can be written as `f x` for some `x ∈ closed_ball b ε`.
  The idea of the proof is to apply the Banach contraction principle to the map
  `g : x ↦ x + f'symm (y - f x)`, as a fixed point of this map satisfies `f x = y`.
  When `f'symm` is a genuine linear inverse, `g` is a contracting map. In our case, since `f'symm`
  is nonlinear, this map is not contracting (it is not even continuous), but still the proof of
  the contraction theorem holds: `uₙ = gⁿ b` is a Cauchy sequence, converging exponentially fast
  to the desired point `x`. Instead of appealing to general results, we check this by hand.

  The main point is that `f (u n)` becomes exponentially close to `y`, and therefore
  `dist (u (n+1)) (u n)` becomes exponentally small, making it possible to get an inductive
  bound on `dist (u n) b`, from which one checks that `u n` stays in the ball on which one has a
  control. Therefore, the bound can be checked at the next step, and so on inductively.
  -/
  set g := λ x, x + f'symm (y - f x) with hg,
  set u := λ (n : ℕ), g ^[n] b with hu,
  have usucc : ∀ n, u (n + 1) = g (u n), by simp [hu, ← iterate_succ_apply' g _ b],
  -- First bound: if `f z` is close to `y`, then `g z` is close to `z` (i.e., almost a fixed point).
  have A : ∀ z, dist (g z) z ≤ f'symm.nnnorm * dist (f z) y,
  { assume z,
    rw [dist_eq_norm, hg, add_sub_cancel', dist_eq_norm'],
    exact f'symm.bound _ },
  -- Second bound: if `z` and `g z` are in the set with good control, then `f (g z)` becomes closer
  -- to `y` than `f z` was (this uses the linear approximation property, and is the reason for the
  -- choice of the formula for `g`).
  have B : ∀ z ∈ closed_ball b ε, g z ∈ closed_ball b ε →
    dist (f (g z)) y ≤ c * f'symm.nnnorm * dist (f z) y,
  { assume z hz hgz,
    set v := f'symm (y - f z) with hv,
    calc dist (f (g z)) y = ∥f (z + v) - y∥ : by rw [dist_eq_norm]
    ... = ∥f (z + v) - f  z - f' v + f' v - (y - f z)∥ : by { congr' 1, abel }
    ... = ∥f (z + v) - f z - f' ((z + v) - z)∥ :
      by simp only [continuous_linear_map.nonlinear_right_inverse.right_inv,
                    add_sub_cancel', sub_add_cancel]
    ... ≤ c * ∥(z + v) - z∥ : hf _ (hε hgz) _ (hε hz)
    ... ≤ c * (f'symm.nnnorm * dist (f z) y) : begin
      apply mul_le_mul_of_nonneg_left _ (nnreal.coe_nonneg c),
      simpa [hv, dist_eq_norm'] using f'symm.bound (y - f z),
    end
    ... = c * f'symm.nnnorm * dist (f z) y : by ring },
  -- Third bound: a complicated bound on `dist w b` (that will show up in the induction) is enough
  -- to check that `w` is in the ball on which one has controls. Will be used to check that `u n`
  -- belongs to this ball for all `n`.
  have C : ∀ (n : ℕ) (w : E),
    dist w b ≤ f'symm.nnnorm * (1 - (c * f'symm.nnnorm)^n) / (1 - c * f'symm.nnnorm) * dist (f b) y
    → w ∈ closed_ball b ε,
  { assume n w hw,
    apply hw.trans,
    rw [div_mul_eq_mul_div, div_le_iff], swap, { linarith },
    calc (f'symm.nnnorm : ℝ) * (1 - (c * f'symm.nnnorm) ^ n) * dist (f b) y
      = f'symm.nnnorm * dist (f b) y * (1 - (c * f'symm.nnnorm) ^ n) : by ring
      ... ≤ f'symm.nnnorm * dist (f b) y * 1 :
      begin
        apply mul_le_mul_of_nonneg_left _ (mul_nonneg (nnreal.coe_nonneg _) dist_nonneg),
        rw [sub_le_self_iff],
        exact pow_nonneg (mul_nonneg (nnreal.coe_nonneg _) (nnreal.coe_nonneg _)) _,
      end
    ... ≤ f'symm.nnnorm * (((f'symm.nnnorm : ℝ)⁻¹ - c) * ε) :
      by { rw [mul_one],
           exact mul_le_mul_of_nonneg_left (mem_closed_ball'.1 hy) (nnreal.coe_nonneg _) }
    ... = ε * (1 - c * f'symm.nnnorm) : by { field_simp, ring } },
  /- Main inductive control: `f (u n)` becomes exponentially close to `y`, and therefore
  `dist (u (n+1)) (u n)` becomes exponentally small, making it possible to get an inductive
  bound on `dist (u n) b`, from which one checks that `u n` remains in the ball on which we
  have estimates. -/
  have D : ∀ (n : ℕ), dist (f (u n)) y ≤ (c * f'symm.nnnorm)^n * dist (f b) y
    ∧ dist (u n) b ≤ f'symm.nnnorm * (1 - (c * f'symm.nnnorm)^n) / (1 - c * f'symm.nnnorm)
      * dist (f b) y,
  { assume n,
    induction n with n IH, { simp [hu, le_refl] },
    rw usucc,
    have Ign : dist (g (u n)) b ≤
      f'symm.nnnorm * (1 - (c * f'symm.nnnorm)^n.succ) / (1 - c * f'symm.nnnorm) * dist (f b) y :=
    calc
      dist (g (u n)) b ≤ dist (g (u n)) (u n) + dist (u n) b : dist_triangle _ _ _
      ... ≤ f'symm.nnnorm * dist (f (u n)) y + dist (u n) b : add_le_add (A _) (le_refl _)
      ... ≤ f'symm.nnnorm * ((c * f'symm.nnnorm)^n * dist (f b) y) +
        f'symm.nnnorm * (1 - (c * f'symm.nnnorm)^n) / (1 - c * f'symm.nnnorm) * dist (f b) y :
          add_le_add (mul_le_mul_of_nonneg_left IH.1 (nnreal.coe_nonneg _)) IH.2
      ... = f'symm.nnnorm * (1 - (c * f'symm.nnnorm)^n.succ) / (1 - c * f'symm.nnnorm)
        * dist (f b) y : by { field_simp [Jcf'], ring_exp },
    refine ⟨_, Ign⟩,
    calc dist (f (g (u n))) y ≤ c * f'symm.nnnorm * dist (f (u n)) y :
      B _ (C n _ IH.2) (C n.succ _ Ign)
    ... ≤ (c * f'symm.nnnorm) * ((c * f'symm.nnnorm)^n * dist (f b) y) :
      mul_le_mul_of_nonneg_left IH.1 (mul_nonneg (nnreal.coe_nonneg _) (nnreal.coe_nonneg _))
    ... = (c * f'symm.nnnorm) ^ n.succ * dist (f b) y : by ring_exp },
  -- Deduce from the inductive bound that `uₙ` is a Cauchy sequence, therefore converging.
  have : cauchy_seq u,
  { have : ∀ (n : ℕ), dist (u n) (u (n+1)) ≤ f'symm.nnnorm * dist (f b) y * (c * f'symm.nnnorm)^n,
    { assume n,
      calc dist (u n) (u (n+1)) = dist (g (u n)) (u n) :  by rw [usucc, dist_comm]
      ... ≤ f'symm.nnnorm * dist (f (u n)) y : A _
      ... ≤ f'symm.nnnorm * ((c * f'symm.nnnorm)^n * dist (f b) y) :
        mul_le_mul_of_nonneg_left (D n).1 (nnreal.coe_nonneg _)
      ... = f'symm.nnnorm * dist (f b) y * (c * f'symm.nnnorm)^n : by ring },
    exact cauchy_seq_of_le_geometric _ _ Icf' this },
  obtain ⟨x, hx⟩ : ∃ x, tendsto u at_top (𝓝 x) := cauchy_seq_tendsto_of_complete this,
  -- As all the `uₙ` belong to the ball `closed_ball b ε`, so does their limit `x`.
  have xmem : x ∈ closed_ball b ε :=
    is_closed_ball.mem_of_tendsto hx (eventually_of_forall (λ n, C n _ (D n).2)),
  refine ⟨x, xmem, _⟩,
  -- It remains to check that `f x = y`. This follows from continuity of `f` on `closed_ball b ε`
  -- and from the fact that `f uₙ` is converging to `y` by construction.
  have hx' : tendsto u at_top (𝓝[closed_ball b ε] x),
  { simp only [nhds_within, tendsto_inf, hx, true_and, ge_iff_le, tendsto_principal],
    exact eventually_of_forall (λ n, C n _ (D n).2) },
  have T1 : tendsto (λ n, f (u n)) at_top (𝓝 (f x)) :=
    (hf.continuous_on.mono hε x xmem).tendsto.comp hx',
  have T2 : tendsto (λ n, f (u n)) at_top (𝓝 y),
  { rw tendsto_iff_dist_tendsto_zero,
    refine squeeze_zero (λ n, dist_nonneg) (λ n, (D n).1) _,
    simpa using (tendsto_pow_at_top_nhds_0_of_lt_1
      (mul_nonneg (nnreal.coe_nonneg _) (nnreal.coe_nonneg _)) Icf').mul tendsto_const_nhds },
  exact tendsto_nhds_unique T1 T2,
end

lemma open_image (hf : approximates_linear_on f f' s c)  (f'symm : f'.nonlinear_right_inverse)
  (hs : is_open s) (hc : subsingleton F ∨ c < f'symm.nnnorm⁻¹) : is_open (f '' s) :=
begin
  cases hc with hE hc, { resetI, apply is_open_discrete },
  simp only [is_open_iff_mem_nhds, nhds_basis_closed_ball.mem_iff, ball_image_iff] at hs ⊢,
  intros x hx,
  rcases hs x hx with ⟨ε, ε0, hε⟩,
  refine ⟨(f'symm.nnnorm⁻¹ - c) * ε, mul_pos (sub_pos.2 hc) ε0, _⟩,
  exact (hf.surj_on_closed_ball_of_nonlinear_right_inverse f'symm (le_of_lt ε0) hε).mono
    hε (subset.refl _)
end

lemma image_mem_nhds (hf : approximates_linear_on f f' s c) (f'symm : f'.nonlinear_right_inverse)
  {x : E} (hs : s ∈ 𝓝 x) (hc : subsingleton F ∨ c < f'symm.nnnorm⁻¹) :
  f '' s ∈ 𝓝 (f x) :=
begin
  obtain ⟨t, hts, ht, xt⟩ : ∃ t ⊆ s, is_open t ∧ x ∈ t := _root_.mem_nhds_iff.1 hs,
  have := is_open.mem_nhds ((hf.mono_set hts).open_image f'symm ht hc) (mem_image_of_mem _ xt),
  exact mem_of_superset this (image_subset _ hts),
end

lemma map_nhds_eq (hf : approximates_linear_on f f' s c) (f'symm : f'.nonlinear_right_inverse)
  {x : E} (hs : s ∈ 𝓝 x) (hc : subsingleton F ∨ c < f'symm.nnnorm⁻¹) :
  map f (𝓝 x) = 𝓝 (f x) :=
begin
  refine le_antisymm ((hf.continuous_on x (mem_of_mem_nhds hs)).continuous_at hs)
    (le_map (λ t ht, _)),
  have : f '' (s ∩ t) ∈ 𝓝 (f x) := (hf.mono_set (inter_subset_left s t)).image_mem_nhds
    f'symm (inter_mem hs ht) hc,
  exact mem_of_superset this (image_subset _ (inter_subset_right _ _)),
end

end locally_onto

/-!
From now on we assume that `f` approximates an invertible continuous linear map `f : E ≃L[𝕜] F`.

We also assume that either `E = {0}`, or `c < ∥f'⁻¹∥⁻¹`. We use `N` as an abbreviation for `∥f'⁻¹∥`.
-/

variables {f' : E ≃L[𝕜] F} {s : set E} {c : ℝ≥0}

local notation `N` := nnnorm (f'.symm : F →L[𝕜] E)

protected lemma antilipschitz (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) :
  antilipschitz_with (N⁻¹ - c)⁻¹ (s.restrict f) :=
begin
  cases hc with hE hc,
  { haveI : subsingleton s := ⟨λ x y, subtype.eq $ @subsingleton.elim _ hE _ _⟩,
    exact antilipschitz_with.of_subsingleton },
  convert (f'.antilipschitz.restrict s).add_lipschitz_with hf.lipschitz_sub hc,
  simp [restrict]
end

protected lemma injective (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) :
  injective (s.restrict f) :=
(hf.antilipschitz hc).injective

protected lemma inj_on (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) :
  inj_on f s :=
inj_on_iff_injective.2 $ hf.injective hc

/-- A map approximating a linear equivalence on a set defines a local equivalence on this set.
Should not be used outside of this file, because it is superseded by `to_local_homeomorph` below.

This is a first step towards the inverse function. -/
def to_local_equiv (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) : local_equiv E F :=
(hf.inj_on hc).to_local_equiv _ _

/-- The inverse function is continuous on `f '' s`. Use properties of `local_homeomorph` instead. -/
lemma inverse_continuous_on (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) :
  continuous_on (hf.to_local_equiv hc).symm (f '' s) :=
begin
  apply continuous_on_iff_continuous_restrict.2,
  refine ((hf.antilipschitz hc).to_right_inv_on' _ (hf.to_local_equiv hc).right_inv').continuous,
  exact (λ x hx, (hf.to_local_equiv hc).map_target hx)
end

include cs

section
variables (f s)

/-- Given a function `f` that approximates a linear equivalence on an open set `s`,
returns a local homeomorph with `to_fun = f` and `source = s`. -/
def to_local_homeomorph (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) (hs : is_open s) : local_homeomorph E F :=
{ to_local_equiv := hf.to_local_equiv hc,
  open_source := hs,
  open_target := hf.open_image f'.to_nonlinear_right_inverse hs
    (by rwa f'.to_linear_equiv.to_equiv.subsingleton_congr at hc),
  continuous_to_fun := hf.continuous_on,
  continuous_inv_fun := hf.inverse_continuous_on hc }

end

@[simp] lemma to_local_homeomorph_coe (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) (hs : is_open s) :
  (hf.to_local_homeomorph f s hc hs : E → F) = f := rfl

@[simp] lemma to_local_homeomorph_source (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) (hs : is_open s) :
  (hf.to_local_homeomorph f s hc hs).source = s := rfl

@[simp] lemma to_local_homeomorph_target (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) (hs : is_open s) :
  (hf.to_local_homeomorph f s hc hs).target = f '' s := rfl

lemma closed_ball_subset_target (hf : approximates_linear_on f (f' : E →L[𝕜] F) s c)
  (hc : subsingleton E ∨ c < N⁻¹) (hs : is_open s) {b : E} (ε0 : 0 ≤ ε) (hε : closed_ball b ε ⊆ s) :
  closed_ball (f b) ((N⁻¹ - c) * ε) ⊆ (hf.to_local_homeomorph f s hc hs).target :=
(hf.surj_on_closed_ball_of_nonlinear_right_inverse f'.to_nonlinear_right_inverse
  ε0 hε).mono hε (subset.refl _)

end approximates_linear_on

/-!
### Inverse function theorem

Now we prove the inverse function theorem. Let `f : E → F` be a map defined on a complete vector
space `E`. Assume that `f` has an invertible derivative `f' : E ≃L[𝕜] F` at `a : E` in the strict
sense. Then `f` approximates `f'` in the sense of `approximates_linear_on` on an open neighborhood
of `a`, and we can apply `approximates_linear_on.to_local_homeomorph` to construct the inverse
function. -/

namespace has_strict_fderiv_at

/-- If `f` has derivative `f'` at `a` in the strict sense and `c > 0`, then `f` approximates `f'`
with constant `c` on some neighborhood of `a`. -/
lemma approximates_deriv_on_nhds {f : E → F} {f' : E →L[𝕜] F} {a : E}
  (hf : has_strict_fderiv_at f f' a) {c : ℝ≥0} (hc : subsingleton E ∨ 0 < c) :
  ∃ s ∈ 𝓝 a, approximates_linear_on f f' s c :=
begin
  cases hc with hE hc,
  { refine ⟨univ, is_open.mem_nhds is_open_univ trivial, λ x hx y hy, _⟩,
    simp [@subsingleton.elim E hE x y] },
  have := hf.def hc,
  rw [nhds_prod_eq, filter.eventually, mem_prod_same_iff] at this,
  rcases this with ⟨s, has, hs⟩,
  exact ⟨s, has, λ x hx y hy, hs (mk_mem_prod hx hy)⟩
end

lemma map_nhds_eq_of_surj [complete_space E] [complete_space F]
  {f : E → F} {f' : E →L[𝕜] F} {a : E}
  (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) (h : f'.range = ⊤) :
  map f (𝓝 a) = 𝓝 (f a) :=
begin
  let f'symm := f'.nonlinear_right_inverse_of_surjective h,
  set c : ℝ≥0 := f'symm.nnnorm⁻¹ / 2 with hc,
  have f'symm_pos : 0 < f'symm.nnnorm := f'.nonlinear_right_inverse_of_surjective_nnnorm_pos h,
  have cpos : 0 < c, by simp [hc, nnreal.half_pos, nnreal.inv_pos, f'symm_pos],
  obtain ⟨s, s_nhds, hs⟩ : ∃ s ∈ 𝓝 a, approximates_linear_on f f' s c :=
    hf.approximates_deriv_on_nhds (or.inr cpos),
  apply hs.map_nhds_eq f'symm s_nhds (or.inr (nnreal.half_lt_self _)),
  simp [ne_of_gt f'symm_pos],
end

variables [cs : complete_space E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

lemma approximates_deriv_on_open_nhds (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∃ (s : set E) (hs : a ∈ s ∧ is_open s),
    approximates_linear_on f (f' : E →L[𝕜] F) s ((nnnorm (f'.symm : F →L[𝕜] E))⁻¹ / 2) :=
begin
  refine ((nhds_basis_opens a).exists_iff _).1 _,
  exact (λ s t, approximates_linear_on.mono_set),
  exact (hf.approximates_deriv_on_nhds $ f'.subsingleton_or_nnnorm_symm_pos.imp id $
    λ hf', nnreal.half_pos $ nnreal.inv_pos.2 $ hf')
end

include cs

variable (f)

/-- Given a function with an invertible strict derivative at `a`, returns a `local_homeomorph`
with `to_fun = f` and `a ∈ source`. This is a part of the inverse function theorem.
The other part `has_strict_fderiv_at.to_local_inverse` states that the inverse function
of this `local_homeomorph` has derivative `f'.symm`. -/
def to_local_homeomorph (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) : local_homeomorph E F :=
approximates_linear_on.to_local_homeomorph f
  (classical.some hf.approximates_deriv_on_open_nhds)
  (classical.some_spec hf.approximates_deriv_on_open_nhds).snd
  (f'.subsingleton_or_nnnorm_symm_pos.imp id $ λ hf', nnreal.half_lt_self $ ne_of_gt $
    nnreal.inv_pos.2 $ hf')
  (classical.some_spec hf.approximates_deriv_on_open_nhds).fst.2

variable {f}

@[simp] lemma to_local_homeomorph_coe (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  (hf.to_local_homeomorph f : E → F) = f := rfl

lemma mem_to_local_homeomorph_source (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  a ∈ (hf.to_local_homeomorph f).source :=
(classical.some_spec hf.approximates_deriv_on_open_nhds).fst.1

lemma image_mem_to_local_homeomorph_target (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  f a ∈ (hf.to_local_homeomorph f).target :=
(hf.to_local_homeomorph f).map_source hf.mem_to_local_homeomorph_source

lemma map_nhds_eq_of_equiv (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  map f (𝓝 a) = 𝓝 (f a) :=
(hf.to_local_homeomorph f).map_nhds_eq hf.mem_to_local_homeomorph_source

variables (f f' a)

/-- Given a function `f` with an invertible derivative, returns a function that is locally inverse
to `f`. -/
def local_inverse (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) : F → E :=
(hf.to_local_homeomorph f).symm

variables {f f' a}

lemma local_inverse_def (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  hf.local_inverse f _ _ = (hf.to_local_homeomorph f).symm :=
rfl

lemma eventually_left_inverse (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∀ᶠ x in 𝓝 a, hf.local_inverse f f' a (f x) = x :=
(hf.to_local_homeomorph f).eventually_left_inverse hf.mem_to_local_homeomorph_source

@[simp] lemma local_inverse_apply_image (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  hf.local_inverse f f' a (f a) = a :=
hf.eventually_left_inverse.self_of_nhds

lemma eventually_right_inverse (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  ∀ᶠ y in 𝓝 (f a), f (hf.local_inverse f f' a y) = y :=
(hf.to_local_homeomorph f).eventually_right_inverse' hf.mem_to_local_homeomorph_source

lemma local_inverse_continuous_at (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  continuous_at (hf.local_inverse f f' a) (f a) :=
(hf.to_local_homeomorph f).continuous_at_symm hf.image_mem_to_local_homeomorph_target

lemma local_inverse_tendsto (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  tendsto (hf.local_inverse f f' a) (𝓝 $ f a) (𝓝 a) :=
(hf.to_local_homeomorph f).tendsto_symm hf.mem_to_local_homeomorph_source

lemma local_inverse_unique (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) {g : F → E}
  (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
  ∀ᶠ y in 𝓝 (f a), g y = local_inverse f f' a hf y :=
eventually_eq_of_left_inv_of_right_inv hg hf.eventually_right_inverse $
  (hf.to_local_homeomorph f).tendsto_symm hf.mem_to_local_homeomorph_source

/-- If `f` has an invertible derivative `f'` at `a` in the sense of strict differentiability `(hf)`,
then the inverse function `hf.local_inverse f` has derivative `f'.symm` at `f a`. -/
theorem to_local_inverse (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) :
  has_strict_fderiv_at (hf.local_inverse f f' a) (f'.symm : F →L[𝕜] E) (f a) :=
(hf.to_local_homeomorph f).has_strict_fderiv_at_symm hf.image_mem_to_local_homeomorph_target $
  by simpa [← local_inverse_def] using hf

/-- If `f : E → F` has an invertible derivative `f'` at `a` in the sense of strict differentiability
and `g (f x) = x` in a neighborhood of `a`, then `g` has derivative `f'.symm` at `f a`.

For a version assuming `f (g y) = y` and continuity of `g` at `f a` but not `[complete_space E]`
see `of_local_left_inverse`.  -/
theorem to_local_left_inverse (hf : has_strict_fderiv_at f (f' : E →L[𝕜] F) a) {g : F → E}
  (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
  has_strict_fderiv_at g (f'.symm : F →L[𝕜] E) (f a) :=
hf.to_local_inverse.congr_of_eventually_eq $ (hf.local_inverse_unique hg).mono $ λ _, eq.symm

end has_strict_fderiv_at

/-- If a function has an invertible strict derivative at all points, then it is an open map. -/
lemma open_map_of_strict_fderiv_equiv [complete_space E] {f : E → F} {f' : E → E ≃L[𝕜] F}
  (hf : ∀ x, has_strict_fderiv_at f (f' x : E →L[𝕜] F) x) :
  is_open_map f :=
is_open_map_iff_nhds_le.2 $ λ x, (hf x).map_nhds_eq_of_equiv.ge

/-!
### Inverse function theorem, 1D case

In this case we prove a version of the inverse function theorem for maps `f : 𝕜 → 𝕜`.
We use `continuous_linear_equiv.units_equiv_aut` to translate `has_strict_deriv_at f f' a` and
`f' ≠ 0` into `has_strict_fderiv_at f (_ : 𝕜 ≃L[𝕜] 𝕜) a`.
-/

namespace has_strict_deriv_at

variables [cs : complete_space 𝕜] {f : 𝕜 → 𝕜} {f' a : 𝕜} (hf : has_strict_deriv_at f f' a)
  (hf' : f' ≠ 0)

include cs

variables (f f' a)

/-- A function that is inverse to `f` near `a`. -/
@[reducible] def local_inverse : 𝕜 → 𝕜 :=
(hf.has_strict_fderiv_at_equiv hf').local_inverse _ _ _

variables {f f' a}

lemma map_nhds_eq : map f (𝓝 a) = 𝓝 (f a) :=
(hf.has_strict_fderiv_at_equiv hf').map_nhds_eq_of_equiv

theorem to_local_inverse : has_strict_deriv_at (hf.local_inverse f f' a hf') f'⁻¹ (f a) :=
(hf.has_strict_fderiv_at_equiv hf').to_local_inverse

theorem to_local_left_inverse {g : 𝕜 → 𝕜} (hg : ∀ᶠ x in 𝓝 a, g (f x) = x) :
  has_strict_deriv_at g f'⁻¹ (f a) :=
(hf.has_strict_fderiv_at_equiv hf').to_local_left_inverse hg

end has_strict_deriv_at

/-- If a function has a non-zero strict derivative at all points, then it is an open map. -/
lemma open_map_of_strict_deriv [complete_space 𝕜] {f f' : 𝕜 → 𝕜}
  (hf : ∀ x, has_strict_deriv_at f (f' x) x) (h0 : ∀ x, f' x ≠ 0) :
  is_open_map f :=
is_open_map_iff_nhds_le.2 $ λ x, ((hf x).map_nhds_eq (h0 x)).ge

/-!
### Inverse function theorem, smooth case

-/

namespace times_cont_diff_at
variables {𝕂 : Type*} [is_R_or_C 𝕂]
variables {E' : Type*} [normed_group E'] [normed_space 𝕂 E']
variables {F' : Type*} [normed_group F'] [normed_space 𝕂 F']
variables [complete_space E'] (f : E' → F') {f' : E' ≃L[𝕂] F'} {a : E'}

/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible
derivative at `a`, returns a `local_homeomorph` with `to_fun = f` and `a ∈ source`. -/
def to_local_homeomorph
  {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) :
  local_homeomorph E' F' :=
(hf.has_strict_fderiv_at' hf' hn).to_local_homeomorph f

variable {f}

@[simp] lemma to_local_homeomorph_coe
  {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) :
  (hf.to_local_homeomorph f hf' hn : E' → F') = f := rfl

lemma mem_to_local_homeomorph_source
  {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) :
  a ∈ (hf.to_local_homeomorph f hf' hn).source :=
(hf.has_strict_fderiv_at' hf' hn).mem_to_local_homeomorph_source

lemma image_mem_to_local_homeomorph_target
  {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) :
  f a ∈ (hf.to_local_homeomorph f hf' hn).target :=
(hf.has_strict_fderiv_at' hf' hn).image_mem_to_local_homeomorph_target

/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, returns a function that is locally inverse to `f`. -/
def local_inverse
  {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) :
  F' → E' :=
(hf.has_strict_fderiv_at' hf' hn).local_inverse f f' a

lemma local_inverse_apply_image
  {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) :
  hf.local_inverse hf' hn (f a) = a :=
(hf.has_strict_fderiv_at' hf' hn).local_inverse_apply_image

/-- Given a `times_cont_diff` function over `𝕂` (which is `ℝ` or `ℂ`) with an invertible derivative
at `a`, the inverse function (produced by `times_cont_diff.to_local_homeomorph`) is
also `times_cont_diff`. -/
lemma to_local_inverse
  {n : with_top ℕ} (hf : times_cont_diff_at 𝕂 n f a) (hf' : has_fderiv_at f (f' : E' →L[𝕂] F') a)
  (hn : 1 ≤ n) :
  times_cont_diff_at 𝕂 n (hf.local_inverse hf' hn) (f a) :=
begin
  have := hf.local_inverse_apply_image hf' hn,
  apply (hf.to_local_homeomorph f hf' hn).times_cont_diff_at_symm
    (image_mem_to_local_homeomorph_target hf hf' hn),
  { convert hf' },
  { convert hf }
end

end times_cont_diff_at
