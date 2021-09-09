/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import geometry.manifold.mfderiv
import geometry.manifold.local_invariant_properties

/-!
# Smooth functions between smooth manifolds

We define `Cⁿ` functions between smooth manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions.

## Main definitions and statements

Let `M ` and `M'` be two smooth manifolds, with respect to model with corners `I` and `I'`. Let
`f : M → M'`.

* `times_cont_mdiff_within_at I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `times_cont_mdiff_at I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `times_cont_mdiff_on I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `times_cont_mdiff I I' n f` states that the function `f` is `Cⁿ`.
* `times_cont_mdiff_on.comp` gives the invariance of the `Cⁿ` property under composition
* `times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within` states that the bundled derivative
  of a `Cⁿ` function in a domain is `Cᵐ` when `m + 1 ≤ n`.
* `times_cont_mdiff.times_cont_mdiff_tangent_map` states that the bundled derivative
  of a `Cⁿ` function is `Cᵐ` when `m + 1 ≤ n`.
* `times_cont_mdiff_iff_times_cont_diff` states that, for functions between vector spaces,
  manifold-smoothness is equivalent to usual smoothness.

We also give many basic properties of smooth functions between manifolds, following the API of
smooth functions between vector spaces.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the smooth groupoid. We take advantage of the
general machinery developed in `local_invariant_properties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `lift_prop_within_at_indep_chart`.

For this to work, the definition of `times_cont_mdiff_within_at` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `times_cont_mdiff_on_iff` and `times_cont_mdiff_iff`.
-/

open set function filter charted_space smooth_manifold_with_corners
open_locale topological_space manifold

/-! ### Definition of smooth functions between manifolds -/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- declare functions, sets, points and smoothness indices
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : with_top ℕ}

/-- Property in the model space of a model with corners of being `C^n` within at set at a point,
when read in the model vector space. This property will be lifted to manifolds to define smooth
functions between manifolds. -/
def times_cont_diff_within_at_prop (n : with_top ℕ) (f s x) : Prop :=
times_cont_diff_within_at 𝕜 n (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) (I x)

/-- Being `Cⁿ` in the model space is a local property, invariant under smooth maps. Therefore,
it will lift nicely to manifolds. -/
lemma times_cont_diff_within_at_local_invariant_prop (n : with_top ℕ) :
  (times_cont_diff_groupoid ∞ I).local_invariant_prop (times_cont_diff_groupoid ∞ I')
  (times_cont_diff_within_at_prop I I' n) :=
{ is_local :=
  begin
    assume s x u f u_open xu,
    have : range I ∩ I.symm ⁻¹' (s ∩ u) = (range I ∩ I.symm ⁻¹' s) ∩ I.symm ⁻¹' u,
      by simp only [inter_assoc, preimage_inter],
    rw [times_cont_diff_within_at_prop, times_cont_diff_within_at_prop, this],
    symmetry,
    apply times_cont_diff_within_at_inter,
    have : u ∈ 𝓝 (I.symm (I x)),
      by { rw [model_with_corners.left_inv], exact is_open.mem_nhds u_open xu },
    apply continuous_at.preimage_mem_nhds I.continuous_symm.continuous_at this,
  end,
  right_invariance :=
  begin
    assume s x f e he hx h,
    rw times_cont_diff_within_at_prop at h ⊢,
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)), by simp only [hx] with mfld_simps,
    rw this at h,
    have : I (e x) ∈ (I.symm) ⁻¹' e.target ∩ range ⇑I, by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he).2.times_cont_diff_within_at this).of_le le_top,
    convert h.comp' _ this using 1,
    { ext y, simp only with mfld_simps },
    { mfld_set_tac }
  end,
  congr :=
  begin
    assume s x f g h hx hf,
    apply hf.congr,
    { assume y hy,
      simp only with mfld_simps at hy,
      simp only [h, hy] with mfld_simps },
    { simp only [hx] with mfld_simps }
  end,
  left_invariance :=
  begin
    assume s x f e' he' hs hx h,
    rw times_cont_diff_within_at_prop at h ⊢,
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ (I'.symm ⁻¹' e'.source ∩ range I'),
      by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he').1.times_cont_diff_within_at A).of_le le_top,
    convert this.comp _ h _,
    { ext y, simp only with mfld_simps },
    { assume y hy, simp only with mfld_simps at hy, simpa only [hy] with mfld_simps using hs hy.2 }
  end }

lemma times_cont_diff_within_at_local_invariant_prop_mono (n : with_top ℕ)
  ⦃s x t⦄ ⦃f : H → H'⦄ (hts : t ⊆ s) (h : times_cont_diff_within_at_prop I I' n f s x) :
  times_cont_diff_within_at_prop I I' n f t x :=
begin
  apply h.mono (λ y hy, _),
  simp only with mfld_simps at hy,
  simp only [hy, hts _] with mfld_simps
end

lemma times_cont_diff_within_at_local_invariant_prop_id (x : H) :
  times_cont_diff_within_at_prop I I ∞ id univ x :=
begin
  simp [times_cont_diff_within_at_prop],
  have : times_cont_diff_within_at 𝕜 ∞ id (range I) (I x) :=
    times_cont_diff_id.times_cont_diff_at.times_cont_diff_within_at,
  apply this.congr (λ y hy, _),
  { simp only with mfld_simps },
  { simp only [model_with_corners.right_inv I hy] with mfld_simps }
end

/-- A function is `n` times continuously differentiable within a set at a point in a manifold if
it is continuous and it is `n` times continuously differentiable in this set around this point, when
read in the preferred chart at this point. -/
def times_cont_mdiff_within_at (n : with_top ℕ) (f : M → M') (s : set M) (x : M) :=
lift_prop_within_at (times_cont_diff_within_at_prop I I' n) f s x

/-- Abbreviation for `times_cont_mdiff_within_at I I' ⊤ f s x`. See also documentation for `smooth`.
-/
@[reducible] def smooth_within_at (f : M → M') (s : set M) (x : M) :=
  times_cont_mdiff_within_at I I' ⊤ f s x

/-- A function is `n` times continuously differentiable at a point in a manifold if
it is continuous and it is `n` times continuously differentiable around this point, when
read in the preferred chart at this point. -/
def times_cont_mdiff_at (n : with_top ℕ) (f : M → M') (x : M) :=
times_cont_mdiff_within_at I I' n f univ x

/-- Abbreviation for `times_cont_mdiff_at I I' ⊤ f x`. See also documentation for `smooth`. -/
@[reducible] def smooth_at (f : M → M') (x : M) := times_cont_mdiff_at I I' ⊤ f x

/-- A function is `n` times continuously differentiable in a set of a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable on this set in the charts
around these points. -/
def times_cont_mdiff_on (n : with_top ℕ) (f : M → M') (s : set M) :=
∀ x ∈ s, times_cont_mdiff_within_at I I' n f s x

/-- Abbreviation for `times_cont_mdiff_on I I' ⊤ f s`. See also documentation for `smooth`. -/
@[reducible] def smooth_on (f : M → M') (s : set M) := times_cont_mdiff_on I I' ⊤ f s

/-- A function is `n` times continuously differentiable in a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable in the charts
around these points. -/
def times_cont_mdiff (n : with_top ℕ) (f : M → M') :=
∀ x, times_cont_mdiff_at I I' n f x

/-- Abbreviation for `times_cont_mdiff I I' ⊤ f`.
Short note to work with these abbreviations: a lemma of the form `times_cont_mdiff_foo.bar` will
apply fine to an assumption `smooth_foo` using dot notation or normal notation.
If the consequence `bar` of the lemma involves `times_cont_diff`, it is still better to restate
the lemma replacing `times_cont_diff` with `smooth` both in the assumption and in the conclusion,
to make it possible to use `smooth` consistently.
This also applies to `smooth_at`, `smooth_on` and `smooth_within_at`.-/
@[reducible] def smooth (f : M → M') := times_cont_mdiff I I' ⊤ f

/-! ### Basic properties of smooth functions between manifolds -/

variables {I I'}

lemma times_cont_mdiff.smooth (h : times_cont_mdiff I I' ⊤ f) : smooth I I' f := h

lemma smooth.times_cont_mdiff (h : smooth I I' f) : times_cont_mdiff I I' ⊤ f := h

lemma times_cont_mdiff_on.smooth_on (h : times_cont_mdiff_on I I' ⊤ f s) : smooth_on I I' f s := h

lemma smooth_on.times_cont_mdiff_on (h : smooth_on I I' f s) : times_cont_mdiff_on I I' ⊤ f s := h

lemma times_cont_mdiff_at.smooth_at (h : times_cont_mdiff_at I I' ⊤ f x) : smooth_at I I' f x := h

lemma smooth_at.times_cont_mdiff_at (h : smooth_at I I' f x) : times_cont_mdiff_at I I' ⊤ f x := h

lemma times_cont_mdiff_within_at.smooth_within_at (h : times_cont_mdiff_within_at I I' ⊤ f s x) :
  smooth_within_at I I' f s x := h

lemma smooth_within_at.times_cont_mdiff_within_at (h : smooth_within_at I I' f s x) :
times_cont_mdiff_within_at I I' ⊤ f s x := h

lemma times_cont_mdiff.times_cont_mdiff_at (h : times_cont_mdiff I I' n f) :
  times_cont_mdiff_at I I' n f x :=
h x

lemma smooth.smooth_at (h : smooth I I' f) :
  smooth_at I I' f x := times_cont_mdiff.times_cont_mdiff_at h

lemma times_cont_mdiff_within_at_univ :
  times_cont_mdiff_within_at I I' n f univ x ↔ times_cont_mdiff_at I I' n f x :=
iff.rfl

lemma smooth_at_univ :
 smooth_within_at I I' f univ x ↔ smooth_at I I' f x := times_cont_mdiff_within_at_univ

lemma times_cont_mdiff_on_univ :
  times_cont_mdiff_on I I' n f univ ↔ times_cont_mdiff I I' n f :=
by simp only [times_cont_mdiff_on, times_cont_mdiff, times_cont_mdiff_within_at_univ,
  forall_prop_of_true, mem_univ]

lemma smooth_on_univ :
  smooth_on I I' f univ ↔ smooth I I' f := times_cont_mdiff_on_univ

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
lemma times_cont_mdiff_within_at_iff :
  times_cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    times_cont_diff_within_at 𝕜 n ((ext_chart_at I' (f x)) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩
      (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' (f x)).source))
    (ext_chart_at I x x) :=
begin
  rw [times_cont_mdiff_within_at, lift_prop_within_at, times_cont_diff_within_at_prop],
  congr' 3,
  mfld_set_tac
end

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. This form states smoothness of `f`
written in the `ext_chart_at`s within the set `(ext_chart_at I x).symm ⁻¹' s ∩ range I`. This set
is larger than the set
`(ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' (f x)).source)`
used in `times_cont_mdiff_within_at_iff` but their germs at `ext_chart_at I x x` are equal. It may
be useful to rewrite using `times_cont_mdiff_within_at_iff''` in the *assumptions* of a lemma and
using `times_cont_mdiff_within_at_iff` in the goal. -/
lemma times_cont_mdiff_within_at_iff'' :
  times_cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    times_cont_diff_within_at 𝕜 n (written_in_ext_chart_at I I' x f)
      ((ext_chart_at I x).symm ⁻¹' s ∩ range I) (ext_chart_at I x x) :=
begin
  rw [times_cont_mdiff_within_at_iff, and.congr_right_iff],
  set e := ext_chart_at I x, set e' := ext_chart_at I' (f x),
  refine λ hc, times_cont_diff_within_at_congr_nhds _,
  rw [← e.image_source_inter_eq', ← ext_chart_at_map_nhds_within_eq_image,
      ← ext_chart_at_map_nhds_within, inter_comm, nhds_within_inter_of_mem],
  exact hc (ext_chart_at_source_mem_nhds _ _)
end

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart in the target. -/
lemma times_cont_mdiff_within_at_iff_target :
  times_cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    times_cont_mdiff_within_at I 𝓘(𝕜, E') n ((ext_chart_at I' (f x)) ∘ f)
    (s ∩ f ⁻¹' (ext_chart_at I' (f x)).source) x :=
begin
  rw [times_cont_mdiff_within_at, times_cont_mdiff_within_at, lift_prop_within_at,
    lift_prop_within_at, ← and_assoc],
  have cont : (continuous_within_at f s x ∧
      continuous_within_at ((I' ∘ (chart_at H' (f x))) ∘ f)
      (s ∩ f ⁻¹' (chart_at H' (f x)).to_local_equiv.source) x) ↔
      continuous_within_at f s x,
  { refine ⟨λ h, h.1, λ h, ⟨h, _⟩⟩,
    have h₁ : continuous_within_at _ univ ((chart_at H' (f x)) (f x)),
    { exact (model_with_corners.continuous I').continuous_within_at },
    have h₂ := (chart_at H' (f x)).continuous_to_fun.continuous_within_at (mem_chart_source _ _),
    convert (h₁.comp' h₂).comp' h,
    simp },
  simp [cont, times_cont_diff_within_at_prop]
end

lemma smooth_within_at_iff :
  smooth_within_at I I' f s x ↔ continuous_within_at f s x ∧
    times_cont_diff_within_at 𝕜 ∞ ((ext_chart_at I' (f x)) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩
      (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' (f x)).source))
    (ext_chart_at I x x) :=
times_cont_mdiff_within_at_iff

lemma smooth_within_at_iff_target :
  smooth_within_at I I' f s x ↔ continuous_within_at f s x ∧
    smooth_within_at I 𝓘(𝕜, E') ((ext_chart_at I' (f x)) ∘ f)
    (s ∩ f ⁻¹' (ext_chart_at I' (f x)).source) x :=
times_cont_mdiff_within_at_iff_target

lemma times_cont_mdiff_at_ext_chart_at :
  times_cont_mdiff_at I 𝓘(𝕜, E) n (ext_chart_at I x) x :=
begin
  rw [times_cont_mdiff_at, times_cont_mdiff_within_at_iff],
  refine ⟨(ext_chart_at_continuous_at _ _).continuous_within_at, _⟩,
  refine times_cont_diff_within_at_id.congr _ _;
    simp only with mfld_simps { contextual := tt }
end

include Is I's

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
lemma times_cont_mdiff_within_at_iff' {x' : M} {y : M'} (hx : x' ∈ (chart_at H x).source)
  (hy : f x' ∈ (chart_at H' y).source) :
  times_cont_mdiff_within_at I I' n f s x' ↔ continuous_within_at f s x' ∧
    times_cont_diff_within_at 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source))
    (ext_chart_at I x x') :=
begin
  refine ((times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
    (structure_groupoid.chart_mem_maximal_atlas _ x) hx
    (structure_groupoid.chart_mem_maximal_atlas _ y) hy).trans _,
  rw [times_cont_diff_within_at_prop, iff_eq_eq],
  congr' 2,
  mfld_set_tac
end

omit I's

lemma times_cont_mdiff_at_ext_chart_at' {x' : M} (h : x' ∈ (chart_at H x).source) :
  times_cont_mdiff_at I 𝓘(𝕜, E) n (ext_chart_at I x) x' :=
begin
  refine (times_cont_mdiff_within_at_iff' h (mem_chart_source _ _)).2 _,
  refine ⟨(ext_chart_at_continuous_at' _ _ _).continuous_within_at, _⟩,
  { rwa ext_chart_at_source },
  refine times_cont_diff_within_at_id.congr' _ _;
    simp only [h] with mfld_simps { contextual := tt }
end

include I's

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
lemma times_cont_mdiff_on_iff :
  times_cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    ∀ (x : M) (y : M'), times_cont_diff_on 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩
      (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source)) :=
begin
  split,
  { assume h,
    refine ⟨λ x hx, (h x hx).1, λ x y z hz, _⟩,
    simp only with mfld_simps at hz,
    let w := (ext_chart_at I x).symm z,
    have : w ∈ s, by simp only [w, hz] with mfld_simps,
    specialize h w this,
    have w1 : w ∈ (chart_at H x).source, by simp only [w, hz] with mfld_simps,
    have w2 : f w ∈ (chart_at H' y).source, by simp only [w, hz] with mfld_simps,
    convert
      (((times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
        (structure_groupoid.chart_mem_maximal_atlas _ x) w1
        (structure_groupoid.chart_mem_maximal_atlas _ y) w2).1 h).2 using 1,
    { mfld_set_tac },
    { simp only [w, hz] with mfld_simps } },
  { rintros ⟨hcont, hdiff⟩ x hx,
    refine ⟨hcont x hx, _⟩,
    have Z := hdiff x (f x) (ext_chart_at I x x) (by simp only [hx] with mfld_simps),
    dsimp [times_cont_diff_within_at_prop],
    convert Z using 1,
    mfld_set_tac }
end

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart in the target. -/
lemma times_cont_mdiff_on_iff_target :
  times_cont_mdiff_on I I' n f s ↔ continuous_on f s ∧ ∀ (y : M'),
    times_cont_mdiff_on I 𝓘(𝕜, E') n ((ext_chart_at I' y) ∘ f)
    (s ∩ f ⁻¹' (ext_chart_at I' y).source) :=
begin
  inhabit E',
  simp only [times_cont_mdiff_on_iff, model_with_corners.source_eq, chart_at_self_eq,
    local_homeomorph.refl_local_equiv, local_equiv.refl_trans, ext_chart_at.equations._eqn_1,
    set.preimage_univ, set.inter_univ, and.congr_right_iff],
  intros h,
  split,
  { refine λ h' y, ⟨_, λ x _, h' x y⟩,
    have h'' : continuous_on _ univ := (model_with_corners.continuous I').continuous_on,
    convert (h''.comp' (chart_at H' y).continuous_to_fun).comp' h,
    simp },
  { exact λ h' x y, (h' y).2 x (default E') }
end

lemma smooth_on_iff :
  smooth_on I I' f s ↔ continuous_on f s ∧
    ∀ (x : M) (y : M'), times_cont_diff_on 𝕜 ⊤ ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩
      (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source)) :=
times_cont_mdiff_on_iff

lemma smooth_on_iff_target :
  smooth_on I I' f s ↔ continuous_on f s ∧ ∀ (y : M'),
    smooth_on I 𝓘(𝕜, E') ((ext_chart_at I' y) ∘ f)
    (s ∩ f ⁻¹' (ext_chart_at I' y).source) :=
times_cont_mdiff_on_iff_target

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
lemma times_cont_mdiff_iff :
  times_cont_mdiff I I' n f ↔ continuous f ∧
    ∀ (x : M) (y : M'), times_cont_diff_on 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' y).source)) :=
by simp [← times_cont_mdiff_on_univ, times_cont_mdiff_on_iff, continuous_iff_continuous_on_univ]

/-- One can reformulate smoothness as continuity and smoothness in any extended chart in the
target. -/
lemma times_cont_mdiff_iff_target :
  times_cont_mdiff I I' n f ↔ continuous f ∧
    ∀ (y : M'), times_cont_mdiff_on I 𝓘(𝕜, E') n ((ext_chart_at I' y) ∘ f)
    (f ⁻¹' (ext_chart_at I' y).source) :=
begin
  rw [← times_cont_mdiff_on_univ, times_cont_mdiff_on_iff_target],
  simp [continuous_iff_continuous_on_univ]
end

lemma smooth_iff :
  smooth I I' f ↔ continuous f ∧
    ∀ (x : M) (y : M'), times_cont_diff_on 𝕜 ⊤ ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' y).source)) :=
times_cont_mdiff_iff

lemma smooth_iff_target :
  smooth I I' f ↔ continuous f ∧ ∀ (y : M'), smooth_on I 𝓘(𝕜, E') ((ext_chart_at I' y) ∘ f)
    (f ⁻¹' (ext_chart_at I' y).source) :=
times_cont_mdiff_iff_target

omit Is I's

/-! ### Deducing smoothness from higher smoothness -/

lemma times_cont_mdiff_within_at.of_le (hf : times_cont_mdiff_within_at I I' n f s x) (le : m ≤ n) :
  times_cont_mdiff_within_at I I' m f s x :=
⟨hf.1, hf.2.of_le le⟩

lemma times_cont_mdiff_at.of_le (hf : times_cont_mdiff_at I I' n f x) (le : m ≤ n) :
  times_cont_mdiff_at I I' m f x :=
times_cont_mdiff_within_at.of_le hf le

lemma times_cont_mdiff_on.of_le (hf : times_cont_mdiff_on I I' n f s) (le : m ≤ n) :
  times_cont_mdiff_on I I' m f s :=
λ x hx, (hf x hx).of_le le

lemma times_cont_mdiff.of_le (hf : times_cont_mdiff I I' n f) (le : m ≤ n) :
  times_cont_mdiff I I' m f :=
λ x, (hf x).of_le le

/-! ### Deducing smoothness from smoothness one step beyond -/

lemma times_cont_mdiff_within_at.of_succ {n : ℕ}
  (h : times_cont_mdiff_within_at I I' n.succ f s x) :
  times_cont_mdiff_within_at I I' n f s x :=
h.of_le (with_top.coe_le_coe.2 (nat.le_succ n))

lemma times_cont_mdiff_at.of_succ {n : ℕ} (h : times_cont_mdiff_at I I' n.succ f x) :
  times_cont_mdiff_at I I' n f x :=
times_cont_mdiff_within_at.of_succ h

lemma times_cont_mdiff_on.of_succ {n : ℕ} (h : times_cont_mdiff_on I I' n.succ f s) :
  times_cont_mdiff_on I I' n f s :=
λ x hx, (h x hx).of_succ

lemma times_cont_mdiff.of_succ {n : ℕ} (h : times_cont_mdiff I I' n.succ f) :
  times_cont_mdiff I I' n f :=
λ x, (h x).of_succ

/-! ### Deducing continuity from smoothness-/

lemma times_cont_mdiff_within_at.continuous_within_at
  (hf : times_cont_mdiff_within_at I I' n f s x) : continuous_within_at f s x :=
hf.1

lemma times_cont_mdiff_at.continuous_at
  (hf : times_cont_mdiff_at I I' n f x) : continuous_at f x :=
(continuous_within_at_univ _ _ ).1 $ times_cont_mdiff_within_at.continuous_within_at hf

lemma times_cont_mdiff_on.continuous_on
  (hf : times_cont_mdiff_on I I' n f s) : continuous_on f s :=
λ x hx, (hf x hx).continuous_within_at

lemma times_cont_mdiff.continuous (hf : times_cont_mdiff I I' n f) :
  continuous f :=
continuous_iff_continuous_at.2 $ λ x, (hf x).continuous_at

/-! ### Deducing differentiability from smoothness -/

lemma times_cont_mdiff_within_at.mdifferentiable_within_at
  (hf : times_cont_mdiff_within_at I I' n f s x) (hn : 1 ≤ n) :
  mdifferentiable_within_at I I' f s x :=
begin
  suffices h : mdifferentiable_within_at I I' f (s ∩ (f ⁻¹' (ext_chart_at I' (f x)).source)) x,
  { rwa mdifferentiable_within_at_inter' at h,
    apply (hf.1).preimage_mem_nhds_within,
    exact is_open.mem_nhds (ext_chart_at_open_source I' (f x)) (mem_ext_chart_source I' (f x)) },
  rw mdifferentiable_within_at_iff,
  exact ⟨hf.1.mono (inter_subset_left _ _),
    (hf.2.differentiable_within_at hn).mono (by mfld_set_tac)⟩,
end

lemma times_cont_mdiff_at.mdifferentiable_at (hf : times_cont_mdiff_at I I' n f x) (hn : 1 ≤ n) :
  mdifferentiable_at I I' f x :=
mdifferentiable_within_at_univ.1 $ times_cont_mdiff_within_at.mdifferentiable_within_at hf hn

lemma times_cont_mdiff_on.mdifferentiable_on (hf : times_cont_mdiff_on I I' n f s) (hn : 1 ≤ n) :
  mdifferentiable_on I I' f s :=
λ x hx, (hf x hx).mdifferentiable_within_at hn

lemma times_cont_mdiff.mdifferentiable (hf : times_cont_mdiff I I' n f) (hn : 1 ≤ n) :
  mdifferentiable I I' f :=
λ x, (hf x).mdifferentiable_at hn

lemma smooth.mdifferentiable (hf : smooth I I' f) : mdifferentiable I I' f :=
times_cont_mdiff.mdifferentiable hf le_top

lemma smooth.mdifferentiable_at (hf : smooth I I' f) : mdifferentiable_at I I' f x :=
hf.mdifferentiable x

lemma smooth.mdifferentiable_within_at (hf : smooth I I' f) :
  mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_at.mdifferentiable_within_at

/-! ### `C^∞` smoothness -/

lemma times_cont_mdiff_within_at_top :
  smooth_within_at I I' f s x ↔ (∀n:ℕ, times_cont_mdiff_within_at I I' n f s x) :=
⟨λ h n, ⟨h.1, times_cont_diff_within_at_top.1 h.2 n⟩,
 λ H, ⟨(H 0).1, times_cont_diff_within_at_top.2 (λ n, (H n).2)⟩⟩

lemma times_cont_mdiff_at_top :
  smooth_at I I' f x ↔ (∀n:ℕ, times_cont_mdiff_at I I' n f x) :=
times_cont_mdiff_within_at_top

lemma times_cont_mdiff_on_top :
  smooth_on I I' f s ↔ (∀n:ℕ, times_cont_mdiff_on I I' n f s) :=
⟨λ h n, h.of_le le_top, λ h x hx, times_cont_mdiff_within_at_top.2 (λ n, h n x hx)⟩

lemma times_cont_mdiff_top :
  smooth I I' f ↔ (∀n:ℕ, times_cont_mdiff I I' n f) :=
⟨λ h n, h.of_le le_top, λ h x, times_cont_mdiff_within_at_top.2 (λ n, h n x)⟩

lemma times_cont_mdiff_within_at_iff_nat :
  times_cont_mdiff_within_at I I' n f s x ↔
  (∀m:ℕ, (m : with_top ℕ) ≤ n → times_cont_mdiff_within_at I I' m f s x) :=
begin
  refine ⟨λ h m hm, h.of_le hm, λ h, _⟩,
  cases n,
  { exact times_cont_mdiff_within_at_top.2 (λ n, h n le_top) },
  { exact h n (le_refl _) }
end

/-! ### Restriction to a smaller set -/

lemma times_cont_mdiff_within_at.mono (hf : times_cont_mdiff_within_at I I' n f s x) (hts : t ⊆ s) :
  times_cont_mdiff_within_at I I' n f t x :=
structure_groupoid.local_invariant_prop.lift_prop_within_at_mono
  (times_cont_diff_within_at_local_invariant_prop_mono I I' n) hf hts

lemma times_cont_mdiff_at.times_cont_mdiff_within_at (hf : times_cont_mdiff_at I I' n f x) :
  times_cont_mdiff_within_at I I' n f s x :=
times_cont_mdiff_within_at.mono hf (subset_univ _)

lemma smooth_at.smooth_within_at (hf : smooth_at I I' f x) :
  smooth_within_at I I' f s x :=
times_cont_mdiff_at.times_cont_mdiff_within_at hf

lemma times_cont_mdiff_on.mono (hf : times_cont_mdiff_on I I' n f s) (hts : t ⊆ s) :
  times_cont_mdiff_on I I' n f t :=
λ x hx, (hf x (hts hx)).mono hts

lemma times_cont_mdiff.times_cont_mdiff_on (hf : times_cont_mdiff I I' n f) :
  times_cont_mdiff_on I I' n f s :=
λ x hx, (hf x).times_cont_mdiff_within_at

lemma smooth.smooth_on (hf : smooth I I' f) :
  smooth_on I I' f s :=
times_cont_mdiff.times_cont_mdiff_on hf

lemma times_cont_mdiff_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  times_cont_mdiff_within_at I I' n f (s ∩ t) x ↔ times_cont_mdiff_within_at I I' n f s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_inter' ht

lemma times_cont_mdiff_within_at_inter (ht : t ∈ 𝓝 x) :
  times_cont_mdiff_within_at I I' n f (s ∩ t) x ↔ times_cont_mdiff_within_at I I' n f s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_inter ht

lemma times_cont_mdiff_within_at.times_cont_mdiff_at
  (h : times_cont_mdiff_within_at I I' n f s x) (ht : s ∈ 𝓝 x) :
  times_cont_mdiff_at I I' n f x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_of_lift_prop_within_at h ht

lemma smooth_within_at.smooth_at
  (h : smooth_within_at I I' f s x) (ht : s ∈ 𝓝 x) :
  smooth_at I I' f x :=
times_cont_mdiff_within_at.times_cont_mdiff_at h ht

include Is

lemma times_cont_mdiff_on_ext_chart_at :
  times_cont_mdiff_on I 𝓘(𝕜, E) n (ext_chart_at I x) (chart_at H x).source :=
λ x' hx', (times_cont_mdiff_at_ext_chart_at' hx').times_cont_mdiff_within_at

include I's

/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
lemma times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds {n : ℕ} :
  times_cont_mdiff_within_at I I' n f s x ↔
  ∃ u ∈ 𝓝[insert x s] x, times_cont_mdiff_on I I' n f u :=
begin
  split,
  { assume h,
    -- the property is true in charts. We will pull such a good neighborhood in the chart to the
    -- manifold. For this, we need to restrict to a small enough set where everything makes sense
    obtain ⟨o, o_open, xo, ho, h'o⟩ : ∃ (o : set M),
      is_open o ∧ x ∈ o ∧ o ⊆ (chart_at H x).source ∧ o ∩ s ⊆ f ⁻¹' (chart_at H' (f x)).source,
    { have : (chart_at H' (f x)).source ∈ 𝓝 (f x) :=
        is_open.mem_nhds (local_homeomorph.open_source _) (mem_chart_source H' (f x)),
      rcases mem_nhds_within.1 (h.1.preimage_mem_nhds_within this) with ⟨u, u_open, xu, hu⟩,
      refine ⟨u ∩ (chart_at H x).source, _, ⟨xu, mem_chart_source _ _⟩, _, _⟩,
      { exact is_open.inter u_open (local_homeomorph.open_source _) },
      { assume y hy, exact hy.2 },
      { assume y hy, exact hu ⟨hy.1.1, hy.2⟩ } },
    have h' : times_cont_mdiff_within_at I I' n f (s ∩ o) x := h.mono (inter_subset_left _ _),
    simp only [times_cont_mdiff_within_at, lift_prop_within_at, times_cont_diff_within_at_prop]
      at h',
    -- let `u` be a good neighborhood in the chart where the function is smooth
    rcases h.2.times_cont_diff_on (le_refl _) with ⟨u, u_nhds, u_subset, hu⟩,
    -- pull it back to the manifold, and intersect with a suitable neighborhood of `x`, to get the
    -- desired good neighborhood `v`.
    let v := ((insert x s) ∩ o) ∩ (ext_chart_at I x) ⁻¹' u,
    have v_incl : v ⊆ (chart_at H x).source := λ y hy, ho hy.1.2,
    have v_incl' : ∀ y ∈ v, f y ∈ (chart_at H' (f x)).source,
    { assume y hy,
      rcases hy.1.1 with rfl|h',
      { simp only with mfld_simps },
      { apply h'o ⟨hy.1.2, h'⟩ } },
    refine ⟨v, _, _⟩,
    show v ∈ 𝓝[insert x s] x,
    { rw nhds_within_restrict _ xo o_open,
      refine filter.inter_mem self_mem_nhds_within _,
      suffices : u ∈ 𝓝[(ext_chart_at I x) '' (insert x s ∩ o)] (ext_chart_at I x x),
        from (ext_chart_at_continuous_at I x).continuous_within_at.preimage_mem_nhds_within' this,
      apply nhds_within_mono _ _ u_nhds,
      rw image_subset_iff,
      assume y hy,
      rcases hy.1 with rfl|h',
      { simp only [mem_insert_iff] with mfld_simps },
      { simp only [mem_insert_iff, ho hy.2, h', h'o ⟨hy.2, h'⟩] with mfld_simps } },
    show times_cont_mdiff_on I I' n f v,
    { assume y hy,
      apply
        (((times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
        (structure_groupoid.chart_mem_maximal_atlas _ x) (v_incl hy)
        (structure_groupoid.chart_mem_maximal_atlas _ (f x)) (v_incl' y hy))).2,
      split,
      { apply (((ext_chart_at_continuous_on_symm I' (f x) _ _).comp'
          (hu _ hy.2).continuous_within_at).comp' (ext_chart_at_continuous_on I x _ _)).congr_mono,
        { assume z hz,
          simp only [v_incl hz, v_incl' z hz] with mfld_simps },
        { assume z hz,
          simp only [v_incl hz, v_incl' z hz] with mfld_simps,
          exact hz.2 },
        { simp only [v_incl hy, v_incl' y hy] with mfld_simps },
        { simp only [v_incl hy, v_incl' y hy] with mfld_simps },
        { simp only [v_incl hy] with mfld_simps } },
      { apply hu.mono,
        { assume z hz,
          simp only [v] with mfld_simps at hz,
          have : I ((chart_at H x) (((chart_at H x).symm) (I.symm z))) ∈ u, by simp only [hz],
          simpa only [hz] with mfld_simps using this },
        { have exty : I (chart_at H x y) ∈ u := hy.2,
          simp only [v_incl hy, v_incl' y hy, exty, hy.1.1, hy.1.2] with mfld_simps } } } },
  { rintros ⟨u, u_nhds, hu⟩,
    have : times_cont_mdiff_within_at I I' ↑n f (insert x s ∩ u) x,
    { have : x ∈ insert x s := mem_insert x s,
      exact hu.mono (inter_subset_right _ _) _ ⟨this, mem_of_mem_nhds_within this u_nhds⟩ },
    rw times_cont_mdiff_within_at_inter' u_nhds at this,
    exact this.mono (subset_insert x s) }
end

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
lemma times_cont_mdiff_at_iff_times_cont_mdiff_on_nhds {n : ℕ} :
  times_cont_mdiff_at I I' n f x ↔ ∃ u ∈ 𝓝 x, times_cont_mdiff_on I I' n f u :=
by simp [← times_cont_mdiff_within_at_univ, times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds,
  nhds_within_univ]

omit Is I's

/-! ### Congruence lemmas -/

lemma times_cont_mdiff_within_at.congr
  (h : times_cont_mdiff_within_at I I' n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
  (hx : f₁ x = f x) : times_cont_mdiff_within_at I I' n f₁ s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr h h₁ hx

lemma times_cont_mdiff_within_at_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
  times_cont_mdiff_within_at I I' n f₁ s x ↔ times_cont_mdiff_within_at I I' n f s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr_iff h₁ hx

lemma times_cont_mdiff_within_at.congr_of_eventually_eq
  (h : times_cont_mdiff_within_at I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  (hx : f₁ x = f x) : times_cont_mdiff_within_at I I' n f₁ s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr_of_eventually_eq
  h h₁ hx

lemma filter.eventually_eq.times_cont_mdiff_within_at_iff
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  times_cont_mdiff_within_at I I' n f₁ s x ↔ times_cont_mdiff_within_at I I' n f s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n)
  .lift_prop_within_at_congr_iff_of_eventually_eq h₁ hx

lemma times_cont_mdiff_at.congr_of_eventually_eq
  (h : times_cont_mdiff_at I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
  times_cont_mdiff_at I I' n f₁ x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_congr_of_eventually_eq h h₁

lemma filter.eventually_eq.times_cont_mdiff_at_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
  times_cont_mdiff_at I I' n f₁ x ↔ times_cont_mdiff_at I I' n f x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_congr_iff_of_eventually_eq h₁

lemma times_cont_mdiff_on.congr (h : times_cont_mdiff_on I I' n f s) (h₁ : ∀ y ∈ s, f₁ y = f y) :
  times_cont_mdiff_on I I' n f₁ s :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_congr h h₁

lemma times_cont_mdiff_on_congr (h₁ : ∀ y ∈ s, f₁ y = f y) :
  times_cont_mdiff_on I I' n f₁ s ↔ times_cont_mdiff_on I I' n f s :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_congr_iff h₁

/-! ### Locality -/

/-- Being `C^n` is a local property. -/
lemma times_cont_mdiff_on_of_locally_times_cont_mdiff_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ times_cont_mdiff_on I I' n f (s ∩ u)) :
  times_cont_mdiff_on I I' n f s :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_of_locally_lift_prop_on h

lemma times_cont_mdiff_of_locally_times_cont_mdiff_on
  (h : ∀x, ∃u, is_open u ∧ x ∈ u ∧ times_cont_mdiff_on I I' n f u) :
  times_cont_mdiff I I' n f :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_of_locally_lift_prop_on h

/-! ### Smoothness of the composition of smooth functions between manifolds -/

section composition

variables {E'' : Type*} [normed_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
lemma times_cont_mdiff_within_at.comp {t : set M'} {g : M' → M''} (x : M)
  (hg : times_cont_mdiff_within_at I' I'' n g t (f x))
  (hf : times_cont_mdiff_within_at I I' n f s x)
  (st : maps_to f s t) : times_cont_mdiff_within_at I I'' n (g ∘ f) s x :=
begin
  rw times_cont_mdiff_within_at_iff'' at hg hf ⊢,
  refine ⟨hg.1.comp hf.1 st, _⟩,
  set e := ext_chart_at I x,
  set e' := ext_chart_at I' (f x),
  set e'' := ext_chart_at I'' (g (f x)),
  have : e' (f x) = (written_in_ext_chart_at I I' x f) (e x),
    by simp only [e, e'] with mfld_simps,
  rw this at hg,
  have A : ∀ᶠ y in 𝓝[e.symm ⁻¹' s ∩ range I] e x,
    y ∈ e.target ∧ f (e.symm y) ∈ t ∧ f (e.symm y) ∈ e'.source ∧ g (f (e.symm y)) ∈ e''.source,
  { simp only [← ext_chart_at_map_nhds_within, eventually_map],
    filter_upwards [hf.1.tendsto (ext_chart_at_source_mem_nhds I' (f x)),
      (hg.1.comp hf.1 st).tendsto (ext_chart_at_source_mem_nhds I'' (g (f x))),
      (inter_mem_nhds_within s (ext_chart_at_source_mem_nhds I x))],
    rintros x' (hfx' : f x' ∈ _) (hgfx' : g (f x') ∈ _) ⟨hx's, hx'⟩,
    simp only [e.map_source hx', true_and, e.left_inv hx', st hx's, *] },
  refine ((hg.2.comp _ (hf.2.mono (inter_subset_right _ _)) (inter_subset_left _ _)).mono_of_mem
    (inter_mem _ self_mem_nhds_within)).congr_of_eventually_eq _ _,
  { filter_upwards [A],
    rintro x' ⟨hx', ht, hfx', hgfx'⟩,
    simp only [*, mem_preimage, written_in_ext_chart_at, (∘), mem_inter_eq, e'.left_inv, true_and],
    exact mem_range_self _ },
  { filter_upwards [A],
    rintro x' ⟨hx', ht, hfx', hgfx'⟩,
    simp only [*, (∘), written_in_ext_chart_at, e'.left_inv] },
  { simp only [written_in_ext_chart_at, (∘), mem_ext_chart_source, e.left_inv, e'.left_inv] }
end

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma times_cont_mdiff_on.comp {t : set M'} {g : M' → M''}
  (hg : times_cont_mdiff_on I' I'' n g t) (hf : times_cont_mdiff_on I I' n f s)
  (st : s ⊆ f ⁻¹' t) : times_cont_mdiff_on I I'' n (g ∘ f) s :=
λ x hx, (hg _ (st hx)).comp x (hf x hx) st

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma times_cont_mdiff_on.comp' {t : set M'} {g : M' → M''}
  (hg : times_cont_mdiff_on I' I'' n g t) (hf : times_cont_mdiff_on I I' n f s) :
  times_cont_mdiff_on I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of `C^n` functions is `C^n`. -/
lemma times_cont_mdiff.comp {g : M' → M''}
  (hg : times_cont_mdiff I' I'' n g) (hf : times_cont_mdiff I I' n f) :
  times_cont_mdiff I I'' n (g ∘ f) :=
begin
  rw ← times_cont_mdiff_on_univ at hf hg ⊢,
  exact hg.comp hf subset_preimage_univ,
end

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
lemma times_cont_mdiff_within_at.comp' {t : set M'} {g : M' → M''} (x : M)
  (hg : times_cont_mdiff_within_at I' I'' n g t (f x))
  (hf : times_cont_mdiff_within_at I I' n f s x) :
  times_cont_mdiff_within_at I I'' n (g ∘ f) (s ∩ f⁻¹' t) x :=
hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
lemma times_cont_mdiff_at.comp_times_cont_mdiff_within_at {g : M' → M''} (x : M)
  (hg : times_cont_mdiff_at I' I'' n g (f x)) (hf : times_cont_mdiff_within_at I I' n f s x) :
  times_cont_mdiff_within_at I I'' n (g ∘ f) s x :=
hg.comp x hf (maps_to_univ _ _)

/-- The composition of `C^n` functions at points is `C^n`. -/
lemma times_cont_mdiff_at.comp {g : M' → M''} (x : M)
  (hg : times_cont_mdiff_at I' I'' n g (f x)) (hf : times_cont_mdiff_at I I' n f x) :
  times_cont_mdiff_at I I'' n (g ∘ f) x :=
hg.comp x hf (maps_to_univ _ _)

lemma times_cont_mdiff.comp_times_cont_mdiff_on {f : M → M'} {g : M' → M''} {s : set M}
  (hg : times_cont_mdiff I' I'' n g) (hf : times_cont_mdiff_on I I' n f s) :
  times_cont_mdiff_on I I'' n (g ∘ f) s :=
hg.times_cont_mdiff_on.comp hf set.subset_preimage_univ

lemma smooth.comp_smooth_on {f : M → M'} {g : M' → M''} {s : set M}
  (hg : smooth I' I'' g) (hf : smooth_on I I' f s) :
  smooth_on I I'' (g ∘ f) s :=
hg.smooth_on.comp hf set.subset_preimage_univ

end composition

/-! ### Atlas members are smooth -/
section atlas

variables {e : local_homeomorph M H}
include Is

/-- An atlas member is `C^n` for any `n`. -/
lemma times_cont_mdiff_on_of_mem_maximal_atlas
  (h : e ∈ maximal_atlas I M) : times_cont_mdiff_on I I n e e.source :=
times_cont_mdiff_on.of_le
  ((times_cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_on_of_mem_maximal_atlas
    (times_cont_diff_within_at_local_invariant_prop_id I) h) le_top

/-- The inverse of an atlas member is `C^n` for any `n`. -/
lemma times_cont_mdiff_on_symm_of_mem_maximal_atlas
  (h : e ∈ maximal_atlas I M) : times_cont_mdiff_on I I n e.symm e.target :=
times_cont_mdiff_on.of_le
  ((times_cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_on_symm_of_mem_maximal_atlas
    (times_cont_diff_within_at_local_invariant_prop_id I) h) le_top

lemma times_cont_mdiff_on_chart :
  times_cont_mdiff_on I I n (chart_at H x) (chart_at H x).source :=
times_cont_mdiff_on_of_mem_maximal_atlas
  ((times_cont_diff_groupoid ⊤ I).chart_mem_maximal_atlas x)

lemma times_cont_mdiff_on_chart_symm :
  times_cont_mdiff_on I I n (chart_at H x).symm (chart_at H x).target :=
times_cont_mdiff_on_symm_of_mem_maximal_atlas
  ((times_cont_diff_groupoid ⊤ I).chart_mem_maximal_atlas x)

end atlas

/-! ### The identity is smooth -/
section id

lemma times_cont_mdiff_id : times_cont_mdiff I I n (id : M → M) :=
times_cont_mdiff.of_le ((times_cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_id
  (times_cont_diff_within_at_local_invariant_prop_id I)) le_top

lemma smooth_id : smooth I I (id : M → M) := times_cont_mdiff_id

lemma times_cont_mdiff_on_id : times_cont_mdiff_on I I n (id : M → M) s :=
times_cont_mdiff_id.times_cont_mdiff_on

lemma smooth_on_id : smooth_on I I (id : M → M) s := times_cont_mdiff_on_id

lemma times_cont_mdiff_at_id : times_cont_mdiff_at I I n (id : M → M) x :=
times_cont_mdiff_id.times_cont_mdiff_at

lemma smooth_at_id : smooth_at I I (id : M → M) x := times_cont_mdiff_at_id

lemma times_cont_mdiff_within_at_id : times_cont_mdiff_within_at I I n (id : M → M) s x :=
times_cont_mdiff_at_id.times_cont_mdiff_within_at

lemma smooth_within_at_id : smooth_within_at I I (id : M → M) s x := times_cont_mdiff_within_at_id

end id

/-! ### Constants are smooth -/
section id

variable {c : M'}

lemma times_cont_mdiff_const : times_cont_mdiff I I' n (λ (x : M), c) :=
begin
  assume x,
  refine ⟨continuous_within_at_const, _⟩,
  simp only [times_cont_diff_within_at_prop, (∘)],
  exact times_cont_diff_within_at_const,
end

@[to_additive]
lemma times_cont_mdiff_one [has_one M'] : times_cont_mdiff I I' n (1 : M → M') :=
by simp only [pi.one_def, times_cont_mdiff_const]

lemma smooth_const : smooth I I' (λ (x : M), c) := times_cont_mdiff_const

@[to_additive]
lemma smooth_one [has_one M'] : smooth I I' (1 : M → M') :=
by simp only [pi.one_def, smooth_const]

lemma times_cont_mdiff_on_const : times_cont_mdiff_on I I' n (λ (x : M), c) s :=
times_cont_mdiff_const.times_cont_mdiff_on

@[to_additive]
lemma times_cont_mdiff_on_one [has_one M'] : times_cont_mdiff_on I I' n (1 : M → M') s :=
times_cont_mdiff_one.times_cont_mdiff_on

lemma smooth_on_const : smooth_on I I' (λ (x : M), c) s :=
times_cont_mdiff_on_const

@[to_additive]
lemma smooth_on_one [has_one M'] : smooth_on I I' (1 : M → M') s :=
times_cont_mdiff_on_one

lemma times_cont_mdiff_at_const : times_cont_mdiff_at I I' n (λ (x : M), c) x :=
times_cont_mdiff_const.times_cont_mdiff_at

@[to_additive]
lemma times_cont_mdiff_at_one [has_one M'] : times_cont_mdiff_at I I' n (1 : M → M') x :=
times_cont_mdiff_one.times_cont_mdiff_at

lemma smooth_at_const : smooth_at I I' (λ (x : M), c) x :=
times_cont_mdiff_at_const

@[to_additive]
lemma smooth_at_one [has_one M'] : smooth_at I I' (1 : M → M') x :=
times_cont_mdiff_at_one

lemma times_cont_mdiff_within_at_const : times_cont_mdiff_within_at I I' n (λ (x : M), c) s x :=
times_cont_mdiff_at_const.times_cont_mdiff_within_at

@[to_additive]
lemma times_cont_mdiff_within_at_one [has_one M'] :
  times_cont_mdiff_within_at I I' n (1 : M → M') s x :=
times_cont_mdiff_at_const.times_cont_mdiff_within_at

lemma smooth_within_at_const : smooth_within_at I I' (λ (x : M), c) s x :=
times_cont_mdiff_within_at_const

@[to_additive]
lemma smooth_within_at_one [has_one M'] : smooth_within_at I I' (1 : M → M') s x :=
times_cont_mdiff_within_at_one

end id

lemma times_cont_mdiff_of_support {f : M → F}
  (hf : ∀ x ∈ closure (support f), times_cont_mdiff_at I 𝓘(𝕜, F) n f x) :
  times_cont_mdiff I 𝓘(𝕜, F) n f :=
begin
  intro x,
  by_cases hx : x ∈ closure (support f),
  { exact hf x hx },
  { refine times_cont_mdiff_at.congr_of_eventually_eq _ (eventually_eq_zero_nhds.2 hx),
    exact times_cont_mdiff_at_const }
end

/-! ### Equivalence with the basic definition for functions between vector spaces -/

section module

lemma times_cont_mdiff_within_at_iff_times_cont_diff_within_at {f : E → E'} {s : set E} {x : E} :
  times_cont_mdiff_within_at 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x
  ↔ times_cont_diff_within_at 𝕜 n f s x :=
begin
  simp only [times_cont_mdiff_within_at, lift_prop_within_at, times_cont_diff_within_at_prop,
    iff_def] with mfld_simps {contextual := tt},
  exact times_cont_diff_within_at.continuous_within_at
end

alias times_cont_mdiff_within_at_iff_times_cont_diff_within_at ↔
  times_cont_mdiff_within_at.times_cont_diff_within_at
  times_cont_diff_within_at.times_cont_mdiff_within_at

lemma times_cont_mdiff_at_iff_times_cont_diff_at {f : E → E'} {x : E} :
  times_cont_mdiff_at 𝓘(𝕜, E) 𝓘(𝕜, E') n f x
  ↔ times_cont_diff_at 𝕜 n f x :=
by rw [← times_cont_mdiff_within_at_univ,
  times_cont_mdiff_within_at_iff_times_cont_diff_within_at, times_cont_diff_within_at_univ]

alias times_cont_mdiff_at_iff_times_cont_diff_at ↔
  times_cont_mdiff_at.times_cont_diff_at times_cont_diff_at.times_cont_mdiff_at

lemma times_cont_mdiff_on_iff_times_cont_diff_on {f : E → E'} {s : set E} :
  times_cont_mdiff_on 𝓘(𝕜, E) 𝓘(𝕜, E') n f s
  ↔ times_cont_diff_on 𝕜 n f s :=
forall_congr $ by simp [times_cont_mdiff_within_at_iff_times_cont_diff_within_at]

alias times_cont_mdiff_on_iff_times_cont_diff_on ↔
  times_cont_mdiff_on.times_cont_diff_on times_cont_diff_on.times_cont_mdiff_on

lemma times_cont_mdiff_iff_times_cont_diff {f : E → E'} :
  times_cont_mdiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f
  ↔ times_cont_diff 𝕜 n f :=
by rw [← times_cont_diff_on_univ, ← times_cont_mdiff_on_univ,
  times_cont_mdiff_on_iff_times_cont_diff_on]

alias times_cont_mdiff_iff_times_cont_diff ↔
  times_cont_mdiff.times_cont_diff times_cont_diff.times_cont_mdiff

end module

/-! ### The tangent map of a smooth function is smooth -/

section tangent_map

/-- If a function is `C^n` with `1 ≤ n` on a domain with unique derivatives, then its bundled
derivative is continuous. In this auxiliary lemma, we prove this fact when the source and target
space are model spaces in models with corners. The general fact is proved in
`times_cont_mdiff_on.continuous_on_tangent_map_within`-/
lemma times_cont_mdiff_on.continuous_on_tangent_map_within_aux
  {f : H → H'} {s : set H}
  (hf : times_cont_mdiff_on I I' n f s) (hn : 1 ≤ n) (hs : unique_mdiff_on I s) :
  continuous_on (tangent_map_within I I' f s) ((tangent_bundle.proj I H) ⁻¹' s) :=
begin
  suffices h : continuous_on (λ (p : H × E), (f p.fst,
    (fderiv_within 𝕜 (written_in_ext_chart_at I I' p.fst f) (I.symm ⁻¹' s ∩ range I)
      ((ext_chart_at I p.fst) p.fst) : E →L[𝕜] E') p.snd)) (prod.fst ⁻¹' s),
  { have A := (tangent_bundle_model_space_homeomorph H I).continuous,
    rw continuous_iff_continuous_on_univ at A,
    have B := ((tangent_bundle_model_space_homeomorph H' I').symm.continuous.comp_continuous_on h)
      .comp' A,
    have : (univ ∩ ⇑(tangent_bundle_model_space_homeomorph H I) ⁻¹' (prod.fst ⁻¹' s)) =
      tangent_bundle.proj I H ⁻¹' s,
      by { ext ⟨x, v⟩, simp only with mfld_simps },
    rw this at B,
    apply B.congr,
    rintros ⟨x, v⟩ hx,
    dsimp [tangent_map_within],
    ext, { refl },
    simp only with mfld_simps,
    apply congr_fun,
    apply congr_arg,
    rw mdifferentiable_within_at.mfderiv_within (hf.mdifferentiable_on hn x hx),
    refl },
  suffices h : continuous_on (λ (p : H × E), (fderiv_within 𝕜 (I' ∘ f ∘ I.symm)
    (I.symm ⁻¹' s ∩ range I) (I p.fst) : E →L[𝕜] E') p.snd) (prod.fst ⁻¹' s),
  { dsimp [written_in_ext_chart_at, ext_chart_at],
    apply continuous_on.prod
      (continuous_on.comp hf.continuous_on continuous_fst.continuous_on (subset.refl _)),
    apply h.congr,
    assume p hp,
    refl },
  suffices h : continuous_on (fderiv_within 𝕜 (I' ∘ f ∘ I.symm)
                     (I.symm ⁻¹' s ∩ range I)) (I '' s),
  { have C := continuous_on.comp h I.continuous_to_fun.continuous_on (subset.refl _),
    have A : continuous (λq : (E →L[𝕜] E') × E, q.1 q.2) :=
      is_bounded_bilinear_map_apply.continuous,
    have B : continuous_on (λp : H × E,
      (fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I)
                       (I p.1), p.2)) (prod.fst ⁻¹' s),
    { apply continuous_on.prod _ continuous_snd.continuous_on,
      refine (continuous_on.comp C continuous_fst.continuous_on _ : _),
      exact preimage_mono (subset_preimage_image _ _) },
    exact A.comp_continuous_on B },
  rw times_cont_mdiff_on_iff at hf,
  let x : H := I.symm (0 : E),
  let y : H' := I'.symm (0 : E'),
  have A := hf.2 x y,
  simp only [I.image_eq, inter_comm] with mfld_simps at A ⊢,
  apply A.continuous_on_fderiv_within _ hn,
  convert hs.unique_diff_on_target_inter x using 1,
  simp only [inter_comm] with mfld_simps
end

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative is
`C^m` when `m+1 ≤ n`. In this auxiliary lemma, we prove this fact when the source and target space
are model spaces in models with corners. The general fact is proved in
`times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within` -/
lemma times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within_aux
  {f : H → H'} {s : set H}
  (hf : times_cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  times_cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s)
    ((tangent_bundle.proj I H) ⁻¹' s) :=
begin
  have m_le_n : m ≤ n,
  { apply le_trans _ hmn,
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _,
    simpa only [add_zero] using this },
  have one_le_n : 1 ≤ n,
  { apply le_trans _ hmn,
    change 0 + 1 ≤ m + 1,
    exact add_le_add_right (zero_le _) _ },
  have U': unique_diff_on 𝕜 (range I ∩ I.symm ⁻¹' s),
  { assume y hy,
    simpa only [unique_mdiff_on, unique_mdiff_within_at, hy.1, inter_comm] with mfld_simps
      using hs (I.symm y) hy.2 },
  have U : unique_diff_on 𝕜 (set.prod (range I ∩ I.symm ⁻¹' s) (univ : set E)) :=
    U'.prod unique_diff_on_univ,
  rw times_cont_mdiff_on_iff,
  refine ⟨hf.continuous_on_tangent_map_within_aux one_le_n hs, λp q, _⟩,
  have A : (range I).prod univ ∩
      ((equiv.sigma_equiv_prod H E).symm ∘ λ (p : E × E), ((I.symm) p.fst, p.snd)) ⁻¹'
        (tangent_bundle.proj I H ⁻¹' s)
      = set.prod (range I ∩ I.symm ⁻¹' s) univ,
    by { ext ⟨x, v⟩, simp only with mfld_simps },
  suffices h : times_cont_diff_on 𝕜 m (((λ (p : H' × E'), (I' p.fst, p.snd)) ∘
      (equiv.sigma_equiv_prod H' E')) ∘ tangent_map_within I I' f s ∘
      ((equiv.sigma_equiv_prod H E).symm) ∘ λ (p : E × E), (I.symm p.fst, p.snd))
    ((range ⇑I ∩ ⇑(I.symm) ⁻¹' s).prod univ),
    by simpa [A] using h,
  change times_cont_diff_on 𝕜 m (λ (p : E × E),
    ((I' (f (I.symm p.fst)), ((mfderiv_within I I' f s (I.symm p.fst)) : E → E') p.snd) : E' × E'))
    (set.prod (range I ∩ I.symm ⁻¹' s) univ),
  -- check that all bits in this formula are `C^n`
  have hf' := times_cont_mdiff_on_iff.1 hf,
  have A : times_cont_diff_on 𝕜 m (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) :=
    by simpa only with mfld_simps using (hf'.2 (I.symm 0) (I'.symm 0)).of_le m_le_n,
  have B : times_cont_diff_on 𝕜 m ((I' ∘ f ∘ I.symm) ∘ prod.fst)
           (set.prod (range I ∩ I.symm ⁻¹' s) (univ : set E)) :=
    A.comp (times_cont_diff_fst.times_cont_diff_on) (prod_subset_preimage_fst _ _),
  suffices C : times_cont_diff_on 𝕜 m (λ (p : E × E),
    ((fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) p.1 : _) p.2))
    (set.prod (range I ∩ I.symm ⁻¹' s) univ),
  { apply times_cont_diff_on.prod B _,
    apply C.congr (λp hp, _),
    simp only with mfld_simps at hp,
    simp only [mfderiv_within, hf.mdifferentiable_on one_le_n _ hp.2, hp.1, dif_pos]
      with mfld_simps },
  have D : times_cont_diff_on 𝕜 m (λ x,
    (fderiv_within 𝕜 (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) x))
    (range I ∩ I.symm ⁻¹' s),
  { have : times_cont_diff_on 𝕜 n (I' ∘ f ∘ I.symm) (range I ∩ I.symm ⁻¹' s) :=
      by simpa only with mfld_simps using (hf'.2 (I.symm 0) (I'.symm 0)),
    simpa only [inter_comm] using this.fderiv_within U' hmn },
  have := D.comp (times_cont_diff_fst.times_cont_diff_on) (prod_subset_preimage_fst _ _),
  have := times_cont_diff_on.prod this (times_cont_diff_snd.times_cont_diff_on),
  exact is_bounded_bilinear_map_apply.times_cont_diff.comp_times_cont_diff_on this,
end

include Is I's

/-- If a function is `C^n` on a domain with unique derivatives, then its bundled derivative
is `C^m` when `m+1 ≤ n`. -/
theorem times_cont_mdiff_on.times_cont_mdiff_on_tangent_map_within
  (hf : times_cont_mdiff_on I I' n f s) (hmn : m + 1 ≤ n) (hs : unique_mdiff_on I s) :
  times_cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s)
  ((tangent_bundle.proj I M) ⁻¹' s) :=
begin
  /- The strategy of the proof is to avoid unfolding the definitions, and reduce by functoriality
  to the case of functions on the model spaces, where we have already proved the result.
  Let `l` and `r` be the charts to the left and to the right, so that we have
  ```
     l^{-1}      f       r
  H --------> M ---> M' ---> H'
  ```
  Then the tangent map `T(r ∘ f ∘ l)` is smooth by a previous result. Consider the composition
  ```
      Tl        T(r ∘ f ∘ l^{-1})         Tr^{-1}
  TM -----> TH -------------------> TH' ---------> TM'
  ```
  where `Tr^{-1}` and `Tl` are the tangent maps of `r^{-1}` and `l`. Writing `Tl` and `Tr^{-1}` as
  composition of charts (called `Dl` and `il` for `l` and `Dr` and `ir` in the proof below), it
  follows that they are smooth. The composition of all these maps is `Tf`, and is therefore smooth
  as a composition of smooth maps.
  -/
  have m_le_n : m ≤ n,
  { apply le_trans _ hmn,
    have : m + 0 ≤ m + 1 := add_le_add_left (zero_le _) _,
    simpa only [add_zero] },
  have one_le_n : 1 ≤ n,
  { apply le_trans _ hmn,
    change 0 + 1 ≤ m + 1,
    exact add_le_add_right (zero_le _) _ },
  /- First step: local reduction on the space, to a set `s'` which is contained in chart domains. -/
  refine times_cont_mdiff_on_of_locally_times_cont_mdiff_on (λp hp, _),
  have hf' := times_cont_mdiff_on_iff.1 hf,
  simp [tangent_bundle.proj] at hp,
  let l  := chart_at H p.1,
  set Dl := chart_at (model_prod H E) p with hDl,
  let r  := chart_at H' (f p.1),
  let Dr := chart_at (model_prod H' E') (tangent_map_within I I' f s p),
  let il := chart_at (model_prod H E) (tangent_map I I l p),
  let ir := chart_at (model_prod H' E') (tangent_map I I' (r ∘ f) p),
  let s' := f ⁻¹' r.source ∩ s ∩ l.source,
  let s'_lift := (tangent_bundle.proj I M)⁻¹' s',
  let s'l := l.target ∩ l.symm ⁻¹' s',
  let s'l_lift := (tangent_bundle.proj I H) ⁻¹' s'l,
  rcases continuous_on_iff'.1 hf'.1 r.source r.open_source with ⟨o, o_open, ho⟩,
  suffices h : times_cont_mdiff_on I.tangent I'.tangent m (tangent_map_within I I' f s) s'_lift,
  { refine ⟨(tangent_bundle.proj I M)⁻¹' (o ∩ l.source), _, _, _⟩,
    show is_open ((tangent_bundle.proj I M)⁻¹' (o ∩ l.source)), from
      (is_open.inter o_open l.open_source).preimage (tangent_bundle_proj_continuous _ _) ,
    show p ∈ tangent_bundle.proj I M ⁻¹' (o ∩ l.source),
    { simp [tangent_bundle.proj] at ⊢,
      have : p.1 ∈ f ⁻¹' r.source ∩ s, by simp [hp],
      rw ho at this,
      exact this.1 },
    { have : tangent_bundle.proj I M ⁻¹' s ∩ tangent_bundle.proj I M ⁻¹' (o ∩ l.source) = s'_lift,
      { dsimp only [s'_lift, s'], rw [ho], mfld_set_tac },
      rw this,
      exact h } },
  /- Second step: check that all functions are smooth, and use the chain rule to write the bundled
  derivative as a composition of a function between model spaces and of charts.
  Convention: statements about the differentiability of `a ∘ b ∘ c` are named `diff_abc`. Statements
  about differentiability in the bundle have a `_lift` suffix. -/
  have U' : unique_mdiff_on I s',
  { apply unique_mdiff_on.inter _ l.open_source,
    rw [ho, inter_comm],
    exact hs.inter o_open },
  have U'l : unique_mdiff_on I s'l :=
    U'.unique_mdiff_on_preimage (mdifferentiable_chart _ _),
  have diff_f : times_cont_mdiff_on I I' n f s' :=
    hf.mono (by mfld_set_tac),
  have diff_r : times_cont_mdiff_on I' I' n r r.source :=
    times_cont_mdiff_on_chart,
  have diff_rf : times_cont_mdiff_on I I' n (r ∘ f) s',
  { apply times_cont_mdiff_on.comp diff_r diff_f (λx hx, _),
    simp only [s'] with mfld_simps at hx, simp only [hx] with mfld_simps },
  have diff_l : times_cont_mdiff_on I I n l.symm s'l,
  { have A : times_cont_mdiff_on I I n l.symm l.target :=
      times_cont_mdiff_on_chart_symm,
    exact A.mono (by mfld_set_tac) },
  have diff_rfl : times_cont_mdiff_on I I' n (r ∘ f ∘ l.symm) s'l,
  { apply times_cont_mdiff_on.comp diff_rf diff_l,
    mfld_set_tac },
  have diff_rfl_lift : times_cont_mdiff_on I.tangent I'.tangent m
      (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l) s'l_lift :=
    diff_rfl.times_cont_mdiff_on_tangent_map_within_aux hmn U'l,
  have diff_irrfl_lift : times_cont_mdiff_on I.tangent I'.tangent m
      (ir ∘ (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l)) s'l_lift,
  { have A : times_cont_mdiff_on I'.tangent I'.tangent m ir ir.source := times_cont_mdiff_on_chart,
    exact times_cont_mdiff_on.comp A diff_rfl_lift (λp hp, by simp only [ir] with mfld_simps) },
  have diff_Drirrfl_lift : times_cont_mdiff_on I.tangent I'.tangent m
    (Dr.symm ∘ (ir ∘ (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l))) s'l_lift,
  { have A : times_cont_mdiff_on I'.tangent I'.tangent m Dr.symm Dr.target :=
      times_cont_mdiff_on_chart_symm,
    apply times_cont_mdiff_on.comp A diff_irrfl_lift (λp hp, _),
    simp only [s'l_lift, tangent_bundle.proj] with mfld_simps at hp,
    simp only [ir, @local_equiv.refl_coe (model_prod H' E'), hp] with mfld_simps },
  -- conclusion of this step: the composition of all the maps above is smooth
  have diff_DrirrflilDl : times_cont_mdiff_on I.tangent I'.tangent m
    (Dr.symm ∘ (ir ∘ (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l)) ∘
      (il.symm ∘ Dl)) s'_lift,
  { have A : times_cont_mdiff_on I.tangent I.tangent m Dl Dl.source := times_cont_mdiff_on_chart,
    have A' : times_cont_mdiff_on I.tangent I.tangent m Dl s'_lift,
    { apply A.mono (λp hp, _),
      simp only [s'_lift, tangent_bundle.proj] with mfld_simps at hp,
      simp only [Dl, hp] with mfld_simps },
    have B : times_cont_mdiff_on I.tangent I.tangent m il.symm il.target :=
      times_cont_mdiff_on_chart_symm,
    have C : times_cont_mdiff_on I.tangent I.tangent m (il.symm ∘ Dl) s'_lift :=
      times_cont_mdiff_on.comp B A' (λp hp, by simp only [il] with mfld_simps),
    apply times_cont_mdiff_on.comp diff_Drirrfl_lift C (λp hp, _),
    simp only [s'_lift, tangent_bundle.proj] with mfld_simps at hp,
    simp only [il, s'l_lift, hp, tangent_bundle.proj] with mfld_simps },
  /- Third step: check that the composition of all the maps indeed coincides with the derivative we
  are looking for -/
  have eq_comp : ∀q ∈ s'_lift, tangent_map_within I I' f s q =
      (Dr.symm ∘ ir ∘ (tangent_map_within I I' (r ∘ f ∘ l.symm) s'l) ∘
      (il.symm ∘ Dl)) q,
  { assume q hq,
    simp only [s'_lift, tangent_bundle.proj] with mfld_simps at hq,
    have U'q : unique_mdiff_within_at I s' q.1,
      by { apply U', simp only [hq, s'] with mfld_simps },
    have U'lq : unique_mdiff_within_at I s'l (Dl q).1,
      by { apply U'l, simp only [hq, s'l] with mfld_simps },
    have A : tangent_map_within I I' ((r ∘ f) ∘ l.symm) s'l (il.symm (Dl q)) =
      tangent_map_within I I' (r ∘ f) s' (tangent_map_within I I l.symm s'l (il.symm (Dl q))),
    { refine tangent_map_within_comp_at (il.symm (Dl q)) _ _ (λp hp, _) U'lq,
      { apply diff_rf.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { apply diff_l.mdifferentiable_on one_le_n,
        simp only [s'l, hq] with mfld_simps },
      { simp only with mfld_simps at hp, simp only [hp] with mfld_simps } },
    have B : tangent_map_within I I l.symm s'l (il.symm (Dl q)) = q,
    { have : tangent_map_within I I l.symm s'l (il.symm (Dl q))
        = tangent_map I I l.symm (il.symm (Dl q)),
      { refine tangent_map_within_eq_tangent_map U'lq _,
        refine mdifferentiable_at_atlas_symm _ (chart_mem_atlas _ _) _,
        simp only [hq] with mfld_simps },
      rw [this, tangent_map_chart_symm, hDl],
      { simp only [hq] with mfld_simps,
        have : q ∈ (chart_at (model_prod H E) p).source, by simp only [hq] with mfld_simps,
        exact (chart_at (model_prod H E) p).left_inv this },
      { simp only [hq] with mfld_simps } },
    have C : tangent_map_within I I' (r ∘ f) s' q
      = tangent_map_within I' I' r r.source (tangent_map_within I I' f s' q),
    { refine tangent_map_within_comp_at q _ _ (λr hr, _) U'q,
      { apply diff_r.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { apply diff_f.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { simp only [s'] with mfld_simps at hr,
        simp only [hr] with mfld_simps } },
    have D : Dr.symm (ir (tangent_map_within I' I' r r.source (tangent_map_within I I' f s' q)))
      = tangent_map_within I I' f s' q,
    { have A : tangent_map_within I' I' r r.source (tangent_map_within I I' f s' q) =
             tangent_map I' I' r (tangent_map_within I I' f s' q),
      { apply tangent_map_within_eq_tangent_map,
        { apply is_open.unique_mdiff_within_at _ r.open_source, simp [hq] },
        { refine mdifferentiable_at_atlas _ (chart_mem_atlas _ _) _,
          simp only [hq] with mfld_simps } },
      have : f p.1 = (tangent_map_within I I' f s p).1 := rfl,
      rw [A],
      dsimp [r, Dr],
      rw [this, tangent_map_chart],
      { simp only [hq] with mfld_simps,
        have : tangent_map_within I I' f s' q ∈
          (chart_at (model_prod H' E') (tangent_map_within I I' f s p)).source,
            by simp only [hq] with mfld_simps,
        exact (chart_at (model_prod H' E') (tangent_map_within I I' f s p)).left_inv this },
      { simp only [hq] with mfld_simps } },
    have E : tangent_map_within I I' f s' q = tangent_map_within I I' f s q,
    { refine tangent_map_within_subset (by mfld_set_tac) U'q _,
      apply hf.mdifferentiable_on one_le_n,
      simp only [hq] with mfld_simps },
    simp only [(∘), A, B, C, D, E.symm] },
  exact diff_DrirrflilDl.congr eq_comp,
end

/-- If a function is `C^n` on a domain with unique derivatives, with `1 ≤ n`, then its bundled
derivative is continuous there. -/
theorem times_cont_mdiff_on.continuous_on_tangent_map_within
  (hf : times_cont_mdiff_on I I' n f s) (hmn : 1 ≤ n) (hs : unique_mdiff_on I s) :
  continuous_on (tangent_map_within I I' f s) ((tangent_bundle.proj I M) ⁻¹' s) :=
begin
  have : times_cont_mdiff_on I.tangent I'.tangent 0 (tangent_map_within I I' f s)
         ((tangent_bundle.proj I M) ⁻¹' s) :=
    hf.times_cont_mdiff_on_tangent_map_within hmn hs,
  exact this.continuous_on
end

/-- If a function is `C^n`, then its bundled derivative is `C^m` when `m+1 ≤ n`. -/
theorem times_cont_mdiff.times_cont_mdiff_tangent_map
  (hf : times_cont_mdiff I I' n f) (hmn : m + 1 ≤ n) :
  times_cont_mdiff I.tangent I'.tangent m (tangent_map I I' f) :=
begin
  rw ← times_cont_mdiff_on_univ at hf ⊢,
  convert hf.times_cont_mdiff_on_tangent_map_within hmn unique_mdiff_on_univ,
  rw tangent_map_within_univ
end

/-- If a function is `C^n`, with `1 ≤ n`, then its bundled derivative is continuous. -/
theorem times_cont_mdiff.continuous_tangent_map
  (hf : times_cont_mdiff I I' n f) (hmn : 1 ≤ n) :
  continuous (tangent_map I I' f) :=
begin
  rw ← times_cont_mdiff_on_univ at hf,
  rw continuous_iff_continuous_on_univ,
  convert hf.continuous_on_tangent_map_within hmn unique_mdiff_on_univ,
  rw tangent_map_within_univ
end

end tangent_map

/-! ### Smoothness of the projection in a basic smooth bundle -/

namespace basic_smooth_bundle_core

variables (Z : basic_smooth_bundle_core I M E')

lemma times_cont_mdiff_proj :
  times_cont_mdiff ((I.prod 𝓘(𝕜, E'))) I n
    Z.to_topological_fiber_bundle_core.proj :=
begin
  assume x,
  rw [times_cont_mdiff_at, times_cont_mdiff_within_at_iff],
  refine ⟨Z.to_topological_fiber_bundle_core.continuous_proj.continuous_at.continuous_within_at, _⟩,
  simp only [(∘), chart_at, chart] with mfld_simps,
  apply times_cont_diff_within_at_fst.congr,
  { rintros ⟨a, b⟩ hab,
    simp only with mfld_simps at hab,
    simp only [hab] with mfld_simps },
  { simp only with mfld_simps }
end

lemma smooth_proj :
  smooth ((I.prod 𝓘(𝕜, E'))) I Z.to_topological_fiber_bundle_core.proj :=
times_cont_mdiff_proj Z

lemma times_cont_mdiff_on_proj {s : set (Z.to_topological_fiber_bundle_core.total_space)} :
  times_cont_mdiff_on ((I.prod 𝓘(𝕜, E'))) I n
    Z.to_topological_fiber_bundle_core.proj s :=
Z.times_cont_mdiff_proj.times_cont_mdiff_on

lemma smooth_on_proj {s : set (Z.to_topological_fiber_bundle_core.total_space)} :
  smooth_on ((I.prod 𝓘(𝕜, E'))) I Z.to_topological_fiber_bundle_core.proj s :=
times_cont_mdiff_on_proj Z

lemma times_cont_mdiff_at_proj {p : Z.to_topological_fiber_bundle_core.total_space} :
  times_cont_mdiff_at ((I.prod 𝓘(𝕜, E'))) I n
    Z.to_topological_fiber_bundle_core.proj p :=
Z.times_cont_mdiff_proj.times_cont_mdiff_at

lemma smooth_at_proj {p : Z.to_topological_fiber_bundle_core.total_space} :
  smooth_at ((I.prod 𝓘(𝕜, E'))) I Z.to_topological_fiber_bundle_core.proj p :=
Z.times_cont_mdiff_at_proj

lemma times_cont_mdiff_within_at_proj
  {s : set (Z.to_topological_fiber_bundle_core.total_space)}
  {p : Z.to_topological_fiber_bundle_core.total_space} :
  times_cont_mdiff_within_at ((I.prod 𝓘(𝕜, E'))) I n
    Z.to_topological_fiber_bundle_core.proj s p :=
Z.times_cont_mdiff_at_proj.times_cont_mdiff_within_at

lemma smooth_within_at_proj
  {s : set (Z.to_topological_fiber_bundle_core.total_space)}
  {p : Z.to_topological_fiber_bundle_core.total_space} :
  smooth_within_at ((I.prod 𝓘(𝕜, E'))) I
    Z.to_topological_fiber_bundle_core.proj s p :=
Z.times_cont_mdiff_within_at_proj

/-- If an element of `E'` is invariant under all coordinate changes, then one can define a
corresponding section of the fiber bundle, which is smooth. This applies in particular to the
zero section of a vector bundle. Another example (not yet defined) would be the identity
section of the endomorphism bundle of a vector bundle. -/
lemma smooth_const_section (v : E')
  (h : ∀ (i j : atlas H M), ∀ x ∈ i.1.source ∩ j.1.source, Z.coord_change i j (i.1 x) v = v) :
  smooth I ((I.prod 𝓘(𝕜, E')))
    (show M → Z.to_topological_fiber_bundle_core.total_space, from λ x, ⟨x, v⟩) :=
begin
  assume x,
  rw [times_cont_mdiff_at, times_cont_mdiff_within_at_iff],
  split,
  { apply continuous.continuous_within_at,
    apply topological_fiber_bundle_core.continuous_const_section,
    assume i j y hy,
    exact h _ _ _ hy },
  { have : times_cont_diff 𝕜 ⊤ (λ (y : E), (y, v)) := times_cont_diff_id.prod times_cont_diff_const,
    apply this.times_cont_diff_within_at.congr,
    { assume y hy,
      simp only with mfld_simps at hy,
      simp only [chart, hy, chart_at, prod.mk.inj_iff, to_topological_fiber_bundle_core]
        with mfld_simps,
      apply h,
      simp only [hy] with mfld_simps },
    { simp only [chart, chart_at, prod.mk.inj_iff, to_topological_fiber_bundle_core]
        with mfld_simps,
      apply h,
      simp only with mfld_simps } }
end

end basic_smooth_bundle_core

/-! ### Smoothness of the tangent bundle projection -/

namespace tangent_bundle

include Is

lemma times_cont_mdiff_proj :
  times_cont_mdiff I.tangent I n (proj I M) :=
basic_smooth_bundle_core.times_cont_mdiff_proj _

lemma smooth_proj : smooth I.tangent I (proj I M) :=
basic_smooth_bundle_core.smooth_proj _

lemma times_cont_mdiff_on_proj {s : set (tangent_bundle I M)} :
  times_cont_mdiff_on I.tangent I n (proj I M) s :=
basic_smooth_bundle_core.times_cont_mdiff_on_proj _

lemma smooth_on_proj {s : set (tangent_bundle I M)} :
  smooth_on I.tangent I (proj I M) s :=
basic_smooth_bundle_core.smooth_on_proj _

lemma times_cont_mdiff_at_proj {p : tangent_bundle I M} :
  times_cont_mdiff_at I.tangent I n
    (proj I M) p :=
basic_smooth_bundle_core.times_cont_mdiff_at_proj _

lemma smooth_at_proj {p : tangent_bundle I M} :
  smooth_at I.tangent I (proj I M) p :=
basic_smooth_bundle_core.smooth_at_proj _

lemma times_cont_mdiff_within_at_proj
  {s : set (tangent_bundle I M)} {p : tangent_bundle I M} :
  times_cont_mdiff_within_at I.tangent I n
    (proj I M) s p :=
basic_smooth_bundle_core.times_cont_mdiff_within_at_proj _

lemma smooth_within_at_proj
  {s : set (tangent_bundle I M)} {p : tangent_bundle I M} :
  smooth_within_at I.tangent I
    (proj I M) s p :=
basic_smooth_bundle_core.smooth_within_at_proj _

variables (I M)
/-- The zero section of the tangent bundle -/
def zero_section : M → tangent_bundle I M := λ x, ⟨x, 0⟩
variables {I M}

lemma smooth_zero_section : smooth I I.tangent (zero_section I M) :=
begin
  apply basic_smooth_bundle_core.smooth_const_section (tangent_bundle_core I M) 0,
  assume i j x hx,
  simp only [tangent_bundle_core, continuous_linear_map.map_zero] with mfld_simps
end

/-- The derivative of the zero section of the tangent bundle maps `⟨x, v⟩` to `⟨⟨x, 0⟩, ⟨v, 0⟩⟩`.

Note that, as currently framed, this is a statement in coordinates, thus reliant on the choice
of the coordinate system we use on the tangent bundle.

However, the result itself is coordinate-dependent only to the extent that the coordinates
determine a splitting of the tangent bundle.  Moreover, there is a canonical splitting at each
point of the zero section (since there is a canonical horizontal space there, the tangent space
to the zero section, in addition to the canonical vertical space which is the kernel of the
derivative of the projection), and this canonical splitting is also the one that comes from the
coordinates on the tangent bundle in our definitions. So this statement is not as crazy as it
may seem.

TODO define splittings of vector bundles; state this result invariantly. -/
lemma tangent_map_tangent_bundle_pure (p : tangent_bundle I M) :
  tangent_map I I.tangent (tangent_bundle.zero_section I M) p = ⟨⟨p.1, 0⟩, ⟨p.2, 0⟩⟩ :=
begin
  rcases p with ⟨x, v⟩,
  have N : I.symm ⁻¹' (chart_at H x).target ∈ 𝓝 (I ((chart_at H x) x)),
  { apply is_open.mem_nhds,
    apply (local_homeomorph.open_target _).preimage I.continuous_inv_fun,
    simp only with mfld_simps },
  have A : mdifferentiable_at I I.tangent (λ (x : M), (⟨x, 0⟩ : tangent_bundle I M)) x :=
    tangent_bundle.smooth_zero_section.mdifferentiable_at,
  have B : fderiv_within 𝕜 (λ (x_1 : E), (x_1, (0 : E))) (set.range ⇑I) (I ((chart_at H x) x)) v
    = (v, 0),
  { rw [fderiv_within_eq_fderiv, differentiable_at.fderiv_prod],
    { simp },
    { exact differentiable_at_id' },
    { exact differentiable_at_const _ },
    { exact model_with_corners.unique_diff_at_image I },
    { exact differentiable_at_id'.prod (differentiable_at_const _) } },
  simp only [tangent_bundle.zero_section, tangent_map, mfderiv,
    A, dif_pos, chart_at, basic_smooth_bundle_core.chart,
    basic_smooth_bundle_core.to_topological_fiber_bundle_core, tangent_bundle_core,
    function.comp, continuous_linear_map.map_zero] with mfld_simps,
  rw ← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (set.mem_range_self _)) at B,
  rw [← fderiv_within_inter N (I.unique_diff (I ((chart_at H x) x)) (set.mem_range_self _)), ← B],
  congr' 1,
  apply fderiv_within_congr _ (λ y hy, _),
  { simp only with mfld_simps, },
  { apply unique_diff_within_at.inter (I.unique_diff _ _) N,
    simp only with mfld_simps },
  { simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
end

end tangent_bundle

/-! ### Smoothness of standard maps associated to the product of manifolds -/

section prod_mk

lemma times_cont_mdiff_within_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : times_cont_mdiff_within_at I I' n f s x) (hg : times_cont_mdiff_within_at I J' n g s x) :
  times_cont_mdiff_within_at I (I'.prod J') n (λ x, (f x, g x)) s x :=
begin
  rw times_cont_mdiff_within_at_iff'' at *,
  exact ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩,
end

lemma times_cont_mdiff_within_at.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : times_cont_mdiff_within_at I 𝓘(𝕜, E') n f s x)
  (hg : times_cont_mdiff_within_at I 𝓘(𝕜, F') n g s x) :
  times_cont_mdiff_within_at I 𝓘(𝕜, E' × F') n (λ x, (f x, g x)) s x :=
begin
  rw times_cont_mdiff_within_at_iff'' at *,
  exact ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩,
end

lemma times_cont_mdiff_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : times_cont_mdiff_at I I' n f x) (hg : times_cont_mdiff_at I J' n g x) :
  times_cont_mdiff_at I (I'.prod J') n (λ x, (f x, g x)) x :=
hf.prod_mk hg

lemma times_cont_mdiff_at.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : times_cont_mdiff_at I 𝓘(𝕜, E') n f x) (hg : times_cont_mdiff_at I 𝓘(𝕜, F') n g x) :
  times_cont_mdiff_at I 𝓘(𝕜, E' × F') n (λ x, (f x, g x)) x :=
hf.prod_mk_space hg

lemma times_cont_mdiff_on.prod_mk {f : M → M'} {g : M → N'}
  (hf : times_cont_mdiff_on I I' n f s) (hg : times_cont_mdiff_on I J' n g s) :
  times_cont_mdiff_on I (I'.prod J') n (λ x, (f x, g x)) s :=
λ x hx, (hf x hx).prod_mk (hg x hx)

lemma times_cont_mdiff_on.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : times_cont_mdiff_on I 𝓘(𝕜, E') n f s) (hg : times_cont_mdiff_on I 𝓘(𝕜, F') n g s) :
  times_cont_mdiff_on I 𝓘(𝕜, E' × F') n (λ x, (f x, g x)) s :=
λ x hx, (hf x hx).prod_mk_space (hg x hx)

lemma times_cont_mdiff.prod_mk {f : M → M'} {g : M → N'}
  (hf : times_cont_mdiff I I' n f) (hg : times_cont_mdiff I J' n g) :
  times_cont_mdiff I (I'.prod J') n (λ x, (f x, g x)) :=
λ x, (hf x).prod_mk (hg x)

lemma times_cont_mdiff.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : times_cont_mdiff I 𝓘(𝕜, E') n f) (hg : times_cont_mdiff I 𝓘(𝕜, F') n g) :
  times_cont_mdiff I 𝓘(𝕜, E' × F') n (λ x, (f x, g x)) :=
λ x, (hf x).prod_mk_space (hg x)

lemma smooth_within_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : smooth_within_at I I' f s x) (hg : smooth_within_at I J' g s x) :
  smooth_within_at I (I'.prod J') (λ x, (f x, g x)) s x :=
hf.prod_mk hg

lemma smooth_within_at.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : smooth_within_at I 𝓘(𝕜, E') f s x) (hg : smooth_within_at I 𝓘(𝕜, F') g s x) :
  smooth_within_at I 𝓘(𝕜, E' × F') (λ x, (f x, g x)) s x :=
hf.prod_mk_space hg

lemma smooth_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : smooth_at I I' f x) (hg : smooth_at I J' g x) :
  smooth_at I (I'.prod J') (λ x, (f x, g x)) x :=
hf.prod_mk hg

lemma smooth_at.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : smooth_at I 𝓘(𝕜, E') f x) (hg : smooth_at I 𝓘(𝕜, F') g x) :
  smooth_at I 𝓘(𝕜, E' × F') (λ x, (f x, g x)) x :=
hf.prod_mk_space hg

lemma smooth_on.prod_mk {f : M → M'} {g : M → N'}
  (hf : smooth_on I I' f s) (hg : smooth_on I J' g s) :
  smooth_on I (I'.prod J') (λ x, (f x, g x)) s :=
hf.prod_mk hg

lemma smooth_on.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : smooth_on I 𝓘(𝕜, E') f s) (hg : smooth_on I 𝓘(𝕜, F') g s) :
  smooth_on I 𝓘(𝕜, E' × F') (λ x, (f x, g x)) s :=
hf.prod_mk_space hg

lemma smooth.prod_mk {f : M → M'} {g : M → N'}
  (hf : smooth I I' f) (hg : smooth I J' g) :
  smooth I (I'.prod J') (λ x, (f x, g x)) :=
hf.prod_mk hg

lemma smooth.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : smooth I 𝓘(𝕜, E') f) (hg : smooth I 𝓘(𝕜, F') g) :
  smooth I 𝓘(𝕜, E' × F') (λ x, (f x, g x)) :=
hf.prod_mk_space hg

end prod_mk

section projections

lemma times_cont_mdiff_within_at_fst {s : set (M × N)} {p : M × N} :
  times_cont_mdiff_within_at (I.prod J) I n prod.fst s p :=
begin
  rw times_cont_mdiff_within_at_iff,
  refine ⟨continuous_within_at_fst, _⟩,
  refine times_cont_diff_within_at_fst.congr (λ y hy, _) _,
  { simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  { simp only with mfld_simps }
end

lemma times_cont_mdiff_at_fst {p : M × N} :
  times_cont_mdiff_at (I.prod J) I n prod.fst p :=
times_cont_mdiff_within_at_fst

lemma times_cont_mdiff_on_fst {s : set (M × N)} :
  times_cont_mdiff_on (I.prod J) I n prod.fst s :=
λ x hx, times_cont_mdiff_within_at_fst

lemma times_cont_mdiff_fst :
  times_cont_mdiff (I.prod J) I n (@prod.fst M N) :=
λ x, times_cont_mdiff_at_fst

lemma smooth_within_at_fst {s : set (M × N)} {p : M × N} :
  smooth_within_at (I.prod J) I prod.fst s p :=
times_cont_mdiff_within_at_fst

lemma smooth_at_fst {p : M × N} :
  smooth_at (I.prod J) I prod.fst p :=
times_cont_mdiff_at_fst

lemma smooth_on_fst {s : set (M × N)} :
  smooth_on (I.prod J) I prod.fst s :=
times_cont_mdiff_on_fst

lemma smooth_fst :
  smooth (I.prod J) I (@prod.fst M N) :=
times_cont_mdiff_fst

lemma times_cont_mdiff_within_at_snd {s : set (M × N)} {p : M × N} :
  times_cont_mdiff_within_at (I.prod J) J n prod.snd s p :=
begin
  rw times_cont_mdiff_within_at_iff,
  refine ⟨continuous_within_at_snd, _⟩,
  refine times_cont_diff_within_at_snd.congr (λ y hy, _) _,
  { simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  { simp only with mfld_simps }
end

lemma times_cont_mdiff_at_snd {p : M × N} :
  times_cont_mdiff_at (I.prod J) J n prod.snd p :=
times_cont_mdiff_within_at_snd

lemma times_cont_mdiff_on_snd {s : set (M × N)} :
  times_cont_mdiff_on (I.prod J) J n prod.snd s :=
λ x hx, times_cont_mdiff_within_at_snd

lemma times_cont_mdiff_snd :
  times_cont_mdiff (I.prod J) J n (@prod.snd M N) :=
λ x, times_cont_mdiff_at_snd

lemma smooth_within_at_snd {s : set (M × N)} {p : M × N} :
  smooth_within_at (I.prod J) J prod.snd s p :=
times_cont_mdiff_within_at_snd

lemma smooth_at_snd {p : M × N} :
  smooth_at (I.prod J) J prod.snd p :=
times_cont_mdiff_at_snd

lemma smooth_on_snd {s : set (M × N)} :
  smooth_on (I.prod J) J prod.snd s :=
times_cont_mdiff_on_snd

lemma smooth_snd :
  smooth (I.prod J) J (@prod.snd M N) :=
times_cont_mdiff_snd

lemma smooth_iff_proj_smooth {f : M → M' × N'} :
  (smooth I (I'.prod J') f) ↔ (smooth I I' (prod.fst ∘ f)) ∧ (smooth I J' (prod.snd ∘ f)) :=
begin
  split,
  { intro h, exact ⟨smooth_fst.comp h, smooth_snd.comp h⟩ },
  { rintro ⟨h_fst, h_snd⟩, simpa only [prod.mk.eta] using h_fst.prod_mk h_snd, }
end

end projections

section prod_map

variables {g : N → N'} {r : set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma times_cont_mdiff_within_at.prod_map' {p : M × N}
  (hf : times_cont_mdiff_within_at I I' n f s p.1)
  (hg : times_cont_mdiff_within_at J J' n g r p.2) :
  times_cont_mdiff_within_at (I.prod J) (I'.prod J') n (prod.map f g) (s.prod r) p :=
(hf.comp p times_cont_mdiff_within_at_fst (prod_subset_preimage_fst _ _)).prod_mk $
hg.comp p times_cont_mdiff_within_at_snd (prod_subset_preimage_snd _ _)

lemma times_cont_mdiff_within_at.prod_map
  (hf : times_cont_mdiff_within_at I I' n f s x) (hg : times_cont_mdiff_within_at J J' n g r y) :
  times_cont_mdiff_within_at (I.prod J) (I'.prod J') n (prod.map f g) (s.prod r) (x, y) :=
times_cont_mdiff_within_at.prod_map' hf hg

lemma times_cont_mdiff_at.prod_map
  (hf : times_cont_mdiff_at I I' n f x) (hg : times_cont_mdiff_at J J' n g y) :
  times_cont_mdiff_at (I.prod J) (I'.prod J') n (prod.map f g) (x, y) :=
begin
  rw ← times_cont_mdiff_within_at_univ at *,
  convert hf.prod_map hg,
  exact univ_prod_univ.symm
end

lemma times_cont_mdiff_at.prod_map' {p : M × N}
  (hf : times_cont_mdiff_at I I' n f p.1) (hg : times_cont_mdiff_at J J' n g p.2) :
  times_cont_mdiff_at (I.prod J) (I'.prod J') n (prod.map f g) p :=
begin
  rcases p,
  exact hf.prod_map hg
end

lemma times_cont_mdiff_on.prod_map
  (hf : times_cont_mdiff_on I I' n f s) (hg : times_cont_mdiff_on J J' n g r) :
  times_cont_mdiff_on (I.prod J) (I'.prod J') n (prod.map f g) (s.prod r) :=
(hf.comp times_cont_mdiff_on_fst (prod_subset_preimage_fst _ _)).prod_mk $
hg.comp (times_cont_mdiff_on_snd) (prod_subset_preimage_snd _ _)

lemma times_cont_mdiff.prod_map
  (hf : times_cont_mdiff I I' n f) (hg : times_cont_mdiff J J' n g) :
  times_cont_mdiff (I.prod J) (I'.prod J') n (prod.map f g) :=
begin
  assume p,
  exact (hf p.1).prod_map' (hg p.2)
end

lemma smooth_within_at.prod_map
  (hf : smooth_within_at I I' f s x) (hg : smooth_within_at J J' g r y) :
  smooth_within_at (I.prod J) (I'.prod J') (prod.map f g) (s.prod r) (x, y) :=
hf.prod_map hg

lemma smooth_at.prod_map
  (hf : smooth_at I I' f x) (hg : smooth_at J J' g y) :
  smooth_at (I.prod J) (I'.prod J') (prod.map f g) (x, y) :=
hf.prod_map hg

lemma smooth_on.prod_map
  (hf : smooth_on I I' f s) (hg : smooth_on J J' g r) :
  smooth_on (I.prod J) (I'.prod J') (prod.map f g) (s.prod r) :=
hf.prod_map hg

lemma smooth.prod_map
  (hf : smooth I I' f) (hg : smooth J J' g) :
  smooth (I.prod J) (I'.prod J') (prod.map f g) :=
hf.prod_map hg

end prod_map

section pi_space

/-!
### Smoothness of functions with codomain `Π i, F i`

We have no `model_with_corners.pi` yet, so we prove lemmas about functions `f : M → Π i, F i` and
use `𝓘(𝕜, Π i, F i)` as the model space.
-/

variables {ι : Type*} [fintype ι] {Fi : ι → Type*} [Π i, normed_group (Fi i)]
  [Π i, normed_space 𝕜 (Fi i)] {φ : M → Π i, Fi i}

lemma times_cont_mdiff_within_at_pi_space :
  times_cont_mdiff_within_at I (𝓘(𝕜, Π i, Fi i)) n φ s x ↔
    ∀ i, times_cont_mdiff_within_at I (𝓘(𝕜, Fi i)) n (λ x, φ x i) s x :=
by simp only [times_cont_mdiff_within_at_iff'', continuous_within_at_pi,
  times_cont_diff_within_at_pi, forall_and_distrib, written_in_ext_chart_at,
  ext_chart_model_space_eq_id, (∘), local_equiv.refl_coe, id]

lemma times_cont_mdiff_on_pi_space :
  times_cont_mdiff_on I (𝓘(𝕜, Π i, Fi i)) n φ s ↔
    ∀ i, times_cont_mdiff_on I (𝓘(𝕜, Fi i)) n (λ x, φ x i) s :=
⟨λ h i x hx, times_cont_mdiff_within_at_pi_space.1 (h x hx) i,
  λ h x hx, times_cont_mdiff_within_at_pi_space.2 (λ i, h i x hx)⟩

lemma times_cont_mdiff_at_pi_space :
  times_cont_mdiff_at I (𝓘(𝕜, Π i, Fi i)) n φ x ↔
    ∀ i, times_cont_mdiff_at I (𝓘(𝕜, Fi i)) n (λ x, φ x i) x :=
times_cont_mdiff_within_at_pi_space

lemma times_cont_mdiff_pi_space :
  times_cont_mdiff I (𝓘(𝕜, Π i, Fi i)) n φ ↔
    ∀ i, times_cont_mdiff I (𝓘(𝕜, Fi i)) n (λ x, φ x i) :=
⟨λ h i x, times_cont_mdiff_at_pi_space.1 (h x) i,
  λ h x, times_cont_mdiff_at_pi_space.2 (λ i, h i x)⟩

lemma smooth_within_at_pi_space :
  smooth_within_at I (𝓘(𝕜, Π i, Fi i)) φ s x ↔
    ∀ i, smooth_within_at I (𝓘(𝕜, Fi i)) (λ x, φ x i) s x :=
times_cont_mdiff_within_at_pi_space

lemma smooth_on_pi_space :
  smooth_on I (𝓘(𝕜, Π i, Fi i)) φ s ↔ ∀ i, smooth_on I (𝓘(𝕜, Fi i)) (λ x, φ x i) s :=
times_cont_mdiff_on_pi_space

lemma smooth_at_pi_space :
  smooth_at I (𝓘(𝕜, Π i, Fi i)) φ x ↔ ∀ i, smooth_at I (𝓘(𝕜, Fi i)) (λ x, φ x i) x :=
times_cont_mdiff_at_pi_space

lemma smooth_pi_space :
  smooth I (𝓘(𝕜, Π i, Fi i)) φ ↔ ∀ i, smooth I (𝓘(𝕜, Fi i)) (λ x, φ x i) :=
times_cont_mdiff_pi_space

end pi_space

/-! ### Linear maps between normed spaces are smooth -/

lemma continuous_linear_map.times_cont_mdiff (L : E →L[𝕜] F) :
  times_cont_mdiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L :=
L.times_cont_diff.times_cont_mdiff

/-! ### Smoothness of standard operations -/

variables {V : Type*} [normed_group V] [normed_space 𝕜 V]

/-- On any vector space, multiplication by a scalar is a smooth operation. -/
lemma smooth_smul : smooth (𝓘(𝕜).prod 𝓘(𝕜, V)) 𝓘(𝕜, V) (λp : 𝕜 × V, p.1 • p.2) :=
smooth_iff.2 ⟨continuous_smul, λ x y, times_cont_diff_smul.times_cont_diff_on⟩

lemma smooth.smul {N : Type*} [topological_space N] [charted_space H N]
  {f : N → 𝕜} {g : N → V} (hf : smooth I 𝓘(𝕜) f) (hg : smooth I 𝓘(𝕜, V) g) :
  smooth I 𝓘(𝕜, V) (λ p, f p • g p) :=
smooth_smul.comp (hf.prod_mk hg)

lemma smooth_on.smul {N : Type*} [topological_space N] [charted_space H N]
  {f : N → 𝕜} {g : N → V} {s : set N} (hf : smooth_on I 𝓘(𝕜) f s) (hg : smooth_on I 𝓘(𝕜, V) g s) :
  smooth_on I 𝓘(𝕜, V) (λ p, f p • g p) s :=
smooth_smul.comp_smooth_on (hf.prod_mk hg)

lemma smooth_at.smul {N : Type*} [topological_space N] [charted_space H N]
  {f : N → 𝕜} {g : N → V} {x : N} (hf : smooth_at I 𝓘(𝕜) f x) (hg : smooth_at I 𝓘(𝕜, V) g x) :
  smooth_at I 𝓘(𝕜, V) (λ p, f p • g p) x :=
smooth_smul.smooth_at.comp _ (hf.prod_mk hg)
