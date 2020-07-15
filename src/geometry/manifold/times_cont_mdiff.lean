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

open set charted_space smooth_manifold_with_corners
open_locale topological_space manifold

/-! ### Definition of smooth functions between manifolds -/

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
{f f₁ : M → M'} {s s₁ t : set M} {x : M}
{m n : with_top ℕ}

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
      by { rw [model_with_corners.left_inv], exact mem_nhds_sets u_open xu },
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
    convert h.comp' this using 1,
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
    convert this.comp h _,
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

/-- A function is `n` times continuously differentiable at a point in a manifold if
it is continuous and it is `n` times continuously differentiable around this point, when
read in the preferred chart at this point. -/
def times_cont_mdiff_at (n : with_top ℕ) (f : M → M') (x : M) :=
times_cont_mdiff_within_at I I' n f univ x

/-- A function is `n` times continuously differentiable in a set of a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable on this set in the charts
around these points. -/
def times_cont_mdiff_on (n : with_top ℕ) (f : M → M') (s : set M) :=
∀ x ∈ s, times_cont_mdiff_within_at I I' n f s x

/-- A function is `n` times continuously differentiable in a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable in the charts
around these points. -/
def times_cont_mdiff (n : with_top ℕ) (f : M → M') :=
∀ x, times_cont_mdiff_at I I' n f x

/-! ### Basic properties of smooth functions between manifolds -/

variables {I I'}

lemma times_cont_mdiff.times_cont_mdiff_at (h : times_cont_mdiff I I' n f) :
  times_cont_mdiff_at I I' n f x :=
h x

lemma times_cont_mdiff_within_at_univ :
  times_cont_mdiff_within_at I I' n f univ x ↔ times_cont_mdiff_at I I' n f x :=
iff.rfl

lemma times_cont_mdiff_on_univ :
  times_cont_mdiff_on I I' n f univ ↔ times_cont_mdiff I I' n f :=
by simp only [times_cont_mdiff_on, times_cont_mdiff, times_cont_mdiff_within_at_univ,
  forall_prop_of_true, mem_univ]

include Is I's

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
lemma times_cont_mdiff_on_iff :
  times_cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    ∀ (x : M) (y : M'), times_cont_diff_on 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source)) :=
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
    convert (((times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
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

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
lemma times_cont_mdiff_iff :
  times_cont_mdiff I I' n f ↔ continuous f ∧
    ∀ (x : M) (y : M'), times_cont_diff_on 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' y).source)) :=
by simp [← times_cont_mdiff_on_univ, times_cont_mdiff_on_iff, continuous_iff_continuous_on_univ]

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

lemma times_cont_mdiff_within_at.of_succ {n : ℕ} (h : times_cont_mdiff_within_at I I' n.succ f s x) :
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
    exact mem_nhds_sets (ext_chart_at_open_source I' (f x)) (mem_ext_chart_source I' (f x)) },
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

/-! ### `C^∞` smoothness -/

lemma times_cont_mdiff_within_at_top :
  times_cont_mdiff_within_at I I' ∞ f s x ↔ (∀n:ℕ, times_cont_mdiff_within_at I I' n f s x) :=
⟨λ h n, ⟨h.1, times_cont_diff_within_at_top.1 h.2 n⟩,
 λ H, ⟨(H 0).1, times_cont_diff_within_at_top.2 (λ n, (H n).2)⟩⟩

lemma times_cont_mdiff_at_top :
  times_cont_mdiff_at I I' ∞ f x ↔ (∀n:ℕ, times_cont_mdiff_at I I' n f x) :=
times_cont_mdiff_within_at_top

lemma times_cont_mdiff_on_top :
  times_cont_mdiff_on I I' ∞ f s ↔ (∀n:ℕ, times_cont_mdiff_on I I' n f s) :=
⟨λ h n, h.of_le le_top, λ h x hx, times_cont_mdiff_within_at_top.2 (λ n, h n x hx)⟩

lemma times_cont_mdiff_top :
  times_cont_mdiff I I' ∞ f ↔ (∀n:ℕ, times_cont_mdiff I I' n f) :=
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

lemma times_cont_mdiff_on.mono (hf : times_cont_mdiff_on I I' n f s) (hts : t ⊆ s) :
  times_cont_mdiff_on I I' n f t :=
λ x hx, (hf x (hts hx)).mono hts

lemma times_cont_mdiff.times_cont_mdiff_on (hf : times_cont_mdiff I I' n f) :
  times_cont_mdiff_on I I' n f s :=
λ x hx, (hf x).times_cont_mdiff_within_at

lemma times_cont_mdiff_within_at_inter' (ht : t ∈ nhds_within x s) :
  times_cont_mdiff_within_at I I' n f (s ∩ t) x ↔ times_cont_mdiff_within_at I I' n f s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_inter' ht

lemma times_cont_mdiff_within_at_inter (ht : t ∈ 𝓝 x) :
  times_cont_mdiff_within_at I I' n f (s ∩ t) x ↔ times_cont_mdiff_within_at I I' n f s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_inter ht

lemma times_cont_mdiff_within_at.times_cont_mdiff_at
  (h : times_cont_mdiff_within_at I I' n f s x) (ht : s ∈ 𝓝 x) :
  times_cont_mdiff_at I I' n f x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_of_lift_prop_within_at h ht

include Is I's

/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
lemma times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds {n : ℕ} :
  times_cont_mdiff_within_at I I' n f s x ↔
  ∃ u ∈ nhds_within x (insert x s), times_cont_mdiff_on I I' n f u :=
begin
  split,
  { assume h,
    -- the property is true in charts. We will pull such a good neighborhood in the chart to the
    -- manifold. For this, we need to restrict to a small enough set where everything makes sense
    obtain ⟨o, o_open, xo, ho, h'o⟩ : ∃ (o : set M),
      is_open o ∧ x ∈ o ∧ o ⊆ (chart_at H x).source ∧ o ∩ s ⊆ f ⁻¹' (chart_at H' (f x)).source,
    { have : (chart_at H' (f x)).source ∈ 𝓝 (f x) :=
        mem_nhds_sets (local_homeomorph.open_source _) (mem_chart_source H' (f x)),
      rcases mem_nhds_within.1 (h.1.preimage_mem_nhds_within this) with ⟨u, u_open, xu, hu⟩,
      refine ⟨u ∩ (chart_at H x).source, _, ⟨xu, mem_chart_source _ _⟩, _, _⟩,
      { exact is_open_inter u_open (local_homeomorph.open_source _) },
      { assume y hy, exact hy.2 },
      { assume y hy, exact hu ⟨hy.1.1, hy.2⟩ } },
    have h' : times_cont_mdiff_within_at I I' n f (s ∩ o) x := h.mono (inter_subset_left _ _),
    simp only [times_cont_mdiff_within_at, lift_prop_within_at, times_cont_diff_within_at_prop] at h',
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
    show v ∈ nhds_within x (insert x s),
    { rw nhds_within_restrict _ xo o_open,
      refine filter.inter_mem_sets self_mem_nhds_within _,
      suffices : u ∈ nhds_within (ext_chart_at I x x) ((ext_chart_at I x) '' (insert x s ∩ o)),
        from (ext_chart_at_continuous_at I x).continuous_within_at.preimage_mem_nhds_within' this,
      apply nhds_within_mono _ _ u_nhds,
      rw image_subset_iff,
      assume y hy,
      rcases hy.1 with rfl|h',
      { simp only [mem_insert_iff] with mfld_simps },
      { simp only [mem_insert_iff, ho hy.2, h', h'o ⟨hy.2, h'⟩] with mfld_simps } },
    show times_cont_mdiff_on I I' n f v,
    { assume y hy,
      apply (((times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart
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
  (h : times_cont_mdiff_within_at I I' n f s x) (h₁ : f₁ =ᶠ[nhds_within x s] f)
  (hx : f₁ x = f x) : times_cont_mdiff_within_at I I' n f₁ s x :=
(times_cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr_of_eventually_eq
  h h₁ hx

lemma filter.eventually_eq.times_cont_mdiff_within_at_iff
  (h₁ : f₁ =ᶠ[nhds_within x s] f) (hx : f₁ x = f x) :
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
[smooth_manifold_with_corners I'' M'']

include Is I's

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma times_cont_mdiff_on.comp {t : set M'} {g : M' → M''}
  (hg : times_cont_mdiff_on I' I'' n g t) (hf : times_cont_mdiff_on I I' n f s)
  (st : s ⊆ f ⁻¹' t) : times_cont_mdiff_on I I'' n (g ∘ f) s :=
begin
  rw times_cont_mdiff_on_iff at hf hg ⊢,
  have cont_gf : continuous_on (g ∘ f) s := continuous_on.comp hg.1 hf.1 st,
  refine ⟨cont_gf, λx y, _⟩,
  apply times_cont_diff_on_of_locally_times_cont_diff_on,
  assume z hz,
  let x' := (ext_chart_at I x).symm z,
  have x'_source : x' ∈ (ext_chart_at I x).source := (ext_chart_at I x).map_target hz.1,
  obtain ⟨o, o_open, zo, o_subset⟩ : ∃ o, is_open o ∧ z ∈ o ∧
    o ∩ (((ext_chart_at I x).symm ⁻¹' s ∩ range I)) ⊆
      (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' (f x')).source),
  { have x'z : (ext_chart_at I x) x' = z, by simp only [x', hz.1, -ext_chart_at] with mfld_simps,
    have : continuous_within_at f s x' := hf.1 _ hz.2.1,
    have : f ⁻¹' (ext_chart_at I' (f x')).source ∈ nhds_within x' s :=
      this.preimage_mem_nhds_within
      (mem_nhds_sets (ext_chart_at_open_source I' (f x')) (mem_ext_chart_source I' (f x'))),
    have : (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' (f x')).source) ∈
      nhds_within ((ext_chart_at I x) x') ((ext_chart_at I x).symm ⁻¹' s ∩ range I) :=
      ext_chart_preimage_mem_nhds_within' _ _ x'_source this,
    rw x'z at this,
    exact mem_nhds_within.1 this },
  refine ⟨o, o_open, zo, _⟩,
  let u := ((ext_chart_at I x).target ∩
         (ext_chart_at I x).symm ⁻¹' (s ∩ g ∘ f ⁻¹' (ext_chart_at I'' y).source) ∩ o),
  -- it remains to show that `g ∘ f` read in the charts is `C^n` on `u`
  have u_subset : u ⊆ (ext_chart_at I x).target ∩
    (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' (f x')).source),
  { rintros p ⟨⟨hp₁, ⟨hp₂, hp₃⟩⟩, hp₄⟩,
    refine ⟨hp₁, ⟨hp₂, o_subset ⟨hp₄, ⟨hp₂, _⟩⟩⟩⟩,
    have := hp₁.1,
    rwa model_with_corners.target at this },
  have : times_cont_diff_on 𝕜 n (((ext_chart_at I'' y) ∘ g ∘ (ext_chart_at I' (f x')).symm) ∘
    ((ext_chart_at I' (f x')) ∘ f ∘ (ext_chart_at I x).symm)) u,
  { refine times_cont_diff_on.comp (hg.2 (f x') y) ((hf.2 x (f x')).mono u_subset) (λp hp, _),
    simp only [local_equiv.map_source _ (u_subset hp).2.2, local_equiv.left_inv _ (u_subset hp).2.2,
      -ext_chart_at] with mfld_simps,
    exact ⟨st (u_subset hp).2.1, hp.1.2.2⟩ },
  refine this.congr (λp hp, _),
  simp only [local_equiv.left_inv _ (u_subset hp).2.2, -ext_chart_at] with mfld_simps
end

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
lemma times_cont_mdiff_within_at.comp {t : set M'} {g : M' → M''}
  (hg : times_cont_mdiff_within_at I' I'' n g t (f x))
  (hf : times_cont_mdiff_within_at I I' n f s x)
  (st : s ⊆ f ⁻¹' t) : times_cont_mdiff_within_at I I'' n (g ∘ f) s x :=
begin
  apply times_cont_mdiff_within_at_iff_nat.2 (λ m hm, _),
  rcases times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds.1 (hg.of_le hm) with ⟨v, v_nhds, hv⟩,
  rcases times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds.1 (hf.of_le hm) with ⟨u, u_nhds, hu⟩,
  apply times_cont_mdiff_within_at_iff_times_cont_mdiff_on_nhds.2 ⟨_, _, hv.comp' hu⟩,
  apply filter.inter_mem_sets u_nhds,
  suffices h : v ∈ nhds_within (f x) (f '' s),
  { convert mem_nhds_within_insert (hf.continuous_within_at.preimage_mem_nhds_within' h),
    rw insert_eq_of_mem,
    apply mem_of_mem_nhds_within (mem_insert (f x) t) v_nhds },
  apply nhds_within_mono _ _ v_nhds,
  rw image_subset_iff,
  exact subset.trans st (preimage_mono (subset_insert _ _))
end

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
lemma times_cont_mdiff_within_at.comp' {t : set M'} {g : M' → M''}
  (hg : times_cont_mdiff_within_at I' I'' n g t (f x))
  (hf : times_cont_mdiff_within_at I I' n f s x) :
  times_cont_mdiff_within_at I I'' n (g ∘ f) (s ∩ f⁻¹' t) x :=
hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of `C^n` functions at points is `C^n`. -/
lemma times_cont_mdiff_at.comp {g : M' → M''}
  (hg : times_cont_mdiff_at I' I'' n g (f x)) (hf : times_cont_mdiff_at I I' n f x) :
  times_cont_mdiff_at I I'' n (g ∘ f) x :=
hg.comp hf subset_preimage_univ

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

lemma times_cont_mdiff_on_id : times_cont_mdiff_on I I n (id : M → M) s :=
times_cont_mdiff_id.times_cont_mdiff_on

lemma times_cont_mdiff_at_id : times_cont_mdiff_at I I n (id : M → M) x :=
times_cont_mdiff_id.times_cont_mdiff_at

lemma times_cont_mdiff_within_at_id : times_cont_mdiff_within_at I I n (id : M → M) s x :=
times_cont_mdiff_at_id.times_cont_mdiff_within_at

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

lemma times_cont_mdiff_on_const : times_cont_mdiff_on I I' n (λ (x : M), c) s :=
times_cont_mdiff_const.times_cont_mdiff_on

lemma times_cont_mdiff_at_const : times_cont_mdiff_at I I' n (λ (x : M), c) x :=
times_cont_mdiff_const.times_cont_mdiff_at

lemma times_cont_mdiff_within_at_const : times_cont_mdiff_within_at I I' n (λ (x : M), c) s x :=
times_cont_mdiff_at_const.times_cont_mdiff_within_at

end id

/-! ### Equivalence with the basic definition for functions between vector spaces -/

section vector_space

lemma times_cont_mdiff_within_at_iff_times_cont_diff_within_at {f : E → E'} {s : set E} {x : E} :
  times_cont_mdiff_within_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f s x
  ↔ times_cont_diff_within_at 𝕜 n f s x :=
begin
  simp only [times_cont_mdiff_within_at, lift_prop_within_at, times_cont_diff_within_at_prop,
    iff_def] with mfld_simps {contextual := tt},
  exact times_cont_diff_within_at.continuous_within_at
end

lemma times_cont_mdiff_at_iff_times_cont_diff_at {f : E → E'} {x : E} :
  times_cont_mdiff_at (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f x
  ↔ times_cont_diff_at 𝕜 n f x :=
by rw [← times_cont_mdiff_within_at_univ,
  times_cont_mdiff_within_at_iff_times_cont_diff_within_at, times_cont_diff_within_at_univ]

lemma times_cont_mdiff_on_iff_times_cont_diff_on {f : E → E'} {s : set E} :
  times_cont_mdiff_on (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f s
  ↔ times_cont_diff_on 𝕜 n f s :=
forall_congr $ by simp [times_cont_mdiff_within_at_iff_times_cont_diff_within_at]

lemma times_cont_mdiff_iff_times_cont_diff {f : E → E'} :
  times_cont_mdiff (model_with_corners_self 𝕜 E) (model_with_corners_self 𝕜 E') n f
  ↔ times_cont_diff 𝕜 n f :=
by rw [← times_cont_diff_on_univ, ← times_cont_mdiff_on_univ,
  times_cont_mdiff_on_iff_times_cont_diff_on]

end vector_space

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
  { have : ∀ (p : tangent_bundle I H), p ∈ tangent_bundle.proj I H ⁻¹' s →
      tangent_map_within I I' f s p =
      (f p.fst, ((fderiv_within 𝕜 (written_in_ext_chart_at I I' p.fst f)
      (I.symm ⁻¹' s ∩ range I) ((ext_chart_at I p.fst) p.fst)) : E →L[𝕜] E') p.snd),
    { rintros ⟨x, v⟩ hx,
      dsimp [tangent_map_within],
      ext, { refl },
      dsimp,
      apply congr_fun,
      apply congr_arg,
      rw mdifferentiable_within_at.mfderiv_within (hf.mdifferentiable_on hn x hx),
      refl },
    convert h.congr this,
    exact tangent_bundle_model_space_topology_eq_prod H I,
    exact tangent_bundle_model_space_topology_eq_prod H' I' },
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
    have A : continuous (λq : (E →L[𝕜] E') × E, q.1 q.2) := is_bounded_bilinear_map_apply.continuous,
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
  simp only [I.image, inter_comm] with mfld_simps at A ⊢,
  apply A.continuous_on_fderiv_within _ hn,
  convert hs.unique_diff_on x using 1,
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
  have A : (λ (p : E × E), (I.symm p.1, p.2)) ⁻¹' (tangent_bundle.proj I H ⁻¹' s)
           = set.prod (I.symm ⁻¹' s) univ,
    by { ext p, simp only [tangent_bundle.proj] with mfld_simps },
  -- unfold the definitions to reduce to a statement on vector spaces
  suffices h : times_cont_diff_on 𝕜 m
    ((λ (p : H' × E'), (I' p.1, p.2)) ∘ tangent_map_within I I' f s ∘
      (λ (p : E × E), (I.symm p.1, p.2))) (set.prod (range I ∩ I.symm ⁻¹' s) univ),
  by simp only [@local_equiv.refl_symm (model_prod H E), @local_equiv.refl_target (model_prod H E),
    @local_equiv.refl_source (model_prod H' E'), h, A] with mfld_simps,
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
     l      f       r
  H ---> M ---> M' ---> H'
  ```
  Then the derivative `D(r ∘ f ∘ l)` is smooth by a previous result. Consider the composition
  ```
      Dl^{-1}          il      D(r ∘ f ∘ l)       ir            Dr^{-1}
  TM ---------> H × E ---> TH -------------> TH' ---> H' × E' ----------> TM'
  ```
  where `Dr^{-1}` and `Dl^{-1}` denote the charts on `TM` and `TM'` (they are smooth, by definition
  of charts) and `ir` and `il` are charts of `TH` and `TH'`, also smooth (they are the identity,
  between two types which are defeq but which carry two manifold structures which are not defeq a
  priori, which is why they are needed here). The composition of all these maps is `Df`, and is
  therefore smooth as a composition of smooth maps.
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
  let Dl := chart_at (model_prod H E) p,
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
      tangent_bundle_proj_continuous _ _ _ (is_open_inter o_open l.open_source),
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
    have A : tangent_map_within I I' ((r ∘ f) ∘ l.symm) s'l (Dl q) =
      tangent_map_within I I' (r ∘ f) s' (tangent_map_within I I l.symm s'l (Dl q)),
    { refine tangent_map_within_comp_at (Dl q) _ _ (λp hp, _) U'lq,
      { apply diff_rf.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { apply diff_l.mdifferentiable_on one_le_n,
        simp only [s'l, hq] with mfld_simps },
      { simp only with mfld_simps at hp, simp only [hp] with mfld_simps } },
    have B : tangent_map_within I I l.symm s'l (Dl q) = q,
    { have : tangent_map_within I I l.symm s'l (Dl q) = tangent_map I I l.symm (Dl q),
      { refine tangent_map_within_eq_tangent_map U'lq _,
        refine mdifferentiable_at_atlas_symm _ (chart_mem_atlas _ _) _,
        simp only [hq] with mfld_simps },
      rw [this, tangent_map_chart_symm, local_homeomorph.left_inv];
      simp only [hq] with mfld_simps },
    have C : tangent_map_within I I' (r ∘ f) s' q
      = tangent_map_within I' I' r r.source (tangent_map_within I I' f s' q),
    { refine tangent_map_within_comp_at q _ _ (λr hr, _) U'q,
      { apply diff_r.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { apply diff_f.mdifferentiable_on one_le_n,
        simp only [hq] with mfld_simps },
      { simp only [s'] with mfld_simps at hr,
        simp only [hr] with mfld_simps } },
    have D : Dr.symm (tangent_map_within I' I' r r.source (tangent_map_within I I' f s' q))
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
      rw [this, tangent_map_chart, local_homeomorph.left_inv];
      simp only [hq] with mfld_simps },
    have M : tangent_map_within I I' f s' q = tangent_map_within I I' f s q,
    { refine tangent_map_within_subset (by mfld_set_tac) U'q _,
      apply hf.mdifferentiable_on one_le_n,
      simp only [hq] with mfld_simps },
    simp only [il, ir, A, B, C, D, M.symm] with mfld_simps },
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
