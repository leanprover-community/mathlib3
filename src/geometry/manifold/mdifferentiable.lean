/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import geometry.manifold.smooth_manifold_with_corners
import geometry.manifold.local_invariant_properties

/-!
# Differentiability of functions between smooth manifolds

Let `M` and `M'` be two smooth manifolds with corners over a field `𝕜` (with respective models with
corners `I` on `(E, H)` and `I'` on `(E', H')`), and let `f : M → M'`. We define the
differentiability of the function at a point, within a set or along the whole space, mimicking the
API for (Fréchet) differentiability.

## Main definitions

* `unique_mdiff_on I s` : predicate saying that, at each point of the set `s`, a function can have
  at most one derivative. This technical condition is important when we define
  `mfderiv_within` in `geometry/manifold/mfderiv`, as otherwise there is an arbitrary choice in the
  derivative, and many properties will fail (for instance the chain rule). This is analogous to
  `unique_diff_on 𝕜 s` in a vector space.

Let `f` be a map between smooth manifolds. The following definitions follow the `fderiv` API.

* `mdifferentiable_at I I' f x` : Prop expressing whether `f` is differentiable at `x`.
* `mdifferentiable_within_at 𝕜 f s x` : Prop expressing whether `f` is differentiable within `s`
  at `x`.
* `mdifferentiable_on I I' f s` : Prop expressing that `f` is differentiable on the set `s`.
* `mdifferentiable I I' f` : Prop expressing that `f` is differentiable everywhere.
* `tangent_map I I' f` : the derivative of `f`, as a map from the tangent bundle of `M` to the
  tangent bundle of `M'`.

We also establish results on the differentiability of charts and extended charts. For functions
between vector spaces, we show that the usual notions and the manifold notions coincide.

## Implementation notes

The tangent bundle is constructed using the machinery of topological fiber bundles, for which one
can define bundled morphisms and construct canonically maps from the total space of one bundle to
the total space of another one. One could use this mechanism to construct directly the derivative
of a smooth map. However, we want to define the derivative of any map (and let it be zero if the map
is not differentiable) to avoid proof arguments everywhere. This means we have to go back to the
details of the definition of the total space of a fiber bundle constructed from core, to cook up a
suitable definition of the derivative. It is the following: at each point, we have a preferred chart
(used to identify the fiber above the point with the model vector space in fiber bundles). Then one
should read the function using these preferred charts at `x` and `f x`, and take the derivative
of `f` in these charts.

Due to the fact that we are working in a model with corners, with an additional embedding `I` of the
model space `H` in the model vector space `E`, the charts taking values in `E` are not the original
charts of the manifold, but those ones composed with `I`, called extended charts. We define
`written_in_ext_chart I I' x f` for the function `f` written in the preferred extended charts. Then
the manifold derivative of `f`, at `x`, is just the usual derivative of
`written_in_ext_chart I I' x f`, at the point `(ext_chart_at I x) x`.

There is a subtelty with respect to continuity: if the function is not continuous, then the image
of a small open set around `x` will not be contained in the source of the preferred chart around
`f x`, which means that when reading `f` in the chart one is losing some information. To avoid this,
we include continuity in the definition of differentiablity (which is reasonable since with any
definition, differentiability implies continuity).

*Warning*: the derivative (even within a subset) is a linear map on the whole tangent space. Suppose
that one is given a smooth submanifold `N`, and a function which is smooth on `N` (i.e., its
restriction to the subtype  `N` is smooth). Then, in the whole manifold `M`, the property
`mdifferentiable_on I I' f N` holds. However, `mfderiv_within I I' f N` is not uniquely defined
(what values would one choose for vectors that are transverse to `N`?), which can create issues down
the road. The problem here is that knowing the value of `f` along `N` does not determine the
differential of `f` in all directions. This is in contrast to the case where `N` would be an open
subset, or a submanifold with boundary of maximal dimension, where this issue does not appear.
The predicate `unique_mdiff_on I N` indicates that the derivative along `N` is unique if it exists,
and is an assumption in most statements requiring a form of uniqueness.

On a vector space, the manifold derivative and the usual derivative are equal. This means in
particular that they live on the same space, i.e., the tangent space is defeq to the original vector
space. To get this property is a motivation for our definition of the tangent space as a single
copy of the vector space, instead of more usual definitions such as the space of derivations, or
the space of equivalence classes of smooth curves in the manifold.

## Tags
Derivative, manifold
-/

noncomputable theory
open_locale classical topology manifold

open set

universe u

section derivatives_definitions
/-!
### Derivative of maps between manifolds

The derivative of a smooth map `f` between smooth manifold `M` and `M'` at `x` is a bounded linear
map from the tangent space to `M` at `x`, to the tangent space to `M'` at `f x`. Since we defined
the tangent space using one specific chart, the formula for the derivative is written in terms of
this specific chart.

We use the names `mdifferentiable` and `mfderiv`, where the prefix letter `m` means "manifold".
-/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M']

/-- Property in the model space of a model with corners of being differentiable within at set at a
point, when read in the model vector space. This property will be lifted to manifolds to define
differentiable functions between manifolds. -/
def differentiable_within_at_prop (f : H → H') (s : set H) (x : H) : Prop :=
differentiable_within_at 𝕜 (I' ∘ f ∘ (I.symm)) (⇑(I.symm) ⁻¹' s ∩ set.range I) (I x)

/-- Being differentiable in the model space is a local property, invariant under smooth maps.
Therefore, it will lift nicely to manifolds. -/
lemma differentiable_within_at_local_invariant_prop :
  (cont_diff_groupoid ⊤ I).local_invariant_prop (cont_diff_groupoid ⊤ I')
    (differentiable_within_at_prop I I') :=
{ is_local :=
  begin
    assume s x u f u_open xu,
    have : I.symm ⁻¹' (s ∩ u) ∩ set.range I = (I.symm ⁻¹' s ∩ set.range I) ∩ I.symm ⁻¹' u,
      by simp only [set.inter_right_comm, set.preimage_inter],
    rw [differentiable_within_at_prop, differentiable_within_at_prop, this],
    symmetry,
    apply differentiable_within_at_inter,
    have : u ∈ 𝓝 (I.symm (I x)),
      by { rw [model_with_corners.left_inv], exact is_open.mem_nhds u_open xu },
    apply continuous_at.preimage_mem_nhds I.continuous_symm.continuous_at this,
  end,
  right_invariance' :=
  begin
    assume s x f e he hx h,
    rw differentiable_within_at_prop at h ⊢,
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)), by simp only [hx] with mfld_simps,
    rw this at h,
    have : I (e x) ∈ (I.symm) ⁻¹' e.target ∩ set.range I, by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he).2.cont_diff_within_at this),
    convert (h.comp' _ (this.differentiable_within_at le_top)).mono_of_mem _ using 1,
    { ext y, simp only with mfld_simps },
    refine mem_nhds_within.mpr ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm,
      by simp_rw [set.mem_preimage, I.left_inv, e.maps_to hx], _⟩,
    mfld_set_tac
  end,
  congr_of_forall :=
  begin
    assume s x f g h hx hf,
    apply hf.congr,
    { assume y hy,
      simp only with mfld_simps at hy,
      simp only [h, hy] with mfld_simps },
    { simp only [hx] with mfld_simps }
  end,
  left_invariance' :=
  begin
    assume s x f e' he' hs hx h,
    rw differentiable_within_at_prop at h ⊢,
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ (I'.symm ⁻¹' e'.source ∩ set.range I'),
      by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he').1.cont_diff_within_at A),
    convert (this.differentiable_within_at le_top).comp _ h _,
    { ext y, simp only with mfld_simps },
    { assume y hy, simp only with mfld_simps at hy, simpa only [hy] with mfld_simps using hs hy.1 }
  end }

/-- Predicate ensuring that, at a point and within a set, a function can have at most one
derivative. This is expressed using the preferred chart at the considered point. -/
def unique_mdiff_within_at (s : set M) (x : M) :=
unique_diff_within_at 𝕜 ((ext_chart_at I x).symm ⁻¹' s ∩ range I) ((ext_chart_at I x) x)

/-- Predicate ensuring that, at all points of a set, a function can have at most one derivative. -/
def unique_mdiff_on (s : set M) :=
∀x∈s, unique_mdiff_within_at I s x

/-- `mdifferentiable_within_at I I' f s x` indicates that the function `f` between manifolds
has a derivative at the point `x` within the set `s`.
This is a generalization of `differentiable_within_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` in `s` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def mdifferentiable_within_at (f : M → M') (s : set M) (x : M) :=
continuous_within_at f s x ∧
differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f)
  ((ext_chart_at I x).symm ⁻¹' s ∩ range I) ((ext_chart_at I x) x)

lemma mdifferentiable_within_at_iff_lift_prop_within_at (f : M → M') (s : set M) (x : M) :
  mdifferentiable_within_at I I' f s x
  ↔ lift_prop_within_at (differentiable_within_at_prop I I') f s x :=
by refl

/-- `mdifferentiable_at I I' f x` indicates that the function `f` between manifolds
has a derivative at the point `x`.
This is a generalization of `differentiable_at` to manifolds.

We require continuity in the definition, as otherwise points close to `x` could be sent by
`f` outside of the chart domain around `f x`. Then the chart could do anything to the image points,
and in particular by coincidence `written_in_ext_chart_at I I' x f` could be differentiable, while
this would not mean anything relevant. -/
def mdifferentiable_at (f : M → M') (x : M) :=
continuous_at f x ∧
differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f) (range I)
  ((ext_chart_at I x) x)

lemma mdifferentiable_at_iff_lift_prop_at (f : M → M') (x : M) :
  mdifferentiable_at I I' f x
  ↔ lift_prop_at (differentiable_within_at_prop I I') f x :=
begin
  congrm _ ∧ _,
  { rw continuous_within_at_univ },
  { simp [differentiable_within_at_prop, set.univ_inter] }
end

/-- `mdifferentiable_on I I' f s` indicates that the function `f` between manifolds
has a derivative within `s` at all points of `s`.
This is a generalization of `differentiable_on` to manifolds. -/
def mdifferentiable_on (f : M → M') (s : set M) :=
∀x ∈ s, mdifferentiable_within_at I I' f s x

/-- `mdifferentiable I I' f` indicates that the function `f` between manifolds
has a derivative everywhere.
This is a generalization of `differentiable` to manifolds. -/
def mdifferentiable (f : M → M') :=
∀x, mdifferentiable_at I I' f x

/-- Prop registering if a local homeomorphism is a local diffeomorphism on its source -/
def local_homeomorph.mdifferentiable (f : local_homeomorph M M') :=
(mdifferentiable_on I I' f f.source) ∧ (mdifferentiable_on I' I f.symm f.target)

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']

end derivatives_definitions

section derivatives_properties
/-! ### Unique differentiability sets in manifolds -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] --
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M']
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']
{f f₀ f₁ : M → M'}
{x : M}
{s t : set M}
{g : M' → M''}
{u : set M'}

lemma unique_mdiff_within_at_univ : unique_mdiff_within_at I univ x :=
begin
  unfold unique_mdiff_within_at,
  simp only [preimage_univ, univ_inter],
  exact I.unique_diff _ (mem_range_self _)
end
variable {I}

lemma unique_mdiff_within_at_iff {s : set M} {x : M} :
  unique_mdiff_within_at I s x ↔
  unique_diff_within_at 𝕜 ((ext_chart_at I x).symm ⁻¹' s ∩ (ext_chart_at I x).target)
  ((ext_chart_at I x) x) :=
begin
  apply unique_diff_within_at_congr,
  rw [nhds_within_inter, nhds_within_inter, nhds_within_ext_chart_at_target_eq]
end

lemma unique_mdiff_within_at.mono (h : unique_mdiff_within_at I s x) (st : s ⊆ t) :
  unique_mdiff_within_at I t x :=
unique_diff_within_at.mono h $ inter_subset_inter (preimage_mono st) (subset.refl _)

lemma unique_mdiff_within_at.inter' (hs : unique_mdiff_within_at I s x) (ht : t ∈ 𝓝[s] x) :
  unique_mdiff_within_at I (s ∩ t) x :=
begin
  rw [unique_mdiff_within_at, ext_chart_at_preimage_inter_eq],
  exact unique_diff_within_at.inter' hs (ext_chart_at_preimage_mem_nhds_within I x ht)
end

lemma unique_mdiff_within_at.inter (hs : unique_mdiff_within_at I s x) (ht : t ∈ 𝓝 x) :
  unique_mdiff_within_at I (s ∩ t) x :=
begin
  rw [unique_mdiff_within_at, ext_chart_at_preimage_inter_eq],
  exact unique_diff_within_at.inter hs (ext_chart_at_preimage_mem_nhds I x ht)
end

lemma is_open.unique_mdiff_within_at (xs : x ∈ s) (hs : is_open s) : unique_mdiff_within_at I s x :=
begin
  have := unique_mdiff_within_at.inter (unique_mdiff_within_at_univ I) (is_open.mem_nhds hs xs),
  rwa univ_inter at this
end

lemma unique_mdiff_on.inter (hs : unique_mdiff_on I s) (ht : is_open t) :
  unique_mdiff_on I (s ∩ t) :=
λx hx, unique_mdiff_within_at.inter (hs _ hx.1) (is_open.mem_nhds ht hx.2)

lemma is_open.unique_mdiff_on (hs : is_open s) : unique_mdiff_on I s :=
λx hx, is_open.unique_mdiff_within_at hx hs

lemma unique_mdiff_on_univ : unique_mdiff_on I (univ : set M) :=
is_open_univ.unique_mdiff_on

/- We name the typeclass variables related to `smooth_manifold_with_corners` structure as they are
necessary in lemmas mentioning the derivative, but not in lemmas about differentiability, so we
want to include them or omit them when necessary. -/
variables [Is : smooth_manifold_with_corners I M] [I's : smooth_manifold_with_corners I' M']
[I''s : smooth_manifold_with_corners I'' M'']

/-!
### General lemmas on derivatives of functions between manifolds

We mimick the API for functions between vector spaces
-/

lemma mdifferentiable_within_at_iff {f : M → M'} {s : set M} {x : M} :
  mdifferentiable_within_at I I' f s x ↔
  continuous_within_at f s x ∧
  differentiable_within_at 𝕜 (written_in_ext_chart_at I I' x f)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' s) ((ext_chart_at I x) x) :=
begin
  refine and_congr iff.rfl (exists_congr $ λ f', _),
  rw [inter_comm],
  simp only [has_fderiv_within_at, nhds_within_inter, nhds_within_ext_chart_at_target_eq]
end

include Is I's

/-- One can reformulate differentiability within a set at a point as continuity within this set at
this point, and differentiability in any chart containing that point. -/
lemma mdifferentiable_within_at_iff_of_mem_source
  {x' : M} {y : M'}
  (hx : x' ∈ (charted_space.chart_at H x).source)
  (hy : f x' ∈ (charted_space.chart_at H' y).source) :
  mdifferentiable_within_at I I' f s x'
  ↔ continuous_within_at f s x'
    ∧ differentiable_within_at 𝕜
        ((ext_chart_at I' y) ∘ f ∘ ((ext_chart_at I x).symm))
        (((ext_chart_at I x).symm) ⁻¹' s ∩ set.range I)
        ((ext_chart_at I x) x') :=
(differentiable_within_at_local_invariant_prop I I').lift_prop_within_at_indep_chart
  (structure_groupoid.chart_mem_maximal_atlas _ x) hx
  (structure_groupoid.chart_mem_maximal_atlas _ y) hy

omit Is I's

lemma mdifferentiable_within_at.mono (hst : s ⊆ t)
  (h : mdifferentiable_within_at I I' f t x) : mdifferentiable_within_at I I' f s x :=
⟨ continuous_within_at.mono h.1 hst,
  differentiable_within_at.mono h.2 (inter_subset_inter (preimage_mono hst) (subset.refl _)) ⟩

lemma mdifferentiable_within_at_univ :
  mdifferentiable_within_at I I' f univ x ↔ mdifferentiable_at I I' f x :=
by simp only [mdifferentiable_within_at, mdifferentiable_at, continuous_within_at_univ]
  with mfld_simps

lemma mdifferentiable_within_at_inter (ht : t ∈ 𝓝 x) :
  mdifferentiable_within_at I I' f (s ∩ t) x ↔ mdifferentiable_within_at I I' f s x :=
begin
  rw [mdifferentiable_within_at, mdifferentiable_within_at, ext_chart_at_preimage_inter_eq,
      differentiable_within_at_inter, continuous_within_at_inter ht],
  exact ext_chart_at_preimage_mem_nhds I x ht
end

lemma mdifferentiable_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  mdifferentiable_within_at I I' f (s ∩ t) x ↔ mdifferentiable_within_at I I' f s x :=
begin
  rw [mdifferentiable_within_at, mdifferentiable_within_at, ext_chart_at_preimage_inter_eq,
      differentiable_within_at_inter', continuous_within_at_inter' ht],
  exact ext_chart_at_preimage_mem_nhds_within I x ht
end

lemma mdifferentiable_at.mdifferentiable_within_at
  (h : mdifferentiable_at I I' f x) : mdifferentiable_within_at I I' f s x :=
mdifferentiable_within_at.mono (subset_univ _) (mdifferentiable_within_at_univ.2 h)

lemma mdifferentiable_within_at.mdifferentiable_at
  (h : mdifferentiable_within_at I I' f s x) (hs : s ∈ 𝓝 x) : mdifferentiable_at I I' f x :=
begin
  have : s = univ ∩ s, by rw univ_inter,
  rwa [this, mdifferentiable_within_at_inter hs, mdifferentiable_within_at_univ] at h,
end

lemma mdifferentiable_on.mono
  (h : mdifferentiable_on I I' f t) (st : s ⊆ t) : mdifferentiable_on I I' f s :=
λx hx, (h x (st hx)).mono st

lemma mdifferentiable_on_univ :
  mdifferentiable_on I I' f univ ↔ mdifferentiable I I' f :=
by { simp only [mdifferentiable_on, mdifferentiable_within_at_univ] with mfld_simps, refl }

lemma mdifferentiable.mdifferentiable_on
  (h : mdifferentiable I I' f) : mdifferentiable_on I I' f s :=
(mdifferentiable_on_univ.2 h).mono (subset_univ _)

lemma mdifferentiable_on_of_locally_mdifferentiable_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ mdifferentiable_on I I' f (s ∩ u)) :
  mdifferentiable_on I I' f s :=
begin
  assume x xs,
  rcases h x xs with ⟨t, t_open, xt, ht⟩,
  exact (mdifferentiable_within_at_inter (is_open.mem_nhds t_open xt)).1 (ht x ⟨xs, xt⟩)
end

include Is I's

lemma mdifferentiable_at_iff_of_mem_source {x' : M} {y : M'}
  (hx : x' ∈ (charted_space.chart_at H x).source)
  (hy : f x' ∈ (charted_space.chart_at H' y).source) :
  mdifferentiable_at I I' f x'
  ↔ continuous_at f x'
    ∧ differentiable_within_at 𝕜
        ((ext_chart_at I' y) ∘ f ∘ ((ext_chart_at I x).symm))
        (set.range I)
        ((ext_chart_at I x) x') :=
mdifferentiable_within_at_univ.symm.trans $
  (mdifferentiable_within_at_iff_of_mem_source hx hy).trans $
  by rw [continuous_within_at_univ, set.preimage_univ, set.univ_inter]

omit Is I's

/-! ### Deriving continuity from differentiability on manifolds -/

lemma mdifferentiable_within_at.continuous_within_at (h : mdifferentiable_within_at I I' f s x) :
  continuous_within_at f s x :=
h.1

lemma mdifferentiable_at.continuous_at (h : mdifferentiable_at I I' f x) : continuous_at f x :=
h.1

lemma mdifferentiable_on.continuous_on (h : mdifferentiable_on I I' f s) : continuous_on f s :=
λx hx, (h x hx).continuous_within_at

lemma mdifferentiable.continuous (h : mdifferentiable I I' f) : continuous f :=
continuous_iff_continuous_at.2 $ λx, (h x).continuous_at

/-! ### Composition lemmas -/

lemma written_in_ext_chart_comp (h : continuous_within_at f s x) :
  {y | written_in_ext_chart_at I I'' x (g ∘ f) y
       = ((written_in_ext_chart_at I' I'' (f x) g) ∘ (written_in_ext_chart_at I I' x f)) y}
  ∈ 𝓝[(ext_chart_at I x).symm ⁻¹' s ∩ range I] ((ext_chart_at I x) x)  :=
begin
  apply @filter.mem_of_superset _ _
    ((f ∘ (ext_chart_at I x).symm)⁻¹' (ext_chart_at I' (f x)).source) _
    (ext_chart_at_preimage_mem_nhds_within I x
      (h.preimage_mem_nhds_within (ext_chart_at_source_mem_nhds _ _))),
  mfld_set_tac,
end

end derivatives_properties

section mfderiv_fderiv

/-!
### Relations between vector space derivative and manifold derivative

Manifold differentiability `mdifferentiable`, when considered on the model vector space with its
trivial manifold structure, coincides with the usual Frechet differentiability `differentiable`. In
this section, we prove this and related statements.
-/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{f : E → E'} {s : set E} {x : E}

lemma unique_mdiff_within_at_iff_unique_diff_within_at :
  unique_mdiff_within_at (𝓘(𝕜, E)) s x ↔ unique_diff_within_at 𝕜 s x :=
by simp only [unique_mdiff_within_at] with mfld_simps

alias unique_mdiff_within_at_iff_unique_diff_within_at ↔
  unique_mdiff_within_at.unique_diff_within_at unique_diff_within_at.unique_mdiff_within_at

lemma unique_mdiff_on_iff_unique_diff_on :
  unique_mdiff_on (𝓘(𝕜, E)) s ↔ unique_diff_on 𝕜 s :=
by simp [unique_mdiff_on, unique_diff_on, unique_mdiff_within_at_iff_unique_diff_within_at]

alias unique_mdiff_on_iff_unique_diff_on ↔
  unique_mdiff_on.unique_diff_on unique_diff_on.unique_mdiff_on

@[simp, mfld_simps] lemma written_in_ext_chart_model_space :
  written_in_ext_chart_at (𝓘(𝕜, E)) (𝓘(𝕜, E')) x f = f :=
rfl

/-- For maps between vector spaces, `mdifferentiable_within_at` and `fdifferentiable_within_at`
coincide -/
theorem mdifferentiable_within_at_iff_differentiable_within_at :
  mdifferentiable_within_at (𝓘(𝕜, E)) (𝓘(𝕜, E')) f s x
  ↔ differentiable_within_at 𝕜 f s x :=
begin
  simp only [mdifferentiable_within_at] with mfld_simps,
  exact ⟨λH, H.2, λH, ⟨H.continuous_within_at, H⟩⟩
end

alias mdifferentiable_within_at_iff_differentiable_within_at ↔
  mdifferentiable_within_at.differentiable_within_at
  differentiable_within_at.mdifferentiable_within_at

/-- For maps between vector spaces, `mdifferentiable_at` and `differentiable_at` coincide -/
theorem mdifferentiable_at_iff_differentiable_at :
  mdifferentiable_at (𝓘(𝕜, E)) (𝓘(𝕜, E')) f x ↔ differentiable_at 𝕜 f x :=
begin
  simp only [mdifferentiable_at, differentiable_within_at_univ] with mfld_simps,
  exact ⟨λH, H.2, λH, ⟨H.continuous_at, H⟩⟩
end

alias mdifferentiable_at_iff_differentiable_at ↔
  mdifferentiable_at.differentiable_at differentiable_at.mdifferentiable_at

/-- For maps between vector spaces, `mdifferentiable_on` and `differentiable_on` coincide -/
theorem mdifferentiable_on_iff_differentiable_on :
  mdifferentiable_on (𝓘(𝕜, E)) (𝓘(𝕜, E')) f s ↔ differentiable_on 𝕜 f s :=
by simp only [mdifferentiable_on, differentiable_on,
              mdifferentiable_within_at_iff_differentiable_within_at]

alias mdifferentiable_on_iff_differentiable_on ↔
  mdifferentiable_on.differentiable_on differentiable_on.mdifferentiable_on

/-- For maps between vector spaces, `mdifferentiable` and `differentiable` coincide -/
theorem mdifferentiable_iff_differentiable :
  mdifferentiable (𝓘(𝕜, E)) (𝓘(𝕜, E')) f ↔ differentiable 𝕜 f :=
by simp only [mdifferentiable, differentiable, mdifferentiable_at_iff_differentiable_at]

alias mdifferentiable_iff_differentiable ↔
  mdifferentiable.differentiable differentiable.mdifferentiable

end mfderiv_fderiv

section specific_functions

/-! ### Differentiability of specific functions -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']

variables {s : set M} {x : M}

section charts

variable {e : local_homeomorph M H}

lemma mdifferentiable_at_atlas (h : e ∈ atlas H M) {x : M} (hx : x ∈ e.source) :
  mdifferentiable_at I I e x :=
begin
  refine ⟨(e.continuous_on x hx).continuous_at (is_open.mem_nhds e.open_source hx), _⟩,
  have mem : I ((chart_at H x : M → H) x) ∈
    I.symm ⁻¹' ((chart_at H x).symm ≫ₕ e).source ∩ range I,
    by simp only [hx] with mfld_simps,
  have : (chart_at H x).symm.trans e ∈ cont_diff_groupoid ∞ I :=
    has_groupoid.compatible _ (chart_mem_atlas H x) h,
  have A : cont_diff_on 𝕜 ∞
    (I ∘ ((chart_at H x).symm.trans e) ∘ I.symm)
    (I.symm ⁻¹' ((chart_at H x).symm.trans e).source ∩ range I) :=
    this.1,
  have B := A.differentiable_on le_top (I ((chart_at H x : M → H) x)) mem,
  simp only with mfld_simps at B,
  rw [inter_comm, differentiable_within_at_inter] at B,
  { simpa only with mfld_simps },
  { apply is_open.mem_nhds ((local_homeomorph.open_source _).preimage I.continuous_symm) mem.1 }
end

lemma mdifferentiable_on_atlas (h : e ∈ atlas H M) :
  mdifferentiable_on I I e e.source :=
λx hx, (mdifferentiable_at_atlas I h hx).mdifferentiable_within_at

lemma mdifferentiable_at_atlas_symm (h : e ∈ atlas H M) {x : H} (hx : x ∈ e.target) :
  mdifferentiable_at I I e.symm x :=
begin
  refine ⟨(e.continuous_on_symm x hx).continuous_at (is_open.mem_nhds e.open_target hx), _⟩,
  have mem : I x ∈ I.symm ⁻¹' (e.symm ≫ₕ chart_at H (e.symm x)).source ∩ range (I),
    by simp only [hx] with mfld_simps,
  have : e.symm.trans (chart_at H (e.symm x)) ∈ cont_diff_groupoid ∞ I :=
    has_groupoid.compatible _ h (chart_mem_atlas H _),
  have A : cont_diff_on 𝕜 ∞
    (I ∘ (e.symm.trans (chart_at H (e.symm x))) ∘ I.symm)
    (I.symm ⁻¹' (e.symm.trans (chart_at H (e.symm x))).source ∩ range I) :=
    this.1,
  have B := A.differentiable_on le_top (I x) mem,
  simp only with mfld_simps at B,
  rw [inter_comm, differentiable_within_at_inter] at B,
  { simpa only with mfld_simps },
  { apply (is_open.mem_nhds ((local_homeomorph.open_source _).preimage I.continuous_symm) mem.1) }
end

lemma mdifferentiable_on_atlas_symm (h : e ∈ atlas H M) :
  mdifferentiable_on I I e.symm e.target :=
λx hx, (mdifferentiable_at_atlas_symm I h hx).mdifferentiable_within_at

lemma mdifferentiable_of_mem_atlas (h : e ∈ atlas H M) : e.mdifferentiable I I :=
⟨mdifferentiable_on_atlas I h, mdifferentiable_on_atlas_symm I h⟩

lemma mdifferentiable_chart (x : M) : (chart_at H x).mdifferentiable I I :=
mdifferentiable_of_mem_atlas _ (chart_mem_atlas _ _)

end charts

end specific_functions

/-! ### Differentiable local homeomorphisms -/
namespace local_homeomorph.mdifferentiable

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M]
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M']
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']
{e : local_homeomorph M M'} (he : e.mdifferentiable I I')
{e' : local_homeomorph M' M''}
include he

lemma symm : e.symm.mdifferentiable I' I :=
⟨he.2, he.1⟩

protected lemma mdifferentiable_at {x : M} (hx : x ∈ e.source) :
  mdifferentiable_at I I' e x :=
(he.1 x hx).mdifferentiable_at (is_open.mem_nhds e.open_source hx)

lemma mdifferentiable_at_symm {x : M'} (hx : x ∈ e.target) :
  mdifferentiable_at I' I e.symm x :=
(he.2 x hx).mdifferentiable_at (is_open.mem_nhds e.open_target hx)

variables [smooth_manifold_with_corners I M] [smooth_manifold_with_corners I' M']
[smooth_manifold_with_corners I'' M'']

end local_homeomorph.mdifferentiable
