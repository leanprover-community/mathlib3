/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import geometry.manifold.smooth_manifold_with_corners
import geometry.manifold.local_invariant_properties

/-!
# Smooth functions between smooth manifolds

We define `Cⁿ` functions between smooth manifolds, as functions which are `Cⁿ` in charts, and prove
basic properties of these notions.

## Main definitions and statements

Let `M ` and `M'` be two smooth manifolds, with respect to model with corners `I` and `I'`. Let
`f : M → M'`.

* `cont_mdiff_within_at I I' n f s x` states that the function `f` is `Cⁿ` within the set `s`
  around the point `x`.
* `cont_mdiff_at I I' n f x` states that the function `f` is `Cⁿ` around `x`.
* `cont_mdiff_on I I' n f s` states that the function `f` is `Cⁿ` on the set `s`
* `cont_mdiff I I' n f` states that the function `f` is `Cⁿ`.
* `cont_mdiff_on.comp` gives the invariance of the `Cⁿ` property under composition
* `cont_mdiff_iff_cont_diff` states that, for functions between vector spaces,
  manifold-smoothness is equivalent to usual smoothness.

We also give many basic properties of smooth functions between manifolds, following the API of
smooth functions between vector spaces.

## Implementation details

Many properties follow for free from the corresponding properties of functions in vector spaces,
as being `Cⁿ` is a local property invariant under the smooth groupoid. We take advantage of the
general machinery developed in `local_invariant_properties.lean` to get these properties
automatically. For instance, the fact that being `Cⁿ` does not depend on the chart one considers
is given by `lift_prop_within_at_indep_chart`.

For this to work, the definition of `cont_mdiff_within_at` and friends has to
follow definitionally the setup of local invariant properties. Still, we recast the definition
in terms of extended charts in `cont_mdiff_on_iff` and `cont_mdiff_iff`.
-/

open set function filter charted_space smooth_manifold_with_corners
open_locale topology manifold

/-! ### Definition of smooth functions between manifolds -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] (I' : model_with_corners 𝕜 E' H')
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a manifold `M''` over the pair `(E'', H'')`.
{E'' : Type*} [normed_add_comm_group E''] [normed_space 𝕜 E'']
{H'' : Type*} [topological_space H''] {I'' : model_with_corners 𝕜 E'' H''}
{M'' : Type*} [topological_space M''] [charted_space H'' M'']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- F₁, F₂, F₃, F₄ are normed spaces
{F₁ : Type*} [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
{F₂ : Type*} [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
{F₃ : Type*} [normed_add_comm_group F₃] [normed_space 𝕜 F₃]
{F₄ : Type*} [normed_add_comm_group F₄] [normed_space 𝕜 F₄]
-- declare functions, sets, points and smoothness indices
{e : local_homeomorph M H} {e' : local_homeomorph M' H'}
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : ℕ∞}

/-- Property in the model space of a model with corners of being `C^n` within at set at a point,
when read in the model vector space. This property will be lifted to manifolds to define smooth
functions between manifolds. -/
def cont_diff_within_at_prop (n : ℕ∞) (f : H → H') (s : set H) (x : H) : Prop :=
cont_diff_within_at 𝕜 n (I' ∘ f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x)

lemma cont_diff_within_at_prop_self_source {f : E → H'} {s : set E} {x : E} :
  cont_diff_within_at_prop 𝓘(𝕜, E) I' n f s x ↔ cont_diff_within_at 𝕜 n (I' ∘ f) s x :=
begin
  simp_rw [cont_diff_within_at_prop, model_with_corners_self_coe, range_id, inter_univ],
  refl
end

lemma cont_diff_within_at_prop_self {f : E → E'} {s : set E} {x : E} :
  cont_diff_within_at_prop 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x ↔ cont_diff_within_at 𝕜 n f s x :=
cont_diff_within_at_prop_self_source 𝓘(𝕜, E')

lemma cont_diff_within_at_prop_self_target {f : H → E'} {s : set H} {x : H} :
  cont_diff_within_at_prop I 𝓘(𝕜, E') n f s x ↔
  cont_diff_within_at 𝕜 n (f ∘ I.symm) (I.symm ⁻¹' s ∩ range I) (I x) :=
iff.rfl

/-- Being `Cⁿ` in the model space is a local property, invariant under smooth maps. Therefore,
it will lift nicely to manifolds. -/
lemma cont_diff_within_at_local_invariant_prop (n : ℕ∞) :
  (cont_diff_groupoid ∞ I).local_invariant_prop (cont_diff_groupoid ∞ I')
  (cont_diff_within_at_prop I I' n) :=
{ is_local :=
  begin
    assume s x u f u_open xu,
    have : I.symm ⁻¹' (s ∩ u) ∩ range I = (I.symm ⁻¹' s ∩ range I) ∩ I.symm ⁻¹' u,
      by simp only [inter_right_comm, preimage_inter],
    rw [cont_diff_within_at_prop, cont_diff_within_at_prop, this],
    symmetry,
    apply cont_diff_within_at_inter,
    have : u ∈ 𝓝 (I.symm (I x)),
      by { rw [model_with_corners.left_inv], exact is_open.mem_nhds u_open xu },
    apply continuous_at.preimage_mem_nhds I.continuous_symm.continuous_at this,
  end,
  right_invariance' :=
  begin
    assume s x f e he hx h,
    rw cont_diff_within_at_prop at h ⊢,
    have : I x = (I ∘ e.symm ∘ I.symm) (I (e x)), by simp only [hx] with mfld_simps,
    rw this at h,
    have : I (e x) ∈ (I.symm) ⁻¹' e.target ∩ range I, by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he).2.cont_diff_within_at this).of_le le_top,
    convert (h.comp' _ this).mono_of_mem _ using 1,
    { ext y, simp only with mfld_simps },
    refine mem_nhds_within.mpr ⟨I.symm ⁻¹' e.target, e.open_target.preimage I.continuous_symm,
      by simp_rw [mem_preimage, I.left_inv, e.maps_to hx], _⟩,
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
    rw cont_diff_within_at_prop at h ⊢,
    have A : (I' ∘ f ∘ I.symm) (I x) ∈ (I'.symm ⁻¹' e'.source ∩ range I'),
      by simp only [hx] with mfld_simps,
    have := ((mem_groupoid_of_pregroupoid.2 he').1.cont_diff_within_at A).of_le le_top,
    convert this.comp _ h _,
    { ext y, simp only with mfld_simps },
    { assume y hy, simp only with mfld_simps at hy, simpa only [hy] with mfld_simps using hs hy.1 }
  end }

lemma cont_diff_within_at_prop_mono_of_mem (n : ℕ∞)
  ⦃s x t⦄ ⦃f : H → H'⦄ (hts : s ∈ 𝓝[t] x) (h : cont_diff_within_at_prop I I' n f s x) :
  cont_diff_within_at_prop I I' n f t x :=
begin
  refine h.mono_of_mem _,
  refine inter_mem _ (mem_of_superset self_mem_nhds_within $ inter_subset_right _ _),
  rwa [← filter.mem_map, ← I.image_eq, I.symm_map_nhds_within_image]
end

lemma cont_diff_within_at_prop_id (x : H) :
  cont_diff_within_at_prop I I n id univ x :=
begin
  simp [cont_diff_within_at_prop],
  have : cont_diff_within_at 𝕜 n id (range I) (I x) :=
    cont_diff_id.cont_diff_at.cont_diff_within_at,
  apply this.congr (λ y hy, _),
  { simp only with mfld_simps },
  { simp only [model_with_corners.right_inv I hy] with mfld_simps }
end

/-- A function is `n` times continuously differentiable within a set at a point in a manifold if
it is continuous and it is `n` times continuously differentiable in this set around this point, when
read in the preferred chart at this point. -/
def cont_mdiff_within_at (n : ℕ∞) (f : M → M') (s : set M) (x : M) :=
lift_prop_within_at (cont_diff_within_at_prop I I' n) f s x

/-- Abbreviation for `cont_mdiff_within_at I I' ⊤ f s x`. See also documentation for `smooth`.
-/
@[reducible] def smooth_within_at (f : M → M') (s : set M) (x : M) :=
cont_mdiff_within_at I I' ⊤ f s x

/-- A function is `n` times continuously differentiable at a point in a manifold if
it is continuous and it is `n` times continuously differentiable around this point, when
read in the preferred chart at this point. -/
def cont_mdiff_at (n : ℕ∞) (f : M → M') (x : M) :=
cont_mdiff_within_at I I' n f univ x

lemma cont_mdiff_at_iff {n : ℕ∞} {f : M → M'} {x : M} :
  cont_mdiff_at I I' n f x ↔ continuous_at f x ∧ cont_diff_within_at 𝕜 n
    (ext_chart_at I' (f x) ∘ f ∘ (ext_chart_at I x).symm) (range I) (ext_chart_at I x x) :=
lift_prop_at_iff.trans $ by { rw [cont_diff_within_at_prop, preimage_univ, univ_inter], refl }

/-- Abbreviation for `cont_mdiff_at I I' ⊤ f x`. See also documentation for `smooth`. -/
@[reducible] def smooth_at (f : M → M') (x : M) := cont_mdiff_at I I' ⊤ f x

/-- A function is `n` times continuously differentiable in a set of a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable on this set in the charts
around these points. -/
def cont_mdiff_on (n : ℕ∞) (f : M → M') (s : set M) :=
∀ x ∈ s, cont_mdiff_within_at I I' n f s x

/-- Abbreviation for `cont_mdiff_on I I' ⊤ f s`. See also documentation for `smooth`. -/
@[reducible] def smooth_on (f : M → M') (s : set M) := cont_mdiff_on I I' ⊤ f s

/-- A function is `n` times continuously differentiable in a manifold if it is continuous
and, for any pair of points, it is `n` times continuously differentiable in the charts
around these points. -/
def cont_mdiff (n : ℕ∞) (f : M → M') :=
∀ x, cont_mdiff_at I I' n f x

/-- Abbreviation for `cont_mdiff I I' ⊤ f`.
Short note to work with these abbreviations: a lemma of the form `cont_mdiff_foo.bar` will
apply fine to an assumption `smooth_foo` using dot notation or normal notation.
If the consequence `bar` of the lemma involves `cont_diff`, it is still better to restate
the lemma replacing `cont_diff` with `smooth` both in the assumption and in the conclusion,
to make it possible to use `smooth` consistently.
This also applies to `smooth_at`, `smooth_on` and `smooth_within_at`.-/
@[reducible] def smooth (f : M → M') := cont_mdiff I I' ⊤ f

/-! ### Basic properties of smooth functions between manifolds -/

variables {I I'}

lemma cont_mdiff.smooth (h : cont_mdiff I I' ⊤ f) : smooth I I' f := h

lemma smooth.cont_mdiff (h : smooth I I' f) : cont_mdiff I I' ⊤ f := h

lemma cont_mdiff_on.smooth_on (h : cont_mdiff_on I I' ⊤ f s) : smooth_on I I' f s := h

lemma smooth_on.cont_mdiff_on (h : smooth_on I I' f s) : cont_mdiff_on I I' ⊤ f s := h

lemma cont_mdiff_at.smooth_at (h : cont_mdiff_at I I' ⊤ f x) : smooth_at I I' f x := h

lemma smooth_at.cont_mdiff_at (h : smooth_at I I' f x) : cont_mdiff_at I I' ⊤ f x := h

lemma cont_mdiff_within_at.smooth_within_at (h : cont_mdiff_within_at I I' ⊤ f s x) :
  smooth_within_at I I' f s x := h

lemma smooth_within_at.cont_mdiff_within_at (h : smooth_within_at I I' f s x) :
cont_mdiff_within_at I I' ⊤ f s x := h

lemma cont_mdiff.cont_mdiff_at (h : cont_mdiff I I' n f) :
  cont_mdiff_at I I' n f x :=
h x

lemma smooth.smooth_at (h : smooth I I' f) :
  smooth_at I I' f x := cont_mdiff.cont_mdiff_at h

lemma cont_mdiff_within_at_univ :
  cont_mdiff_within_at I I' n f univ x ↔ cont_mdiff_at I I' n f x :=
iff.rfl

lemma smooth_within_at_univ :
 smooth_within_at I I' f univ x ↔ smooth_at I I' f x := cont_mdiff_within_at_univ

lemma cont_mdiff_on_univ :
  cont_mdiff_on I I' n f univ ↔ cont_mdiff I I' n f :=
by simp only [cont_mdiff_on, cont_mdiff, cont_mdiff_within_at_univ,
  forall_prop_of_true, mem_univ]

lemma smooth_on_univ : smooth_on I I' f univ ↔ smooth I I' f := cont_mdiff_on_univ

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. -/
lemma cont_mdiff_within_at_iff :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_diff_within_at 𝕜 n ((ext_chart_at I' (f x)) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).symm ⁻¹' s ∩ range I)
    (ext_chart_at I x x) :=
iff.rfl

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart. This form states smoothness of `f`
written in such a way that the set is restricted to lie within the domain/codomain of the
corresponding charts.
Even though this expression is more complicated than the one in `cont_mdiff_within_at_iff`, it is
a smaller set, but their germs at `ext_chart_at I x x` are equal. It is sometimes useful to rewrite
using this in the goal.
-/
lemma cont_mdiff_within_at_iff' :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_diff_within_at 𝕜 n ((ext_chart_at I' (f x)) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩
      (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' (f x)).source))
    (ext_chart_at I x x) :=
begin
  rw [cont_mdiff_within_at_iff, and.congr_right_iff],
  set e := ext_chart_at I x, set e' := ext_chart_at I' (f x),
  refine λ hc, cont_diff_within_at_congr_nhds _,
  rw [← e.image_source_inter_eq', ← map_ext_chart_at_nhds_within_eq_image,
      ← map_ext_chart_at_nhds_within, inter_comm, nhds_within_inter_of_mem],
  exact hc (ext_chart_at_source_mem_nhds _ _)
end

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in the corresponding extended chart in the target. -/
lemma cont_mdiff_within_at_iff_target :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_mdiff_within_at I 𝓘(𝕜, E') n (ext_chart_at I' (f x) ∘ f) s x :=
begin
  simp_rw [cont_mdiff_within_at, lift_prop_within_at, ← and_assoc],
  have cont : (continuous_within_at f s x ∧
      continuous_within_at (ext_chart_at I' (f x) ∘ f) s x) ↔
      continuous_within_at f s x,
  { refine ⟨λ h, h.1, λ h, ⟨h, _⟩⟩,
    have h₂ := (chart_at H' (f x)).continuous_to_fun.continuous_within_at (mem_chart_source _ _),
    refine ((I'.continuous_at.comp_continuous_within_at h₂).comp' h).mono_of_mem _,
    exact inter_mem self_mem_nhds_within (h.preimage_mem_nhds_within $
      (chart_at _ _).open_source.mem_nhds $ mem_chart_source _ _) },
  simp_rw [cont, cont_diff_within_at_prop, ext_chart_at, local_homeomorph.extend,
    local_equiv.coe_trans, model_with_corners.to_local_equiv_coe, local_homeomorph.coe_coe,
    model_with_corners_self_coe, chart_at_self_eq, local_homeomorph.refl_apply, comp.left_id]
end

lemma smooth_within_at_iff :
  smooth_within_at I I' f s x ↔ continuous_within_at f s x ∧
    cont_diff_within_at 𝕜 ∞ (ext_chart_at I' (f x) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).symm ⁻¹' s ∩ range I)
    (ext_chart_at I x x) :=
cont_mdiff_within_at_iff

lemma smooth_within_at_iff_target :
  smooth_within_at I I' f s x ↔ continuous_within_at f s x ∧
    smooth_within_at I 𝓘(𝕜, E') (ext_chart_at I' (f x) ∘ f) s x :=
cont_mdiff_within_at_iff_target

lemma cont_mdiff_at_iff_target {x : M} :
  cont_mdiff_at I I' n f x ↔
    continuous_at f x ∧ cont_mdiff_at I 𝓘(𝕜, E') n (ext_chart_at I' (f x) ∘ f) x :=
by rw [cont_mdiff_at, cont_mdiff_at, cont_mdiff_within_at_iff_target, continuous_within_at_univ]

lemma smooth_at_iff_target {x : M} :
  smooth_at I I' f x ↔ continuous_at f x ∧ smooth_at I 𝓘(𝕜, E') (ext_chart_at I' (f x) ∘ f) x :=
cont_mdiff_at_iff_target

include Is I's

lemma cont_mdiff_within_at_iff_of_mem_maximal_atlas
  {x : M} (he : e ∈ maximal_atlas I M) (he' : e' ∈ maximal_atlas I' M')
  (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_diff_within_at 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm)
    ((e.extend I).symm ⁻¹' s ∩ range I)
    (e.extend I x) :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart he hx he' hy

/-- An alternative formulation of `cont_mdiff_within_at_iff_of_mem_maximal_atlas`
  if the set if `s` lies in `e.source`. -/
lemma cont_mdiff_within_at_iff_image {x : M} (he : e ∈ maximal_atlas I M)
  (he' : e' ∈ maximal_atlas I' M') (hs : s ⊆ e.source) (hx : x ∈ e.source) (hy : f x ∈ e'.source) :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
  cont_diff_within_at 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm) (e.extend I '' s) (e.extend I x) :=
begin
  rw [cont_mdiff_within_at_iff_of_mem_maximal_atlas he he' hx hy, and.congr_right_iff],
  refine λ hf, cont_diff_within_at_congr_nhds _,
  simp_rw [nhds_within_eq_iff_eventually_eq,
    e.extend_symm_preimage_inter_range_eventually_eq I hs hx]
end

/-- One can reformulate smoothness within a set at a point as continuity within this set at this
point, and smoothness in any chart containing that point. -/
lemma cont_mdiff_within_at_iff_of_mem_source
  {x' : M} {y : M'} (hx : x' ∈ (chart_at H x).source)
  (hy : f x' ∈ (chart_at H' y).source) :
  cont_mdiff_within_at I I' n f s x' ↔ continuous_within_at f s x' ∧
    cont_diff_within_at 𝕜 n (ext_chart_at I' y ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).symm ⁻¹' s ∩ range I)
    (ext_chart_at I x x') :=
cont_mdiff_within_at_iff_of_mem_maximal_atlas
  (chart_mem_maximal_atlas _ x) (chart_mem_maximal_atlas _ y) hx hy

lemma cont_mdiff_within_at_iff_of_mem_source' {x' : M} {y : M'} (hx : x' ∈ (chart_at H x).source)
  (hy : f x' ∈ (chart_at H' y).source) :
  cont_mdiff_within_at I I' n f s x' ↔ continuous_within_at f s x' ∧
    cont_diff_within_at 𝕜 n ((ext_chart_at I' y) ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source))
    (ext_chart_at I x x') :=
begin
  refine (cont_mdiff_within_at_iff_of_mem_source hx hy).trans _,
  rw [← ext_chart_at_source I] at hx,
  rw [← ext_chart_at_source I'] at hy,
  rw [and.congr_right_iff],
  set e := ext_chart_at I x, set e' := ext_chart_at I' (f x),
  refine λ hc, cont_diff_within_at_congr_nhds _,
  rw [← e.image_source_inter_eq', ← map_ext_chart_at_nhds_within_eq_image' I x hx,
      ← map_ext_chart_at_nhds_within' I x hx, inter_comm, nhds_within_inter_of_mem],
  exact hc (ext_chart_at_source_mem_nhds' _ _ hy)
end

lemma cont_mdiff_at_iff_of_mem_source {x' : M} {y : M'} (hx : x' ∈ (chart_at H x).source)
  (hy : f x' ∈ (chart_at H' y).source) :
  cont_mdiff_at I I' n f x' ↔ continuous_at f x' ∧
    cont_diff_within_at 𝕜 n (ext_chart_at I' y ∘ f ∘ (ext_chart_at I x).symm)
    (range I)
    (ext_chart_at I x x') :=
(cont_mdiff_within_at_iff_of_mem_source hx hy).trans $
  by rw [continuous_within_at_univ, preimage_univ, univ_inter]

omit Is

lemma cont_mdiff_within_at_iff_target_of_mem_source
  {x : M} {y : M'} (hy : f x ∈ (chart_at H' y).source) :
  cont_mdiff_within_at I I' n f s x ↔ continuous_within_at f s x ∧
    cont_mdiff_within_at I 𝓘(𝕜, E') n (ext_chart_at I' y ∘ f) s x :=
begin
  simp_rw [cont_mdiff_within_at],
  rw [(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart_target
    (chart_mem_maximal_atlas I' y) hy, and_congr_right],
  intro hf,
  simp_rw [structure_groupoid.lift_prop_within_at_self_target],
  simp_rw [((chart_at H' y).continuous_at hy).comp_continuous_within_at hf],
  rw [← ext_chart_at_source I'] at hy,
  simp_rw [(continuous_at_ext_chart_at' I' _ hy).comp_continuous_within_at hf],
  refl,
end

lemma cont_mdiff_at_iff_target_of_mem_source
  {x : M} {y : M'} (hy : f x ∈ (chart_at H' y).source) :
  cont_mdiff_at I I' n f x ↔ continuous_at f x ∧
    cont_mdiff_at I 𝓘(𝕜, E') n (ext_chart_at I' y ∘ f) x :=
begin
  rw [cont_mdiff_at, cont_mdiff_within_at_iff_target_of_mem_source hy,
    continuous_within_at_univ, cont_mdiff_at],
  apply_instance
end

omit I's
include Is

lemma cont_mdiff_within_at_iff_source_of_mem_maximal_atlas
  (he : e ∈ maximal_atlas I M) (hx : x ∈ e.source) :
  cont_mdiff_within_at I I' n f s x ↔
    cont_mdiff_within_at 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm)
      ((e.extend I).symm ⁻¹' s ∩ range I) (e.extend I x) :=
begin
  have h2x := hx, rw [← e.extend_source I] at h2x,
  simp_rw [cont_mdiff_within_at,
    (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_indep_chart_source
    he hx, structure_groupoid.lift_prop_within_at_self_source,
    e.extend_symm_continuous_within_at_comp_right_iff, cont_diff_within_at_prop_self_source,
    cont_diff_within_at_prop, function.comp, e.left_inv hx, (e.extend I).left_inv h2x],
  refl,
end

lemma cont_mdiff_within_at_iff_source_of_mem_source
  {x' : M} (hx' : x' ∈ (chart_at H x).source) :
  cont_mdiff_within_at I I' n f s x' ↔
    cont_mdiff_within_at 𝓘(𝕜, E) I' n (f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).symm ⁻¹' s ∩ range I) (ext_chart_at I x x') :=
cont_mdiff_within_at_iff_source_of_mem_maximal_atlas (chart_mem_maximal_atlas I x) hx'

lemma cont_mdiff_at_iff_source_of_mem_source
  {x' : M} (hx' : x' ∈ (chart_at H x).source) :
  cont_mdiff_at I I' n f x' ↔ cont_mdiff_within_at 𝓘(𝕜, E) I' n (f ∘ (ext_chart_at I x).symm)
    (range I) (ext_chart_at I x x') :=
by simp_rw [cont_mdiff_at, cont_mdiff_within_at_iff_source_of_mem_source hx', preimage_univ,
  univ_inter]

include I's

lemma cont_mdiff_on_iff_of_mem_maximal_atlas
  (he : e ∈ maximal_atlas I M) (he' : e' ∈ maximal_atlas I' M')
  (hs : s ⊆ e.source)
  (h2s : maps_to f s e'.source) :
  cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    cont_diff_on 𝕜 n (e'.extend I' ∘ f ∘ (e.extend I).symm)
    (e.extend I '' s) :=
begin
  simp_rw [continuous_on, cont_diff_on, set.ball_image_iff, ← forall_and_distrib, cont_mdiff_on],
  exact forall₂_congr (λ x hx, cont_mdiff_within_at_iff_image he he' hs (hs hx) (h2s hx))
end

/-- If the set where you want `f` to be smooth lies entirely in a single chart, and `f` maps it
  into a single chart, the smoothness of `f` on that set can be expressed by purely looking in
  these charts.
  Note: this lemma uses `ext_chart_at I x '' s` instead of `(ext_chart_at I x).symm ⁻¹' s` to ensure
  that this set lies in `(ext_chart_at I x).target`. -/
lemma cont_mdiff_on_iff_of_subset_source {x : M} {y : M'}
  (hs : s ⊆ (chart_at H x).source)
  (h2s : maps_to f s (chart_at H' y).source) :
  cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    cont_diff_on 𝕜 n (ext_chart_at I' y ∘ f ∘ (ext_chart_at I x).symm)
    (ext_chart_at I x '' s) :=
cont_mdiff_on_iff_of_mem_maximal_atlas
  (chart_mem_maximal_atlas I x) (chart_mem_maximal_atlas I' y) hs h2s

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart. -/
lemma cont_mdiff_on_iff :
  cont_mdiff_on I I' n f s ↔ continuous_on f s ∧
    ∀ (x : M) (y : M'), cont_diff_on 𝕜 n (ext_chart_at I' y ∘ f ∘ (ext_chart_at I x).symm)
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
    convert ((cont_mdiff_within_at_iff_of_mem_source w1 w2).mp h).2.mono _,
    { simp only [w, hz] with mfld_simps },
    { mfld_set_tac } },
  { rintros ⟨hcont, hdiff⟩ x hx,
    refine (cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_iff.mpr _,
    refine ⟨hcont x hx, _⟩,
    dsimp [cont_diff_within_at_prop],
    convert hdiff x (f x) (ext_chart_at I x x) (by simp only [hx] with mfld_simps) using 1,
    mfld_set_tac }
end

/-- One can reformulate smoothness on a set as continuity on this set, and smoothness in any
extended chart in the target. -/
lemma cont_mdiff_on_iff_target :
  cont_mdiff_on I I' n f s ↔ continuous_on f s ∧ ∀ (y : M'),
    cont_mdiff_on I 𝓘(𝕜, E') n (ext_chart_at I' y ∘ f)
    (s ∩ f ⁻¹' (ext_chart_at I' y).source) :=
begin
  inhabit E',
  simp only [cont_mdiff_on_iff, model_with_corners.source_eq, chart_at_self_eq,
    local_homeomorph.refl_local_equiv, local_equiv.refl_trans, ext_chart_at,
    local_homeomorph.extend, set.preimage_univ, set.inter_univ, and.congr_right_iff],
  intros h,
  split,
  { refine λ h' y, ⟨_, λ x _, h' x y⟩,
    have h'' : continuous_on _ univ := (model_with_corners.continuous I').continuous_on,
    convert (h''.comp' (chart_at H' y).continuous_to_fun).comp' h,
    simp },
  { exact λ h' x y, (h' y).2 x default }
end

lemma smooth_on_iff :
  smooth_on I I' f s ↔ continuous_on f s ∧
    ∀ (x : M) (y : M'), cont_diff_on 𝕜 ⊤ (ext_chart_at I' y ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩
      (ext_chart_at I x).symm ⁻¹' (s ∩ f ⁻¹' (ext_chart_at I' y).source)) :=
cont_mdiff_on_iff

lemma smooth_on_iff_target :
  smooth_on I I' f s ↔ continuous_on f s ∧ ∀ (y : M'),
    smooth_on I 𝓘(𝕜, E') (ext_chart_at I' y ∘ f)
    (s ∩ f ⁻¹' (ext_chart_at I' y).source) :=
cont_mdiff_on_iff_target

/-- One can reformulate smoothness as continuity and smoothness in any extended chart. -/
lemma cont_mdiff_iff :
  cont_mdiff I I' n f ↔ continuous f ∧
    ∀ (x : M) (y : M'), cont_diff_on 𝕜 n (ext_chart_at I' y ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' y).source)) :=
by simp [← cont_mdiff_on_univ, cont_mdiff_on_iff, continuous_iff_continuous_on_univ]

/-- One can reformulate smoothness as continuity and smoothness in any extended chart in the
target. -/
lemma cont_mdiff_iff_target :
  cont_mdiff I I' n f ↔ continuous f ∧
    ∀ (y : M'), cont_mdiff_on I 𝓘(𝕜, E') n (ext_chart_at I' y ∘ f)
    (f ⁻¹' (ext_chart_at I' y).source) :=
begin
  rw [← cont_mdiff_on_univ, cont_mdiff_on_iff_target],
  simp [continuous_iff_continuous_on_univ]
end

lemma smooth_iff :
  smooth I I' f ↔ continuous f ∧
    ∀ (x : M) (y : M'), cont_diff_on 𝕜 ⊤ (ext_chart_at I' y ∘ f ∘ (ext_chart_at I x).symm)
    ((ext_chart_at I x).target ∩ (ext_chart_at I x).symm ⁻¹' (f ⁻¹' (ext_chart_at I' y).source)) :=
cont_mdiff_iff

lemma smooth_iff_target :
  smooth I I' f ↔ continuous f ∧ ∀ (y : M'), smooth_on I 𝓘(𝕜, E') (ext_chart_at I' y ∘ f)
    (f ⁻¹' (ext_chart_at I' y).source) :=
cont_mdiff_iff_target

omit Is I's

/-! ### Deducing smoothness from higher smoothness -/

lemma cont_mdiff_within_at.of_le (hf : cont_mdiff_within_at I I' n f s x) (le : m ≤ n) :
  cont_mdiff_within_at I I' m f s x :=
⟨hf.1, hf.2.of_le le⟩

lemma cont_mdiff_at.of_le (hf : cont_mdiff_at I I' n f x) (le : m ≤ n) :
  cont_mdiff_at I I' m f x :=
cont_mdiff_within_at.of_le hf le

lemma cont_mdiff_on.of_le (hf : cont_mdiff_on I I' n f s) (le : m ≤ n) :
  cont_mdiff_on I I' m f s :=
λ x hx, (hf x hx).of_le le

lemma cont_mdiff.of_le (hf : cont_mdiff I I' n f) (le : m ≤ n) :
  cont_mdiff I I' m f :=
λ x, (hf x).of_le le

/-! ### Deducing smoothness from smoothness one step beyond -/

lemma cont_mdiff_within_at.of_succ {n : ℕ}
  (h : cont_mdiff_within_at I I' n.succ f s x) :
  cont_mdiff_within_at I I' n f s x :=
h.of_le (with_top.coe_le_coe.2 (nat.le_succ n))

lemma cont_mdiff_at.of_succ {n : ℕ} (h : cont_mdiff_at I I' n.succ f x) :
  cont_mdiff_at I I' n f x :=
cont_mdiff_within_at.of_succ h

lemma cont_mdiff_on.of_succ {n : ℕ} (h : cont_mdiff_on I I' n.succ f s) :
  cont_mdiff_on I I' n f s :=
λ x hx, (h x hx).of_succ

lemma cont_mdiff.of_succ {n : ℕ} (h : cont_mdiff I I' n.succ f) :
  cont_mdiff I I' n f :=
λ x, (h x).of_succ

/-! ### Deducing continuity from smoothness -/

lemma cont_mdiff_within_at.continuous_within_at
  (hf : cont_mdiff_within_at I I' n f s x) : continuous_within_at f s x :=
hf.1

lemma cont_mdiff_at.continuous_at
  (hf : cont_mdiff_at I I' n f x) : continuous_at f x :=
(continuous_within_at_univ _ _ ).1 $ cont_mdiff_within_at.continuous_within_at hf

lemma cont_mdiff_on.continuous_on
  (hf : cont_mdiff_on I I' n f s) : continuous_on f s :=
λ x hx, (hf x hx).continuous_within_at

lemma cont_mdiff.continuous (hf : cont_mdiff I I' n f) :
  continuous f :=
continuous_iff_continuous_at.2 $ λ x, (hf x).continuous_at

/-! ### `C^∞` smoothness -/

lemma cont_mdiff_within_at_top :
  smooth_within_at I I' f s x ↔ (∀n:ℕ, cont_mdiff_within_at I I' n f s x) :=
⟨λ h n, ⟨h.1, cont_diff_within_at_top.1 h.2 n⟩,
 λ H, ⟨(H 0).1, cont_diff_within_at_top.2 (λ n, (H n).2)⟩⟩

lemma cont_mdiff_at_top :
  smooth_at I I' f x ↔ (∀n:ℕ, cont_mdiff_at I I' n f x) :=
cont_mdiff_within_at_top

lemma cont_mdiff_on_top :
  smooth_on I I' f s ↔ (∀n:ℕ, cont_mdiff_on I I' n f s) :=
⟨λ h n, h.of_le le_top, λ h x hx, cont_mdiff_within_at_top.2 (λ n, h n x hx)⟩

lemma cont_mdiff_top :
  smooth I I' f ↔ (∀n:ℕ, cont_mdiff I I' n f) :=
⟨λ h n, h.of_le le_top, λ h x, cont_mdiff_within_at_top.2 (λ n, h n x)⟩

lemma cont_mdiff_within_at_iff_nat :
  cont_mdiff_within_at I I' n f s x ↔
  (∀m:ℕ, (m : ℕ∞) ≤ n → cont_mdiff_within_at I I' m f s x) :=
begin
  refine ⟨λ h m hm, h.of_le hm, λ h, _⟩,
  cases n,
  { exact cont_mdiff_within_at_top.2 (λ n, h n le_top) },
  { exact h n le_rfl }
end

/-! ### Restriction to a smaller set -/

lemma cont_mdiff_within_at.mono_of_mem (hf : cont_mdiff_within_at I I' n f s x)
  (hts : s ∈ 𝓝[t] x) : cont_mdiff_within_at I I' n f t x :=
structure_groupoid.local_invariant_prop.lift_prop_within_at_mono_of_mem
  (cont_diff_within_at_prop_mono_of_mem I I' n) hf hts

lemma cont_mdiff_within_at.mono (hf : cont_mdiff_within_at I I' n f s x) (hts : t ⊆ s) :
  cont_mdiff_within_at I I' n f t x :=
hf.mono_of_mem $ mem_of_superset self_mem_nhds_within hts

lemma cont_mdiff_within_at_congr_nhds (hst : 𝓝[s] x = 𝓝[t] x) :
  cont_mdiff_within_at I I' n f s x ↔ cont_mdiff_within_at I I' n f t x :=
⟨λ h, h.mono_of_mem $ hst ▸ self_mem_nhds_within,
  λ h, h.mono_of_mem $ hst.symm ▸ self_mem_nhds_within⟩

lemma cont_mdiff_at.cont_mdiff_within_at (hf : cont_mdiff_at I I' n f x) :
  cont_mdiff_within_at I I' n f s x :=
cont_mdiff_within_at.mono hf (subset_univ _)

lemma smooth_at.smooth_within_at (hf : smooth_at I I' f x) :
  smooth_within_at I I' f s x :=
cont_mdiff_at.cont_mdiff_within_at hf

lemma cont_mdiff_on.mono (hf : cont_mdiff_on I I' n f s) (hts : t ⊆ s) :
  cont_mdiff_on I I' n f t :=
λ x hx, (hf x (hts hx)).mono hts

lemma cont_mdiff.cont_mdiff_on (hf : cont_mdiff I I' n f) :
  cont_mdiff_on I I' n f s :=
λ x hx, (hf x).cont_mdiff_within_at

lemma smooth.smooth_on (hf : smooth I I' f) :
  smooth_on I I' f s :=
cont_mdiff.cont_mdiff_on hf

lemma cont_mdiff_within_at_inter' (ht : t ∈ 𝓝[s] x) :
  cont_mdiff_within_at I I' n f (s ∩ t) x ↔ cont_mdiff_within_at I I' n f s x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_inter' ht

lemma cont_mdiff_within_at_inter (ht : t ∈ 𝓝 x) :
  cont_mdiff_within_at I I' n f (s ∩ t) x ↔ cont_mdiff_within_at I I' n f s x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_inter ht

lemma cont_mdiff_within_at.cont_mdiff_at
  (h : cont_mdiff_within_at I I' n f s x) (ht : s ∈ 𝓝 x) :
  cont_mdiff_at I I' n f x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_of_lift_prop_within_at h ht

lemma smooth_within_at.smooth_at
  (h : smooth_within_at I I' f s x) (ht : s ∈ 𝓝 x) :
  smooth_at I I' f x :=
cont_mdiff_within_at.cont_mdiff_at h ht

lemma cont_mdiff_on.cont_mdiff_at (h : cont_mdiff_on I I' n f s) (hx : s ∈ 𝓝 x) :
  cont_mdiff_at I I' n f x :=
(h x (mem_of_mem_nhds hx)).cont_mdiff_at hx

lemma smooth_on.smooth_at (h : smooth_on I I' f s) (hx : s ∈ 𝓝 x) : smooth_at I I' f x :=
h.cont_mdiff_at hx

include Is

lemma cont_mdiff_on_iff_source_of_mem_maximal_atlas
  (he : e ∈ maximal_atlas I M) (hs : s ⊆ e.source) :
  cont_mdiff_on I I' n f s ↔ cont_mdiff_on 𝓘(𝕜, E) I' n (f ∘ (e.extend I).symm) (e.extend I '' s) :=
begin
  simp_rw [cont_mdiff_on, set.ball_image_iff],
  refine forall₂_congr (λ x hx, _),
  rw [cont_mdiff_within_at_iff_source_of_mem_maximal_atlas he (hs hx)],
  apply cont_mdiff_within_at_congr_nhds,
  simp_rw [nhds_within_eq_iff_eventually_eq,
    e.extend_symm_preimage_inter_range_eventually_eq I hs (hs hx)]
end

include I's

/-- A function is `C^n` within a set at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
lemma cont_mdiff_within_at_iff_cont_mdiff_on_nhds {n : ℕ} :
  cont_mdiff_within_at I I' n f s x ↔
  ∃ u ∈ 𝓝[insert x s] x, cont_mdiff_on I I' n f u :=
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
    have h' : cont_mdiff_within_at I I' n f (s ∩ o) x := h.mono (inter_subset_left _ _),
    simp only [cont_mdiff_within_at, lift_prop_within_at, cont_diff_within_at_prop] at h',
    -- let `u` be a good neighborhood in the chart where the function is smooth
    rcases h.2.cont_diff_on le_rfl with ⟨u, u_nhds, u_subset, hu⟩,
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
        from (continuous_at_ext_chart_at I x).continuous_within_at.preimage_mem_nhds_within' this,
      apply nhds_within_mono _ _ u_nhds,
      rw image_subset_iff,
      assume y hy,
      rcases hy.1 with rfl|h',
      { simp only [mem_insert_iff] with mfld_simps },
      { simp only [mem_insert_iff, ho hy.2, h', h'o ⟨hy.2, h'⟩] with mfld_simps } },
    show cont_mdiff_on I I' n f v,
    { assume y hy,
      have : continuous_within_at f v y,
      { apply (((continuous_on_ext_chart_at_symm I' (f x) _ _).comp'
          (hu _ hy.2).continuous_within_at).comp' (continuous_on_ext_chart_at I x _ _)).congr_mono,
        { assume z hz,
          simp only [v_incl hz, v_incl' z hz] with mfld_simps },
        { assume z hz,
          simp only [v_incl hz, v_incl' z hz] with mfld_simps,
          exact hz.2 },
        { simp only [v_incl hy, v_incl' y hy] with mfld_simps },
        { simp only [v_incl hy, v_incl' y hy] with mfld_simps },
        { simp only [v_incl hy] with mfld_simps } },
      refine (cont_mdiff_within_at_iff_of_mem_source' (v_incl hy) (v_incl' y hy)).mpr ⟨this, _⟩,
      { apply hu.mono,
        { assume z hz,
          simp only [v] with mfld_simps at hz,
          have : I ((chart_at H x) (((chart_at H x).symm) (I.symm z))) ∈ u, by simp only [hz],
          simpa only [hz] with mfld_simps using this },
        { have exty : I (chart_at H x y) ∈ u := hy.2,
          simp only [v_incl hy, v_incl' y hy, exty, hy.1.1, hy.1.2] with mfld_simps } } } },
  { rintros ⟨u, u_nhds, hu⟩,
    have : cont_mdiff_within_at I I' ↑n f (insert x s ∩ u) x,
    { have : x ∈ insert x s := mem_insert x s,
      exact hu.mono (inter_subset_right _ _) _ ⟨this, mem_of_mem_nhds_within this u_nhds⟩ },
    rw cont_mdiff_within_at_inter' u_nhds at this,
    exact this.mono (subset_insert x s) }
end

/-- A function is `C^n` at a point, for `n : ℕ`, if and only if it is `C^n` on
a neighborhood of this point. -/
lemma cont_mdiff_at_iff_cont_mdiff_on_nhds {n : ℕ} :
  cont_mdiff_at I I' n f x ↔ ∃ u ∈ 𝓝 x, cont_mdiff_on I I' n f u :=
by simp [← cont_mdiff_within_at_univ, cont_mdiff_within_at_iff_cont_mdiff_on_nhds,
  nhds_within_univ]

/-- Note: This does not hold for `n = ∞`. `f` being `C^∞` at `x` means that for every `n`, `f` is
`C^n` on some neighborhood of `x`, but this neighborhood can depend on `n`. -/
lemma cont_mdiff_at_iff_cont_mdiff_at_nhds {n : ℕ} :
  cont_mdiff_at I I' n f x ↔ ∀ᶠ x' in 𝓝 x, cont_mdiff_at I I' n f x' :=
begin
  refine ⟨_, λ h, h.self_of_nhds⟩,
  rw [cont_mdiff_at_iff_cont_mdiff_on_nhds],
  rintro ⟨u, hu, h⟩,
  refine (eventually_mem_nhds.mpr hu).mono (λ x' hx', _),
  exact (h x' $ mem_of_mem_nhds hx').cont_mdiff_at hx'
end

omit Is I's

/-! ### Congruence lemmas -/

lemma cont_mdiff_within_at.congr
  (h : cont_mdiff_within_at I I' n f s x) (h₁ : ∀ y ∈ s, f₁ y = f y)
  (hx : f₁ x = f x) : cont_mdiff_within_at I I' n f₁ s x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr h h₁ hx

lemma cont_mdiff_within_at_congr (h₁ : ∀ y ∈ s, f₁ y = f y) (hx : f₁ x = f x) :
  cont_mdiff_within_at I I' n f₁ s x ↔ cont_mdiff_within_at I I' n f s x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr_iff h₁ hx

lemma cont_mdiff_within_at.congr_of_eventually_eq
  (h : cont_mdiff_within_at I I' n f s x) (h₁ : f₁ =ᶠ[𝓝[s] x] f)
  (hx : f₁ x = f x) : cont_mdiff_within_at I I' n f₁ s x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_within_at_congr_of_eventually_eq
  h h₁ hx

lemma filter.eventually_eq.cont_mdiff_within_at_iff
  (h₁ : f₁ =ᶠ[𝓝[s] x] f) (hx : f₁ x = f x) :
  cont_mdiff_within_at I I' n f₁ s x ↔ cont_mdiff_within_at I I' n f s x :=
(cont_diff_within_at_local_invariant_prop I I' n)
  .lift_prop_within_at_congr_iff_of_eventually_eq h₁ hx

lemma cont_mdiff_at.congr_of_eventually_eq
  (h : cont_mdiff_at I I' n f x) (h₁ : f₁ =ᶠ[𝓝 x] f) :
  cont_mdiff_at I I' n f₁ x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_congr_of_eventually_eq h h₁

lemma filter.eventually_eq.cont_mdiff_at_iff (h₁ : f₁ =ᶠ[𝓝 x] f) :
  cont_mdiff_at I I' n f₁ x ↔ cont_mdiff_at I I' n f x :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_at_congr_iff_of_eventually_eq h₁

lemma cont_mdiff_on.congr (h : cont_mdiff_on I I' n f s) (h₁ : ∀ y ∈ s, f₁ y = f y) :
  cont_mdiff_on I I' n f₁ s :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_congr h h₁

lemma cont_mdiff_on_congr (h₁ : ∀ y ∈ s, f₁ y = f y) :
  cont_mdiff_on I I' n f₁ s ↔ cont_mdiff_on I I' n f s :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_congr_iff h₁

/-! ### Locality -/

/-- Being `C^n` is a local property. -/
lemma cont_mdiff_on_of_locally_cont_mdiff_on
  (h : ∀x∈s, ∃u, is_open u ∧ x ∈ u ∧ cont_mdiff_on I I' n f (s ∩ u)) :
  cont_mdiff_on I I' n f s :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_on_of_locally_lift_prop_on h

lemma cont_mdiff_of_locally_cont_mdiff_on
  (h : ∀x, ∃u, is_open u ∧ x ∈ u ∧ cont_mdiff_on I I' n f u) :
  cont_mdiff I I' n f :=
(cont_diff_within_at_local_invariant_prop I I' n).lift_prop_of_locally_lift_prop_on h

/-! ### Smoothness of the composition of smooth functions between manifolds -/

section composition

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
lemma cont_mdiff_within_at.comp {t : set M'} {g : M' → M''} (x : M)
  (hg : cont_mdiff_within_at I' I'' n g t (f x))
  (hf : cont_mdiff_within_at I I' n f s x)
  (st : maps_to f s t) : cont_mdiff_within_at I I'' n (g ∘ f) s x :=
begin
  rw cont_mdiff_within_at_iff at hg hf ⊢,
  refine ⟨hg.1.comp hf.1 st, _⟩,
  set e := ext_chart_at I x,
  set e' := ext_chart_at I' (f x),
  set e'' := ext_chart_at I'' (g (f x)),
  have : e' (f x) = (written_in_ext_chart_at I I' x f) (e x),
    by simp only [e, e'] with mfld_simps,
  rw this at hg,
  have A : ∀ᶠ y in 𝓝[e.symm ⁻¹' s ∩ range I] e x,
    y ∈ e.target ∧ f (e.symm y) ∈ t ∧ f (e.symm y) ∈ e'.source ∧ g (f (e.symm y)) ∈ e''.source,
  { simp only [← map_ext_chart_at_nhds_within, eventually_map],
    filter_upwards [hf.1.tendsto (ext_chart_at_source_mem_nhds I' (f x)),
      (hg.1.comp hf.1 st).tendsto (ext_chart_at_source_mem_nhds I'' (g (f x))),
      (inter_mem_nhds_within s (ext_chart_at_source_mem_nhds I x))],
    rintros x' (hfx' : f x' ∈ _) (hgfx' : g (f x') ∈ _) ⟨hx's, hx'⟩,
    simp only [e.map_source hx', true_and, e.left_inv hx', st hx's, *] },
  refine ((hg.2.comp _ (hf.2.mono (inter_subset_right _ _)) (inter_subset_left _ _)).mono_of_mem
    (inter_mem _ self_mem_nhds_within)).congr_of_eventually_eq _ _,
  { filter_upwards [A],
    rintro x' ⟨hx', ht, hfx', hgfx'⟩,
    simp only [*, mem_preimage, written_in_ext_chart_at, (∘), mem_inter_iff, e'.left_inv, true_and],
    exact mem_range_self _ },
  { filter_upwards [A],
    rintro x' ⟨hx', ht, hfx', hgfx'⟩,
    simp only [*, (∘), written_in_ext_chart_at, e'.left_inv] },
  { simp only [written_in_ext_chart_at, (∘), mem_ext_chart_source, e.left_inv, e'.left_inv] }
end

/-- The composition of `C^∞` functions within domains at points is `C^∞`. -/
lemma smooth_within_at.comp {t : set M'} {g : M' → M''} (x : M)
  (hg : smooth_within_at I' I'' g t (f x))
  (hf : smooth_within_at I I' f s x)
  (st : maps_to f s t) : smooth_within_at I I'' (g ∘ f) s x :=
hg.comp x hf st

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma cont_mdiff_on.comp {t : set M'} {g : M' → M''}
  (hg : cont_mdiff_on I' I'' n g t) (hf : cont_mdiff_on I I' n f s)
  (st : s ⊆ f ⁻¹' t) : cont_mdiff_on I I'' n (g ∘ f) s :=
λ x hx, (hg _ (st hx)).comp x (hf x hx) st

/-- The composition of `C^∞` functions on domains is `C^∞`. -/
lemma smooth_on.comp {t : set M'} {g : M' → M''}
  (hg : smooth_on I' I'' g t) (hf : smooth_on I I' f s)
  (st : s ⊆ f ⁻¹' t) : smooth_on I I'' (g ∘ f) s :=
hg.comp hf st

/-- The composition of `C^n` functions on domains is `C^n`. -/
lemma cont_mdiff_on.comp' {t : set M'} {g : M' → M''}
  (hg : cont_mdiff_on I' I'' n g t) (hf : cont_mdiff_on I I' n f s) :
  cont_mdiff_on I I'' n (g ∘ f) (s ∩ f ⁻¹' t) :=
hg.comp (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of `C^∞` functions is `C^∞`. -/
lemma smooth_on.comp' {t : set M'} {g : M' → M''}
  (hg : smooth_on I' I'' g t) (hf : smooth_on I I' f s) :
  smooth_on I I'' (g ∘ f) (s ∩ f ⁻¹' t) :=
hg.comp' hf

/-- The composition of `C^n` functions is `C^n`. -/
lemma cont_mdiff.comp {g : M' → M''}
  (hg : cont_mdiff I' I'' n g) (hf : cont_mdiff I I' n f) :
  cont_mdiff I I'' n (g ∘ f) :=
begin
  rw ← cont_mdiff_on_univ at hf hg ⊢,
  exact hg.comp hf subset_preimage_univ,
end

/-- The composition of `C^∞` functions is `C^∞`. -/
lemma smooth.comp {g : M' → M''} (hg : smooth I' I'' g) (hf : smooth I I' f) :
  smooth I I'' (g ∘ f) :=
hg.comp hf

/-- The composition of `C^n` functions within domains at points is `C^n`. -/
lemma cont_mdiff_within_at.comp' {t : set M'} {g : M' → M''} (x : M)
  (hg : cont_mdiff_within_at I' I'' n g t (f x))
  (hf : cont_mdiff_within_at I I' n f s x) :
  cont_mdiff_within_at I I'' n (g ∘ f) (s ∩ f⁻¹' t) x :=
hg.comp x (hf.mono (inter_subset_left _ _)) (inter_subset_right _ _)

/-- The composition of `C^∞` functions within domains at points is `C^∞`. -/
lemma smooth_within_at.comp' {t : set M'} {g : M' → M''} (x : M)
  (hg : smooth_within_at I' I'' g t (f x))
  (hf : smooth_within_at I I' f s x) :
  smooth_within_at I I'' (g ∘ f) (s ∩ f⁻¹' t) x :=
hg.comp' x hf

/-- `g ∘ f` is `C^n` within `s` at `x` if `g` is `C^n` at `f x` and
`f` is `C^n` within `s` at `x`. -/
lemma cont_mdiff_at.comp_cont_mdiff_within_at {g : M' → M''} (x : M)
  (hg : cont_mdiff_at I' I'' n g (f x)) (hf : cont_mdiff_within_at I I' n f s x) :
  cont_mdiff_within_at I I'' n (g ∘ f) s x :=
hg.comp x hf (maps_to_univ _ _)

/-- `g ∘ f` is `C^∞` within `s` at `x` if `g` is `C^∞` at `f x` and
`f` is `C^∞` within `s` at `x`. -/
lemma smooth_at.comp_smooth_within_at {g : M' → M''} (x : M)
  (hg : smooth_at I' I'' g (f x)) (hf : smooth_within_at I I' f s x) :
  smooth_within_at I I'' (g ∘ f) s x :=
hg.comp_cont_mdiff_within_at x hf

/-- The composition of `C^n` functions at points is `C^n`. -/
lemma cont_mdiff_at.comp {g : M' → M''} (x : M)
  (hg : cont_mdiff_at I' I'' n g (f x)) (hf : cont_mdiff_at I I' n f x) :
  cont_mdiff_at I I'' n (g ∘ f) x :=
hg.comp x hf (maps_to_univ _ _)

/-- The composition of `C^∞` functions at points is `C^∞`. -/
lemma smooth_at.comp {g : M' → M''} (x : M)
  (hg : smooth_at I' I'' g (f x)) (hf : smooth_at I I' f x) :
  smooth_at I I'' (g ∘ f) x :=
hg.comp x hf

lemma cont_mdiff.comp_cont_mdiff_on {f : M → M'} {g : M' → M''} {s : set M}
  (hg : cont_mdiff I' I'' n g) (hf : cont_mdiff_on I I' n f s) :
  cont_mdiff_on I I'' n (g ∘ f) s :=
hg.cont_mdiff_on.comp hf set.subset_preimage_univ

lemma smooth.comp_smooth_on {f : M → M'} {g : M' → M''} {s : set M}
  (hg : smooth I' I'' g) (hf : smooth_on I I' f s) :
  smooth_on I I'' (g ∘ f) s :=
hg.smooth_on.comp hf set.subset_preimage_univ

lemma cont_mdiff_on.comp_cont_mdiff {t : set M'} {g : M' → M''}
  (hg : cont_mdiff_on I' I'' n g t) (hf : cont_mdiff I I' n f)
  (ht : ∀ x, f x ∈ t) : cont_mdiff I I'' n (g ∘ f) :=
cont_mdiff_on_univ.mp $ hg.comp hf.cont_mdiff_on (λ x _, ht x)

lemma smooth_on.comp_smooth {t : set M'} {g : M' → M''}
  (hg : smooth_on I' I'' g t) (hf : smooth I I' f)
  (ht : ∀ x, f x ∈ t) : smooth I I'' (g ∘ f) :=
hg.comp_cont_mdiff hf ht

end composition

/-! ### Atlas members are smooth -/
section atlas

lemma cont_mdiff_model : cont_mdiff I 𝓘(𝕜, E) n I :=
begin
  intro x,
  refine (cont_mdiff_at_iff _ _).mpr ⟨I.continuous_at, _⟩,
  simp only with mfld_simps,
  refine cont_diff_within_at_id.congr_of_eventually_eq _ _,
  { exact eventually_eq_of_mem self_mem_nhds_within (λ x₂, I.right_inv) },
  simp_rw [function.comp_apply, I.left_inv, id_def]
end

include Is

/-- An atlas member is `C^n` for any `n`. -/
lemma cont_mdiff_on_of_mem_maximal_atlas
  (h : e ∈ maximal_atlas I M) : cont_mdiff_on I I n e e.source :=
cont_mdiff_on.of_le
  ((cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_on_of_mem_maximal_atlas
    (cont_diff_within_at_prop_id I) h) le_top

/-- The inverse of an atlas member is `C^n` for any `n`. -/
lemma cont_mdiff_on_symm_of_mem_maximal_atlas
  (h : e ∈ maximal_atlas I M) : cont_mdiff_on I I n e.symm e.target :=
cont_mdiff_on.of_le
  ((cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_on_symm_of_mem_maximal_atlas
    (cont_diff_within_at_prop_id I) h) le_top

lemma cont_mdiff_at_of_mem_maximal_atlas (h : e ∈ maximal_atlas I M) (hx : x ∈ e.source) :
  cont_mdiff_at I I n e x :=
(cont_mdiff_on_of_mem_maximal_atlas h).cont_mdiff_at $ e.open_source.mem_nhds hx

lemma cont_mdiff_at_symm_of_mem_maximal_atlas {x : H}
  (h : e ∈ maximal_atlas I M) (hx : x ∈ e.target) : cont_mdiff_at I I n e.symm x :=
(cont_mdiff_on_symm_of_mem_maximal_atlas h).cont_mdiff_at $ e.open_target.mem_nhds hx

lemma cont_mdiff_on_chart :
  cont_mdiff_on I I n (chart_at H x) (chart_at H x).source :=
cont_mdiff_on_of_mem_maximal_atlas $ chart_mem_maximal_atlas I x

lemma cont_mdiff_on_chart_symm :
  cont_mdiff_on I I n (chart_at H x).symm (chart_at H x).target :=
cont_mdiff_on_symm_of_mem_maximal_atlas $ chart_mem_maximal_atlas I x

lemma cont_mdiff_at_extend {x : M} (he : e ∈ maximal_atlas I M) (hx : x ∈ e.source) :
  cont_mdiff_at I 𝓘(𝕜, E) n (e.extend I) x :=
(cont_mdiff_model _).comp x $ cont_mdiff_at_of_mem_maximal_atlas he hx

lemma cont_mdiff_at_ext_chart_at' {x' : M} (h : x' ∈ (chart_at H x).source) :
  cont_mdiff_at I 𝓘(𝕜, E) n (ext_chart_at I x) x' :=
cont_mdiff_at_extend (chart_mem_maximal_atlas I x) h

lemma cont_mdiff_at_ext_chart_at : cont_mdiff_at I 𝓘(𝕜, E) n (ext_chart_at I x) x :=
cont_mdiff_at_ext_chart_at' $ mem_chart_source H x

lemma cont_mdiff_on_ext_chart_at :
  cont_mdiff_on I 𝓘(𝕜, E) n (ext_chart_at I x) (chart_at H x).source :=
λ x' hx', (cont_mdiff_at_ext_chart_at' hx').cont_mdiff_within_at

omit Is

/-- An element of `cont_diff_groupoid ⊤ I` is `C^n` for any `n`. -/
lemma cont_mdiff_on_of_mem_cont_diff_groupoid {e' : local_homeomorph H H}
  (h : e' ∈ cont_diff_groupoid ⊤ I) : cont_mdiff_on I I n e' e'.source :=
(cont_diff_within_at_local_invariant_prop I I n).lift_prop_on_of_mem_groupoid
  (cont_diff_within_at_prop_id I) h

end atlas

/-! ### The identity is smooth -/
section id

lemma cont_mdiff_id : cont_mdiff I I n (id : M → M) :=
cont_mdiff.of_le ((cont_diff_within_at_local_invariant_prop I I ∞).lift_prop_id
  (cont_diff_within_at_prop_id I)) le_top

lemma smooth_id : smooth I I (id : M → M) := cont_mdiff_id

lemma cont_mdiff_on_id : cont_mdiff_on I I n (id : M → M) s :=
cont_mdiff_id.cont_mdiff_on

lemma smooth_on_id : smooth_on I I (id : M → M) s := cont_mdiff_on_id

lemma cont_mdiff_at_id : cont_mdiff_at I I n (id : M → M) x :=
cont_mdiff_id.cont_mdiff_at

lemma smooth_at_id : smooth_at I I (id : M → M) x := cont_mdiff_at_id

lemma cont_mdiff_within_at_id : cont_mdiff_within_at I I n (id : M → M) s x :=
cont_mdiff_at_id.cont_mdiff_within_at

lemma smooth_within_at_id : smooth_within_at I I (id : M → M) s x := cont_mdiff_within_at_id

end id

/-! ### Constants are smooth -/
section id

variable {c : M'}

lemma cont_mdiff_const : cont_mdiff I I' n (λ (x : M), c) :=
begin
  assume x,
  refine ⟨continuous_within_at_const, _⟩,
  simp only [cont_diff_within_at_prop, (∘)],
  exact cont_diff_within_at_const,
end

@[to_additive]
lemma cont_mdiff_one [has_one M'] : cont_mdiff I I' n (1 : M → M') :=
by simp only [pi.one_def, cont_mdiff_const]

lemma smooth_const : smooth I I' (λ (x : M), c) := cont_mdiff_const

@[to_additive]
lemma smooth_one [has_one M'] : smooth I I' (1 : M → M') :=
by simp only [pi.one_def, smooth_const]

lemma cont_mdiff_on_const : cont_mdiff_on I I' n (λ (x : M), c) s :=
cont_mdiff_const.cont_mdiff_on

@[to_additive]
lemma cont_mdiff_on_one [has_one M'] : cont_mdiff_on I I' n (1 : M → M') s :=
cont_mdiff_one.cont_mdiff_on

lemma smooth_on_const : smooth_on I I' (λ (x : M), c) s :=
cont_mdiff_on_const

@[to_additive]
lemma smooth_on_one [has_one M'] : smooth_on I I' (1 : M → M') s :=
cont_mdiff_on_one

lemma cont_mdiff_at_const : cont_mdiff_at I I' n (λ (x : M), c) x :=
cont_mdiff_const.cont_mdiff_at

@[to_additive]
lemma cont_mdiff_at_one [has_one M'] : cont_mdiff_at I I' n (1 : M → M') x :=
cont_mdiff_one.cont_mdiff_at

lemma smooth_at_const : smooth_at I I' (λ (x : M), c) x :=
cont_mdiff_at_const

@[to_additive]
lemma smooth_at_one [has_one M'] : smooth_at I I' (1 : M → M') x :=
cont_mdiff_at_one

lemma cont_mdiff_within_at_const : cont_mdiff_within_at I I' n (λ (x : M), c) s x :=
cont_mdiff_at_const.cont_mdiff_within_at

@[to_additive]
lemma cont_mdiff_within_at_one [has_one M'] :
  cont_mdiff_within_at I I' n (1 : M → M') s x :=
cont_mdiff_at_const.cont_mdiff_within_at

lemma smooth_within_at_const : smooth_within_at I I' (λ (x : M), c) s x :=
cont_mdiff_within_at_const

@[to_additive]
lemma smooth_within_at_one [has_one M'] : smooth_within_at I I' (1 : M → M') s x :=
cont_mdiff_within_at_one

end id

lemma cont_mdiff_of_support {f : M → F}
  (hf : ∀ x ∈ tsupport f, cont_mdiff_at I 𝓘(𝕜, F) n f x) :
  cont_mdiff I 𝓘(𝕜, F) n f :=
begin
  intro x,
  by_cases hx : x ∈ tsupport f,
  { exact hf x hx },
  { refine cont_mdiff_at.congr_of_eventually_eq _ (eventually_eq_zero_nhds.2 hx),
    exact cont_mdiff_at_const }
end

/-! ### Equivalence with the basic definition for functions between vector spaces -/

section module

lemma cont_mdiff_within_at_iff_cont_diff_within_at {f : E → E'} {s : set E} {x : E} :
  cont_mdiff_within_at 𝓘(𝕜, E) 𝓘(𝕜, E') n f s x
  ↔ cont_diff_within_at 𝕜 n f s x :=
begin
  simp only [cont_mdiff_within_at, lift_prop_within_at, cont_diff_within_at_prop,
    iff_def] with mfld_simps {contextual := tt},
  exact cont_diff_within_at.continuous_within_at
end

alias cont_mdiff_within_at_iff_cont_diff_within_at ↔
  cont_mdiff_within_at.cont_diff_within_at
  cont_diff_within_at.cont_mdiff_within_at

lemma cont_mdiff_at_iff_cont_diff_at {f : E → E'} {x : E} :
  cont_mdiff_at 𝓘(𝕜, E) 𝓘(𝕜, E') n f x
  ↔ cont_diff_at 𝕜 n f x :=
by rw [← cont_mdiff_within_at_univ,
  cont_mdiff_within_at_iff_cont_diff_within_at, cont_diff_within_at_univ]

alias cont_mdiff_at_iff_cont_diff_at ↔
  cont_mdiff_at.cont_diff_at cont_diff_at.cont_mdiff_at

lemma cont_mdiff_on_iff_cont_diff_on {f : E → E'} {s : set E} :
  cont_mdiff_on 𝓘(𝕜, E) 𝓘(𝕜, E') n f s
  ↔ cont_diff_on 𝕜 n f s :=
forall_congr $ by simp [cont_mdiff_within_at_iff_cont_diff_within_at]

alias cont_mdiff_on_iff_cont_diff_on ↔
  cont_mdiff_on.cont_diff_on cont_diff_on.cont_mdiff_on

lemma cont_mdiff_iff_cont_diff {f : E → E'} :
  cont_mdiff 𝓘(𝕜, E) 𝓘(𝕜, E') n f
  ↔ cont_diff 𝕜 n f :=
by rw [← cont_diff_on_univ, ← cont_mdiff_on_univ,
  cont_mdiff_on_iff_cont_diff_on]

alias cont_mdiff_iff_cont_diff ↔
  cont_mdiff.cont_diff cont_diff.cont_mdiff

lemma cont_diff_within_at.comp_cont_mdiff_within_at
  {g : F → F'} {f : M → F} {s : set M} {t : set F} {x : M}
  (hg : cont_diff_within_at 𝕜 n g t (f x))
  (hf : cont_mdiff_within_at I 𝓘(𝕜, F) n f s x) (h : s ⊆ f ⁻¹' t) :
  cont_mdiff_within_at I 𝓘(𝕜, F') n (g ∘ f) s x :=
begin
  rw cont_mdiff_within_at_iff at *,
  refine ⟨hg.continuous_within_at.comp hf.1 h, _⟩,
  rw [← (ext_chart_at I x).left_inv (mem_ext_chart_source I x)] at hg,
  apply cont_diff_within_at.comp _ (by exact hg) hf.2 _,
  exact (inter_subset_left _ _).trans (preimage_mono h)
end

lemma cont_diff_at.comp_cont_mdiff_at {g : F → F'} {f : M → F} {x : M}
  (hg : cont_diff_at 𝕜 n g (f x)) (hf : cont_mdiff_at I 𝓘(𝕜, F) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F') n (g ∘ f) x :=
hg.comp_cont_mdiff_within_at hf subset.rfl

lemma cont_diff.comp_cont_mdiff {g : F → F'} {f : M → F}
  (hg : cont_diff 𝕜 n g) (hf : cont_mdiff I 𝓘(𝕜, F) n f) :
  cont_mdiff I 𝓘(𝕜, F') n (g ∘ f) :=
λ x, hg.cont_diff_at.comp_cont_mdiff_at (hf x)

end module

/-! ### Smoothness of standard maps associated to the product of manifolds -/

section prod_mk

lemma cont_mdiff_within_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : cont_mdiff_within_at I I' n f s x) (hg : cont_mdiff_within_at I J' n g s x) :
  cont_mdiff_within_at I (I'.prod J') n (λ x, (f x, g x)) s x :=
begin
  rw cont_mdiff_within_at_iff at *,
  exact ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩,
end

lemma cont_mdiff_within_at.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : cont_mdiff_within_at I 𝓘(𝕜, E') n f s x)
  (hg : cont_mdiff_within_at I 𝓘(𝕜, F') n g s x) :
  cont_mdiff_within_at I 𝓘(𝕜, E' × F') n (λ x, (f x, g x)) s x :=
begin
  rw cont_mdiff_within_at_iff at *,
  exact ⟨hf.1.prod hg.1, hf.2.prod hg.2⟩,
end

lemma cont_mdiff_at.prod_mk {f : M → M'} {g : M → N'}
  (hf : cont_mdiff_at I I' n f x) (hg : cont_mdiff_at I J' n g x) :
  cont_mdiff_at I (I'.prod J') n (λ x, (f x, g x)) x :=
hf.prod_mk hg

lemma cont_mdiff_at.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : cont_mdiff_at I 𝓘(𝕜, E') n f x) (hg : cont_mdiff_at I 𝓘(𝕜, F') n g x) :
  cont_mdiff_at I 𝓘(𝕜, E' × F') n (λ x, (f x, g x)) x :=
hf.prod_mk_space hg

lemma cont_mdiff_on.prod_mk {f : M → M'} {g : M → N'}
  (hf : cont_mdiff_on I I' n f s) (hg : cont_mdiff_on I J' n g s) :
  cont_mdiff_on I (I'.prod J') n (λ x, (f x, g x)) s :=
λ x hx, (hf x hx).prod_mk (hg x hx)

lemma cont_mdiff_on.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : cont_mdiff_on I 𝓘(𝕜, E') n f s) (hg : cont_mdiff_on I 𝓘(𝕜, F') n g s) :
  cont_mdiff_on I 𝓘(𝕜, E' × F') n (λ x, (f x, g x)) s :=
λ x hx, (hf x hx).prod_mk_space (hg x hx)

lemma cont_mdiff.prod_mk {f : M → M'} {g : M → N'}
  (hf : cont_mdiff I I' n f) (hg : cont_mdiff I J' n g) :
  cont_mdiff I (I'.prod J') n (λ x, (f x, g x)) :=
λ x, (hf x).prod_mk (hg x)

lemma cont_mdiff.prod_mk_space {f : M → E'} {g : M → F'}
  (hf : cont_mdiff I 𝓘(𝕜, E') n f) (hg : cont_mdiff I 𝓘(𝕜, F') n g) :
  cont_mdiff I 𝓘(𝕜, E' × F') n (λ x, (f x, g x)) :=
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

lemma cont_mdiff_within_at_fst {s : set (M × N)} {p : M × N} :
  cont_mdiff_within_at (I.prod J) I n prod.fst s p :=
begin
  rw cont_mdiff_within_at_iff',
  refine ⟨continuous_within_at_fst, _⟩,
  refine cont_diff_within_at_fst.congr (λ y hy, _) _,
  { simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  { simp only with mfld_simps }
end

lemma cont_mdiff_at_fst {p : M × N} :
  cont_mdiff_at (I.prod J) I n prod.fst p :=
cont_mdiff_within_at_fst

lemma cont_mdiff_on_fst {s : set (M × N)} :
  cont_mdiff_on (I.prod J) I n prod.fst s :=
λ x hx, cont_mdiff_within_at_fst

lemma cont_mdiff_fst :
  cont_mdiff (I.prod J) I n (@prod.fst M N) :=
λ x, cont_mdiff_at_fst

lemma smooth_within_at_fst {s : set (M × N)} {p : M × N} :
  smooth_within_at (I.prod J) I prod.fst s p :=
cont_mdiff_within_at_fst

lemma smooth_at_fst {p : M × N} :
  smooth_at (I.prod J) I prod.fst p :=
cont_mdiff_at_fst

lemma smooth_on_fst {s : set (M × N)} :
  smooth_on (I.prod J) I prod.fst s :=
cont_mdiff_on_fst

lemma smooth_fst :
  smooth (I.prod J) I (@prod.fst M N) :=
cont_mdiff_fst

lemma cont_mdiff_at.fst {f : N → M × M'} {x : N} (hf : cont_mdiff_at J (I.prod I') n f x) :
  cont_mdiff_at J I n (λ x, (f x).1) x :=
cont_mdiff_at_fst.comp x hf

lemma cont_mdiff.fst {f : N → M × M'} (hf : cont_mdiff J (I.prod I') n f) :
  cont_mdiff J I n (λ x, (f x).1) :=
cont_mdiff_fst.comp hf

lemma smooth_at.fst {f : N → M × M'} {x : N} (hf : smooth_at J (I.prod I') f x) :
  smooth_at J I (λ x, (f x).1) x :=
smooth_at_fst.comp x hf

lemma smooth.fst {f : N → M × M'} (hf : smooth J (I.prod I') f) :
  smooth J I (λ x, (f x).1) :=
smooth_fst.comp hf

lemma cont_mdiff_within_at_snd {s : set (M × N)} {p : M × N} :
  cont_mdiff_within_at (I.prod J) J n prod.snd s p :=
begin
  rw cont_mdiff_within_at_iff',
  refine ⟨continuous_within_at_snd, _⟩,
  refine cont_diff_within_at_snd.congr (λ y hy, _) _,
  { simp only with mfld_simps at hy,
    simp only [hy] with mfld_simps },
  { simp only with mfld_simps }
end

lemma cont_mdiff_at_snd {p : M × N} :
  cont_mdiff_at (I.prod J) J n prod.snd p :=
cont_mdiff_within_at_snd

lemma cont_mdiff_on_snd {s : set (M × N)} :
  cont_mdiff_on (I.prod J) J n prod.snd s :=
λ x hx, cont_mdiff_within_at_snd

lemma cont_mdiff_snd :
  cont_mdiff (I.prod J) J n (@prod.snd M N) :=
λ x, cont_mdiff_at_snd

lemma smooth_within_at_snd {s : set (M × N)} {p : M × N} :
  smooth_within_at (I.prod J) J prod.snd s p :=
cont_mdiff_within_at_snd

lemma smooth_at_snd {p : M × N} :
  smooth_at (I.prod J) J prod.snd p :=
cont_mdiff_at_snd

lemma smooth_on_snd {s : set (M × N)} :
  smooth_on (I.prod J) J prod.snd s :=
cont_mdiff_on_snd

lemma smooth_snd :
  smooth (I.prod J) J (@prod.snd M N) :=
cont_mdiff_snd

lemma cont_mdiff_at.snd {f : N → M × M'} {x : N} (hf : cont_mdiff_at J (I.prod I') n f x) :
  cont_mdiff_at J I' n (λ x, (f x).2) x :=
cont_mdiff_at_snd.comp x hf

lemma cont_mdiff.snd {f : N → M × M'} (hf : cont_mdiff J (I.prod I') n f) :
  cont_mdiff J I' n (λ x, (f x).2) :=
cont_mdiff_snd.comp hf

lemma smooth_at.snd {f : N → M × M'} {x : N} (hf : smooth_at J (I.prod I') f x) :
  smooth_at J I' (λ x, (f x).2) x :=
smooth_at_snd.comp x hf

lemma smooth.snd {f : N → M × M'} (hf : smooth J (I.prod I') f) :
  smooth J I' (λ x, (f x).2) :=
smooth_snd.comp hf

lemma smooth_iff_proj_smooth {f : M → M' × N'} :
  (smooth I (I'.prod J') f) ↔ (smooth I I' (prod.fst ∘ f)) ∧ (smooth I J' (prod.snd ∘ f)) :=
begin
  split,
  { intro h, exact ⟨smooth_fst.comp h, smooth_snd.comp h⟩ },
  { rintro ⟨h_fst, h_snd⟩, simpa only [prod.mk.eta] using h_fst.prod_mk h_snd, }
end

lemma smooth_prod_assoc :
  smooth ((I.prod I').prod J) (I.prod (I'.prod J)) (λ x : (M × M') × N, (x.1.1, x.1.2, x.2)) :=
smooth_fst.fst.prod_mk $ smooth_fst.snd.prod_mk smooth_snd

end projections

section prod_map

variables {g : N → N'} {r : set N} {y : N}

/-- The product map of two `C^n` functions within a set at a point is `C^n`
within the product set at the product point. -/
lemma cont_mdiff_within_at.prod_map' {p : M × N}
  (hf : cont_mdiff_within_at I I' n f s p.1)
  (hg : cont_mdiff_within_at J J' n g r p.2) :
  cont_mdiff_within_at (I.prod J) (I'.prod J') n (prod.map f g) (s ×ˢ r) p :=
(hf.comp p cont_mdiff_within_at_fst (prod_subset_preimage_fst _ _)).prod_mk $
hg.comp p cont_mdiff_within_at_snd (prod_subset_preimage_snd _ _)

lemma cont_mdiff_within_at.prod_map
  (hf : cont_mdiff_within_at I I' n f s x) (hg : cont_mdiff_within_at J J' n g r y) :
  cont_mdiff_within_at (I.prod J) (I'.prod J') n (prod.map f g) (s ×ˢ r) (x, y) :=
cont_mdiff_within_at.prod_map' hf hg

lemma cont_mdiff_at.prod_map
  (hf : cont_mdiff_at I I' n f x) (hg : cont_mdiff_at J J' n g y) :
  cont_mdiff_at (I.prod J) (I'.prod J') n (prod.map f g) (x, y) :=
begin
  rw ← cont_mdiff_within_at_univ at *,
  convert hf.prod_map hg,
  exact univ_prod_univ.symm
end

lemma cont_mdiff_at.prod_map' {p : M × N}
  (hf : cont_mdiff_at I I' n f p.1) (hg : cont_mdiff_at J J' n g p.2) :
  cont_mdiff_at (I.prod J) (I'.prod J') n (prod.map f g) p :=
begin
  rcases p,
  exact hf.prod_map hg
end

lemma cont_mdiff_on.prod_map
  (hf : cont_mdiff_on I I' n f s) (hg : cont_mdiff_on J J' n g r) :
  cont_mdiff_on (I.prod J) (I'.prod J') n (prod.map f g) (s ×ˢ r) :=
(hf.comp cont_mdiff_on_fst (prod_subset_preimage_fst _ _)).prod_mk $
hg.comp (cont_mdiff_on_snd) (prod_subset_preimage_snd _ _)

lemma cont_mdiff.prod_map
  (hf : cont_mdiff I I' n f) (hg : cont_mdiff J J' n g) :
  cont_mdiff (I.prod J) (I'.prod J') n (prod.map f g) :=
begin
  assume p,
  exact (hf p.1).prod_map' (hg p.2)
end

lemma smooth_within_at.prod_map
  (hf : smooth_within_at I I' f s x) (hg : smooth_within_at J J' g r y) :
  smooth_within_at (I.prod J) (I'.prod J') (prod.map f g) (s ×ˢ r) (x, y) :=
hf.prod_map hg

lemma smooth_at.prod_map
  (hf : smooth_at I I' f x) (hg : smooth_at J J' g y) :
  smooth_at (I.prod J) (I'.prod J') (prod.map f g) (x, y) :=
hf.prod_map hg

lemma smooth_on.prod_map
  (hf : smooth_on I I' f s) (hg : smooth_on J J' g r) :
  smooth_on (I.prod J) (I'.prod J') (prod.map f g) (s ×ˢ r) :=
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

variables {ι : Type*} [fintype ι] {Fi : ι → Type*} [Π i, normed_add_comm_group (Fi i)]
  [Π i, normed_space 𝕜 (Fi i)] {φ : M → Π i, Fi i}

lemma cont_mdiff_within_at_pi_space :
  cont_mdiff_within_at I (𝓘(𝕜, Π i, Fi i)) n φ s x ↔
    ∀ i, cont_mdiff_within_at I (𝓘(𝕜, Fi i)) n (λ x, φ x i) s x :=
by simp only [cont_mdiff_within_at_iff, continuous_within_at_pi,
  cont_diff_within_at_pi, forall_and_distrib, written_in_ext_chart_at,
  ext_chart_at_model_space_eq_id, (∘), local_equiv.refl_coe, id]

lemma cont_mdiff_on_pi_space :
  cont_mdiff_on I (𝓘(𝕜, Π i, Fi i)) n φ s ↔
    ∀ i, cont_mdiff_on I (𝓘(𝕜, Fi i)) n (λ x, φ x i) s :=
⟨λ h i x hx, cont_mdiff_within_at_pi_space.1 (h x hx) i,
  λ h x hx, cont_mdiff_within_at_pi_space.2 (λ i, h i x hx)⟩

lemma cont_mdiff_at_pi_space :
  cont_mdiff_at I (𝓘(𝕜, Π i, Fi i)) n φ x ↔
    ∀ i, cont_mdiff_at I (𝓘(𝕜, Fi i)) n (λ x, φ x i) x :=
cont_mdiff_within_at_pi_space

lemma cont_mdiff_pi_space :
  cont_mdiff I (𝓘(𝕜, Π i, Fi i)) n φ ↔
    ∀ i, cont_mdiff I (𝓘(𝕜, Fi i)) n (λ x, φ x i) :=
⟨λ h i x, cont_mdiff_at_pi_space.1 (h x) i,
  λ h x, cont_mdiff_at_pi_space.2 (λ i, h i x)⟩

lemma smooth_within_at_pi_space :
  smooth_within_at I (𝓘(𝕜, Π i, Fi i)) φ s x ↔
    ∀ i, smooth_within_at I (𝓘(𝕜, Fi i)) (λ x, φ x i) s x :=
cont_mdiff_within_at_pi_space

lemma smooth_on_pi_space :
  smooth_on I (𝓘(𝕜, Π i, Fi i)) φ s ↔ ∀ i, smooth_on I (𝓘(𝕜, Fi i)) (λ x, φ x i) s :=
cont_mdiff_on_pi_space

lemma smooth_at_pi_space :
  smooth_at I (𝓘(𝕜, Π i, Fi i)) φ x ↔ ∀ i, smooth_at I (𝓘(𝕜, Fi i)) (λ x, φ x i) x :=
cont_mdiff_at_pi_space

lemma smooth_pi_space :
  smooth I (𝓘(𝕜, Π i, Fi i)) φ ↔ ∀ i, smooth I (𝓘(𝕜, Fi i)) (λ x, φ x i) :=
cont_mdiff_pi_space

end pi_space

/-! ### Linear maps between normed spaces are smooth -/

lemma continuous_linear_map.cont_mdiff (L : E →L[𝕜] F) :
  cont_mdiff 𝓘(𝕜, E) 𝓘(𝕜, F) n L :=
L.cont_diff.cont_mdiff

lemma cont_mdiff_within_at.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : set M} {x : M}
  (hg : cont_mdiff_within_at I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
  (hf : cont_mdiff_within_at I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f s x) :
  cont_mdiff_within_at I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (λ x, (g x).comp (f x)) s x :=
@cont_diff_within_at.comp_cont_mdiff_within_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (λ x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₁), x.1.comp x.2) (λ x, (g x, f x)) s _ x
  (by { apply cont_diff.cont_diff_at, exact cont_diff_fst.clm_comp cont_diff_snd })
  (hg.prod_mk_space hf) (by simp_rw [preimage_univ, subset_univ])

lemma cont_mdiff_at.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {x : M}
  (hg : cont_mdiff_at I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x) (hf : cont_mdiff_at I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (λ x, (g x).comp (f x)) x :=
(hg.cont_mdiff_within_at.clm_comp hf.cont_mdiff_within_at).cont_mdiff_at univ_mem

lemma cont_mdiff_on.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁} {s : set M}
  (hg : cont_mdiff_on I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s) (hf : cont_mdiff_on I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f s) :
  cont_mdiff_on I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (λ x, (g x).comp (f x)) s :=
λ x hx, (hg x hx).clm_comp (hf x hx)

lemma cont_mdiff.clm_comp {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₁}
  (hg : cont_mdiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g) (hf : cont_mdiff I 𝓘(𝕜, F₂ →L[𝕜] F₁) n f) :
  cont_mdiff I 𝓘(𝕜, F₂ →L[𝕜] F₃) n (λ x, (g x).comp (f x)) :=
λ x, (hg x).clm_comp (hf x)

lemma cont_mdiff_within_at.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : set M} {x : M}
  (hg : cont_mdiff_within_at I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g s x)
  (hf : cont_mdiff_within_at I 𝓘(𝕜, F₁) n f s x) :
  cont_mdiff_within_at I 𝓘(𝕜, F₂) n (λ x, g x (f x)) s x :=
@cont_diff_within_at.comp_cont_mdiff_within_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (λ x : (F₁ →L[𝕜] F₂) × F₁, x.1 x.2) (λ x, (g x, f x)) s _ x
  (by { apply cont_diff.cont_diff_at, exact cont_diff_fst.clm_apply cont_diff_snd })
  (hg.prod_mk_space hf) (by simp_rw [preimage_univ, subset_univ])

lemma cont_mdiff_at.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {x : M}
  (hg : cont_mdiff_at I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g x) (hf : cont_mdiff_at I 𝓘(𝕜, F₁) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F₂) n (λ x, g x (f x)) x :=
(hg.cont_mdiff_within_at.clm_apply hf.cont_mdiff_within_at).cont_mdiff_at univ_mem

lemma cont_mdiff_on.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁} {s : set M}
  (hg : cont_mdiff_on I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g s) (hf : cont_mdiff_on I 𝓘(𝕜, F₁) n f s) :
  cont_mdiff_on I 𝓘(𝕜, F₂) n (λ x, g x (f x)) s :=
λ x hx, (hg x hx).clm_apply (hf x hx)

lemma cont_mdiff.clm_apply {g : M → F₁ →L[𝕜] F₂} {f : M → F₁}
  (hg : cont_mdiff I 𝓘(𝕜, F₁ →L[𝕜] F₂) n g) (hf : cont_mdiff I 𝓘(𝕜, F₁) n f) :
  cont_mdiff I 𝓘(𝕜, F₂) n (λ x, g x (f x)) :=
λ x, (hg x).clm_apply (hf x)

lemma cont_mdiff_within_at.clm_prod_map
  {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : set M} {x : M}
  (hg : cont_mdiff_within_at I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s x)
  (hf : cont_mdiff_within_at I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f s x) :
  cont_mdiff_within_at I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (λ x, (g x).prod_map (f x)) s x :=
@cont_diff_within_at.comp_cont_mdiff_within_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
  (λ x : (F₁ →L[𝕜] F₃) × (F₂ →L[𝕜] F₄), x.1.prod_map x.2) (λ x, (g x, f x)) s _ x
  (by { apply cont_diff.cont_diff_at,
    exact (continuous_linear_map.prod_mapL 𝕜 F₁ F₃ F₂ F₄).cont_diff })
  (hg.prod_mk_space hf) (by simp_rw [preimage_univ, subset_univ])

lemma cont_mdiff_at.clm_prod_map {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {x : M}
  (hg : cont_mdiff_at I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g x) (hf : cont_mdiff_at I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f x) :
  cont_mdiff_at I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (λ x, (g x).prod_map (f x)) x :=
(hg.cont_mdiff_within_at.clm_prod_map hf.cont_mdiff_within_at).cont_mdiff_at univ_mem

lemma cont_mdiff_on.clm_prod_map {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄} {s : set M}
  (hg : cont_mdiff_on I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g s) (hf : cont_mdiff_on I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f s) :
  cont_mdiff_on I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (λ x, (g x).prod_map (f x)) s :=
λ x hx, (hg x hx).clm_prod_map (hf x hx)

lemma cont_mdiff.clm_prod_map {g : M → F₁ →L[𝕜] F₃} {f : M → F₂ →L[𝕜] F₄}
  (hg : cont_mdiff I 𝓘(𝕜, F₁ →L[𝕜] F₃) n g) (hf : cont_mdiff I 𝓘(𝕜, F₂ →L[𝕜] F₄) n f) :
  cont_mdiff I 𝓘(𝕜, F₁ × F₂ →L[𝕜] F₃ × F₄) n (λ x, (g x).prod_map (f x)) :=
λ x, (hg x).clm_prod_map (hf x)

/-! ### Smoothness of standard operations -/

variables {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V]

/-- On any vector space, multiplication by a scalar is a smooth operation. -/
lemma smooth_smul : smooth (𝓘(𝕜).prod 𝓘(𝕜, V)) 𝓘(𝕜, V) (λp : 𝕜 × V, p.1 • p.2) :=
smooth_iff.2 ⟨continuous_smul, λ x y, cont_diff_smul.cont_diff_on⟩

lemma cont_mdiff_within_at.smul {f : M → 𝕜} {g : M → V} (hf : cont_mdiff_within_at I 𝓘(𝕜) n f s x)
  (hg : cont_mdiff_within_at I 𝓘(𝕜, V) n g s x) :
  cont_mdiff_within_at I 𝓘(𝕜, V) n (λ p, f p • g p) s x :=
(smooth_smul.of_le le_top).cont_mdiff_at.comp_cont_mdiff_within_at x (hf.prod_mk hg)

lemma cont_mdiff_at.smul {f : M → 𝕜} {g : M → V} (hf : cont_mdiff_at I 𝓘(𝕜) n f x)
  (hg : cont_mdiff_at I 𝓘(𝕜, V) n g x) :
  cont_mdiff_at I 𝓘(𝕜, V) n (λ p, f p • g p) x :=
hf.smul hg

lemma cont_mdiff_on.smul {f : M → 𝕜} {g : M → V} (hf : cont_mdiff_on I 𝓘(𝕜) n f s)
  (hg : cont_mdiff_on I 𝓘(𝕜, V) n g s) :
  cont_mdiff_on I 𝓘(𝕜, V) n (λ p, f p • g p) s :=
λ x hx, (hf x hx).smul (hg x hx)

lemma cont_mdiff.smul {f : M → 𝕜} {g : M → V} (hf : cont_mdiff I 𝓘(𝕜) n f)
  (hg : cont_mdiff I 𝓘(𝕜, V) n g) :
  cont_mdiff I 𝓘(𝕜, V) n (λ p, f p • g p) :=
λ x, (hf x).smul (hg x)

lemma smooth_within_at.smul {f : M → 𝕜} {g : M → V} (hf : smooth_within_at I 𝓘(𝕜) f s x)
  (hg : smooth_within_at I 𝓘(𝕜, V) g s x) :
  smooth_within_at I 𝓘(𝕜, V) (λ p, f p • g p) s x :=
hf.smul hg

lemma smooth_at.smul {f : M → 𝕜} {g : M → V} (hf : smooth_at I 𝓘(𝕜) f x)
  (hg : smooth_at I 𝓘(𝕜, V) g x) :
  smooth_at I 𝓘(𝕜, V) (λ p, f p • g p) x :=
hf.smul hg

lemma smooth_on.smul {f : M → 𝕜} {g : M → V} (hf : smooth_on I 𝓘(𝕜) f s)
  (hg : smooth_on I 𝓘(𝕜, V) g s) :
  smooth_on I 𝓘(𝕜, V) (λ p, f p • g p) s :=
hf.smul hg

lemma smooth.smul {f : M → 𝕜} {g : M → V} (hf : smooth I 𝓘(𝕜) f) (hg : smooth I 𝓘(𝕜, V) g) :
  smooth I 𝓘(𝕜, V) (λ p, f p • g p) :=
hf.smul hg

/-! ### Smoothness of (local) structomorphisms -/
section

variables [charted_space H M'] [IsM' : smooth_manifold_with_corners I M']
include Is IsM'

lemma is_local_structomorph_on_cont_diff_groupoid_iff_aux {f : local_homeomorph M M'}
  (hf : lift_prop_on (cont_diff_groupoid ⊤ I).is_local_structomorph_within_at f f.source) :
  smooth_on I I f f.source :=
begin
  -- It suffices to show smoothness near each `x`
  apply cont_mdiff_on_of_locally_cont_mdiff_on,
  intros x hx,
  let c := chart_at H x,
  let c' := chart_at H (f x),
  obtain ⟨-, hxf⟩ := hf x hx,
  -- Since `f` is a local structomorph, it is locally equal to some transferred element `e` of
  -- the `cont_diff_groupoid`.
  obtain ⟨e, he, he' : eq_on (c' ∘ f ∘ c.symm) e (c.symm ⁻¹' f.source ∩ e.source),
    hex : c x ∈ e.source⟩ := hxf (by simp only [hx] with mfld_simps),
  -- We choose a convenient set `s` in `M`.
  let s : set M := (f.trans c').source ∩ ((c.trans e).trans c'.symm).source,
  refine ⟨s, (f.trans c').open_source.inter ((c.trans e).trans c'.symm).open_source, _, _⟩,
  { simp only with mfld_simps,
    rw ← he'; simp only [hx, hex] with mfld_simps },
  -- We need to show `f` is `cont_mdiff_on` the domain `s ∩ f.source`.  We show this in two
  -- steps: `f` is equal to `c'.symm ∘ e ∘ c` on that domain and that function is
  -- `cont_mdiff_on` it.
  have H₁ : cont_mdiff_on I I ⊤ (c'.symm ∘ e ∘ c) s,
  { have hc' : cont_mdiff_on I I ⊤ c'.symm _ := cont_mdiff_on_chart_symm,
    have he'' : cont_mdiff_on I I ⊤ e _ := cont_mdiff_on_of_mem_cont_diff_groupoid he,
    have hc : cont_mdiff_on I I ⊤ c _ := cont_mdiff_on_chart,
    refine (hc'.comp' (he''.comp' hc)).mono _,
    mfld_set_tac },
  have H₂ : eq_on f (c'.symm ∘ e ∘ c) s,
  { intros y hy,
    simp only with mfld_simps at hy,
    have hy₁ : f y ∈ c'.source := by simp only [hy] with mfld_simps,
    have hy₂ : y ∈ c.source := by simp only [hy] with mfld_simps,
    have hy₃ : c y ∈ c.symm ⁻¹' f.source ∩ e.source := by simp only [hy] with mfld_simps,
    calc f y = c'.symm (c' (f y)) : by rw c'.left_inv hy₁
    ... = c'.symm (c' (f (c.symm (c y)))) : by rw c.left_inv hy₂
    ... = c'.symm (e (c y)) : by rw ← he' hy₃ },
  refine (H₁.congr H₂).mono _,
  mfld_set_tac
end

/-- Let `M` and `M'` be smooth manifolds with the same model-with-corners, `I`.  Then `f : M → M'`
is a local structomorphism for `I`, if and only if it is manifold-smooth on the domain of definition
in both directions. -/
lemma is_local_structomorph_on_cont_diff_groupoid_iff (f : local_homeomorph M M') :
  lift_prop_on (cont_diff_groupoid ⊤ I).is_local_structomorph_within_at f f.source
  ↔ smooth_on I I f f.source ∧ smooth_on I I f.symm f.target :=
begin
  split,
  { intros h,
    refine ⟨is_local_structomorph_on_cont_diff_groupoid_iff_aux h,
      is_local_structomorph_on_cont_diff_groupoid_iff_aux _⟩,
    -- todo: we can generalize this part of the proof to a lemma
    intros X hX,
    let x := f.symm X,
    have hx : x ∈ f.source := f.symm.maps_to hX,
    let c := chart_at H x,
    let c' := chart_at H X,
    obtain ⟨-, hxf⟩ := h x hx,
    refine ⟨(f.symm.continuous_at hX).continuous_within_at, λ h2x, _⟩,
    obtain ⟨e, he, h2e, hef, hex⟩ : ∃ e : local_homeomorph H H, e ∈ cont_diff_groupoid ⊤ I ∧
      e.source ⊆ (c.symm ≫ₕ f ≫ₕ c').source ∧
      eq_on (c' ∘ f ∘ c.symm) e e.source ∧ c x ∈ e.source,
    { have h1 : c' = chart_at H (f x) := by simp only [f.right_inv hX],
      have h2 : ⇑c' ∘ ⇑f ∘ ⇑(c.symm) = ⇑(c.symm ≫ₕ f ≫ₕ c') := rfl,
      have hcx : c x ∈ c.symm ⁻¹' f.source, { simp only [hx] with mfld_simps },
      rw [h2],
      rw [← h1, h2, local_homeomorph.is_local_structomorph_within_at_iff'] at hxf,
      { exact hxf hcx },
      { mfld_set_tac },
      { apply or.inl,
        simp only [hx, h1] with mfld_simps } },
    have h2X : c' X = e (c (f.symm X)),
    { rw ← hef hex,
      dsimp only [function.comp],
      have hfX : f.symm X ∈ c.source := by simp only [hX] with mfld_simps,
      rw [c.left_inv hfX, f.right_inv hX] },
    have h3e : eq_on (c ∘ f.symm ∘ c'.symm) e.symm (c'.symm ⁻¹' f.target ∩ e.target),
    { have h1 : eq_on (c.symm ≫ₕ f ≫ₕ c').symm e.symm (e.target ∩ e.target),
      { apply eq_on.symm,
        refine e.is_image_source_target.symm_eq_on_of_inter_eq_of_eq_on _ _,
        { rw [inter_self, inter_eq_right_iff_subset.mpr h2e] },
        rw [inter_self], exact hef.symm },
      have h2 : e.target ⊆ (c.symm ≫ₕ f ≫ₕ c').target,
      { intros x hx, rw [← e.right_inv hx, ← hef (e.symm.maps_to hx)],
        exact local_homeomorph.maps_to _ (h2e $ e.symm.maps_to hx) },
      rw [inter_self] at h1,
      rwa [inter_eq_right_iff_subset.mpr],
      refine h2.trans _,
      mfld_set_tac },
    refine ⟨e.symm, structure_groupoid.symm _ he, h3e, _⟩,
    rw [h2X], exact e.maps_to hex },
  { -- We now show the converse: a local homeomorphism `f : M → M'` which is smooth in both
    -- directions is a local structomorphism.  We do this by proposing
    -- `((chart_at H x).symm.trans f).trans (chart_at H (f x))` as a candidate for a structomorphism
    -- of `H`.
    rintros ⟨h₁, h₂⟩ x hx,
    refine ⟨(h₁ x hx).continuous_within_at, _⟩,
    let c := chart_at H x,
    let c' := chart_at H (f x),
    rintros (hx' : c x ∈ c.symm ⁻¹' f.source),
    -- propose `(c.symm.trans f).trans c'` as a candidate for a local structomorphism of `H`
    refine ⟨(c.symm.trans f).trans c', ⟨_, _⟩, (_ : eq_on (c' ∘ f ∘ c.symm) _ _), _⟩,
    { -- smoothness of the candidate local structomorphism in the forward direction
      intros y hy,
      simp only with mfld_simps at hy,
      have H : cont_mdiff_within_at I I ⊤ f (f ≫ₕ c').source (((ext_chart_at I x).symm) y),
      { refine (h₁ ((ext_chart_at I x).symm y) _).mono _,
        { simp only [hy] with mfld_simps },
        { mfld_set_tac } },
      have hy' : (ext_chart_at I x).symm y ∈ c.source := by simp only [hy] with mfld_simps,
      have hy'' : f ((ext_chart_at I x).symm y) ∈ c'.source := by simp only [hy] with mfld_simps,
      rw cont_mdiff_within_at_iff_of_mem_source hy' hy'' at H,
      { convert H.2.mono _,
        { simp only [hy] with mfld_simps },
        { mfld_set_tac } },
      { apply_instance },
      { apply_instance } },
    { -- smoothness of the candidate local structomorphism in the reverse direction
      intros y hy,
      simp only with mfld_simps at hy,
      have H : cont_mdiff_within_at I I ⊤ f.symm (f.symm ≫ₕ c).source
        (((ext_chart_at I (f x)).symm) y),
      { refine (h₂ ((ext_chart_at I (f x)).symm y) _).mono _,
        { simp only [hy] with mfld_simps },
        { mfld_set_tac } },
      have hy' : (ext_chart_at I (f x)).symm y ∈ c'.source := by simp only [hy] with mfld_simps,
      have hy'' : f.symm ((ext_chart_at I (f x)).symm y) ∈ c.source,
      { simp only [hy] with mfld_simps },
      rw cont_mdiff_within_at_iff_of_mem_source hy' hy'' at H,
      { convert H.2.mono _,
        { simp only [hy] with mfld_simps },
        { mfld_set_tac } },
      { apply_instance },
      { apply_instance } },
    -- now check the candidate local structomorphism agrees with `f` where it is supposed to
    { simp only with mfld_simps },
    { simp only [hx'] with mfld_simps } },
end

end
