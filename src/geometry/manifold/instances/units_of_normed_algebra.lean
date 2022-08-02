/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Heather Macbeth
-/

import geometry.manifold.smooth_manifold_with_corners
import geometry.manifold.algebra.lie_group
import analysis.normed_space.units

/-!
# Units of a normed algebra

This file is a stub, containing a construction of the charted space structure on the group of units
of a complete normed ring `R`, and of the smooth manifold structure on the group of units of a
complete normed `𝕜`-algebra `R`.

This manifold is actually a Lie group, which eventually should be the main result of this file.

An important special case of this construction is the general linear group.  For a normed space `V`
over a field `𝕜`, the `𝕜`-linear endomorphisms of `V` are a normed `𝕜`-algebra (see
`continuous_linear_map.to_normed_algebra`), so this construction provides a Lie group structure on
its group of units, the general linear group GL(`𝕜`, `V`).

## TODO

The Lie group instance requires the following fields:
```
instance : lie_group 𝓘(𝕜, R) Rˣ :=
{ smooth_mul := sorry,
  smooth_inv := sorry,
  ..units.smooth_manifold_with_corners }
```

The ingredients needed for the construction are
* smoothness of multiplication and inversion in the charts, i.e. as functions on the normed
  `𝕜`-space `R`:  see `cont_diff_at_ring_inverse` for the inversion result, and
  `cont_diff_mul` (needs to be generalized from field to algebra) for the multiplication
  result
* for an open embedding `f`, whose domain is equipped with the induced manifold structure
  `f.singleton_smooth_manifold_with_corners`, characterization of smoothness of functions to/from
  this manifold in terms of smoothness in the target space.  See the pair of lemmas
  `cont_mdiff_coe_sphere` and `cont_mdiff.cod_restrict_sphere` for a model.
None of this should be particularly difficult.

-/

noncomputable theory

open_locale manifold

/-- Continuous differentiability of a function between manifolds can be stated in terms of the
continuous differentiability of the corresponding function on the model vector space. This requires
that the extended charts on the manifolds coincide with an open embedding of the manifold into the
model vector space.

TODO: Restructure proof and rearrange variables -/
lemma open_embedding_cont_diff_on_cont_mdiff'
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M]
  [smooth_manifold_with_corners I M]
  (e : M → E) {he : open_embedding e} (hce : ∀ x y, (ext_chart_at I x) y = e y)
  (htarg : ∀ x : M, (ext_chart_at I x).target = set.range e)
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {M' : Type*} [topological_space M'] [charted_space H' M']
  [smooth_manifold_with_corners I' M']
  (e' : M' → E') {he' : open_embedding e'} (hce' : ∀ x y, (ext_chart_at I' x) y = e' y)
  {n : with_top ℕ} {f : E → E'} (H : cont_diff_on 𝕜 n f (set.range e))
  {g : M → M'} (hfg : e' ∘ g = f ∘ e) :
  cont_mdiff I I' n g :=
begin
  rw cont_mdiff_iff,
  split,
  { rw continuous_def,
    intros s hs,
    rw ←set.preimage_image_eq s he'.inj,
    rw ←set.preimage_comp,
    rw hfg,
    have hcont : continuous (f ∘ e),
    { apply continuous_on.comp_continuous
        (cont_diff_on.continuous_on H)
        (open_embedding.continuous he),
      exact λ y, ⟨y, rfl⟩ },
    apply continuous.is_open_preimage hcont,
    exact he'.open_iff_image_open.mp hs },
    { intros,
      apply cont_diff_on.congr_mono,
      swap 4,
      exact set.range e,
      swap 4,
      exact f,
      swap 3,
      rw set.subset_def,
      intros a ha,
      cases ha with ha ha',
      rw htarg at ha,
      exact ha,

      exact H,

      intros a ha,
      rw [function.comp_app, hce', ←function.comp_app e' g, hfg, function.comp_app, ←hce x,
        local_equiv.right_inv],
      exact ha.1 }
end

/-- A weaker version of `units.open_embedding_cont_diff_on_cont_mdiff` in which the model space H
coincides with the model vector space E via `model_with_corners_self` and the chart is given by the
open embedding itself. -/
lemma open_embedding_cont_diff_on_cont_mdiff
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {M : Type*} [topological_space M] [nonempty M]
  (e : M → E) {he : open_embedding e}
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {M' : Type*} [topological_space M'] [nonempty M']
  (e' : M' → E') {he' : open_embedding e'}
  {n : with_top ℕ} {f : E → E'} (H : cont_diff_on 𝕜 n f (set.range e))
  {g : M → M'} (hfg : e' ∘ g = f ∘ e) :
  @cont_mdiff _ _ _ _ _ _ _ 𝓘(𝕜, E) _ _ he.singleton_charted_space
    _ _ _ _ _ 𝓘(𝕜, E') _ _ he'.singleton_charted_space n g :=
begin
  apply @open_embedding_cont_diff_on_cont_mdiff' 𝕜 _
    E _ _ E _ 𝓘(𝕜, E) M _ he.singleton_charted_space
    (he.singleton_smooth_manifold_with_corners 𝓘(𝕜, E)) e he (_) (_)
    E' _ _ E' _ 𝓘(𝕜, E') M' _ he'.singleton_charted_space
    (he'.singleton_smooth_manifold_with_corners 𝓘(𝕜, E')) e' he' (_)
    n f H _ hfg;
  simp
end

namespace units

variables {R : Type*} [normed_ring R] [complete_space R]

instance : charted_space R Rˣ := open_embedding_coe.singleton_charted_space

lemma chart_at_apply {a : Rˣ} {b : Rˣ} : chart_at R a b = b := rfl
lemma chart_at_source {a : Rˣ} : (chart_at R a).source = set.univ := rfl

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [normed_algebra 𝕜 R]

instance : smooth_manifold_with_corners 𝓘(𝕜, R) Rˣ :=
open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(𝕜, R)

lemma smooth_mul :
  smooth (𝓘(𝕜, R).prod 𝓘(𝕜, R)) 𝓘(𝕜, R) (λ (p : Rˣ × Rˣ), p.fst * p.snd) :=
begin
  apply @open_embedding_cont_diff_on_cont_mdiff' 𝕜 _
    (R × R) _ _ (model_prod R R) _ _ (Rˣ × Rˣ) _ _ _ (λ x, (x.1, x.2))
    (by {apply open_embedding.prod open_embedding_coe open_embedding_coe; apply_instance}) _ _
    R _ _ R _ _ Rˣ _ _ _ coe open_embedding_coe _ _ ⊤ (λ x, x.1 * x.2),
  { exact cont_diff.cont_diff_on cont_diff_mul },
  { ext, simp },
  { apply_instance },
  { simp },
  { intro,
    ext x',
    cases x' with x1 x2,
    split;
    { simp,
      intros y1 hy1 y2 hy2,
      exact ⟨⟨y1, hy1⟩, ⟨y2, hy2⟩⟩ } },
  { apply_instance },
  { intros, simp },
  { intro, simp }
end

lemma smooth_inv :
  smooth 𝓘(𝕜, R) 𝓘(𝕜, R) (λ (a : Rˣ), a⁻¹) :=
begin
  apply open_embedding_cont_diff_on_cont_mdiff,
  intros x hx,
  apply cont_diff_at.cont_diff_within_at,
  rw set.mem_range at hx,
  cases hx with y hy,
  rw ←hy,
  apply cont_diff_at_ring_inverse,

  ext,
  simp
end

instance : lie_group 𝓘(𝕜, R) Rˣ :=
{ smooth_mul := smooth_mul,
  smooth_inv := smooth_inv }

end units
