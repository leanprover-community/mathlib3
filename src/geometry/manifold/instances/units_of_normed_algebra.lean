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

set_option trace.simplify.rewrite true

lemma charted_space_is_open_map_target_mem_nhds
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M]
  (hI : is_open_map I) (x: M) :
  (ext_chart_at I x).target ∈ nhds ((ext_chart_at I x) x) :=
begin
  rw mem_nhds_iff,
  have := ext_chart_at_target_mem_nhds_within I x,
  rw mem_nhds_within at this,
  rcases this with ⟨u, hu1, hu2, hu3⟩,
  existsi u ∩ set.range ⇑I,
  existsi hu3,
  refine ⟨is_open.inter hu1 hI.is_open_range, _⟩,
  refine ⟨hu2, _⟩,
  apply set.mem_of_subset_of_mem (ext_chart_at_target_subset_range I x),
  apply local_equiv.map_source,
  apply mem_ext_chart_source
end

lemma open_embedding_cont_diff_on_cont_mdiff
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {M' : Type*} [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
  {n : with_top ℕ} {f : E → E'} {g : M → M'}
  (hI : is_open_map I) (hI' : ∀ x : M', (ext_chart_at I' x).source = set.univ)
  (hf : ∀ x : M, cont_diff_on 𝕜 n f (ext_chart_at I x).target)
  (hfg : ∀ x y, f ∘ (ext_chart_at I x) = (ext_chart_at I' y) ∘ g ) :
  cont_mdiff I I' n g :=
begin
  rw cont_mdiff_iff,
  split,
  { rw continuous_iff_continuous_at,
    intro,
    have : g = (ext_chart_at I' (g x)).symm ∘ f ∘ ext_chart_at I x,
    { ext x',
      rw function.comp_app,
      rw local_equiv.eq_symm_apply,
      { rw hfg },
      { rw hI',
        apply set.mem_univ },
      { rw hfg,
        rw function.comp_app,
        apply local_equiv.map_source,
        rw hI',
        apply set.mem_univ } },
    rw this,
    apply continuous_at.comp,
    { rw hfg,
      rw function.comp_app,
      apply ext_chart_continuous_at_symm },
    apply continuous_at.comp,
    { apply continuous_on.continuous_at (cont_diff_on.continuous_on (hf x)),
      apply charted_space_is_open_map_target_mem_nhds hI },
    { apply ext_chart_at_continuous_at } },
  { intros,
    apply cont_diff_on.congr_mono (hf x),
    { intros a ha,
      rw ←function.comp.assoc,
      rw function.comp_app,
      rw ←hfg x y,
      rw function.comp_app,
      congr,
      apply local_equiv.right_inv,
      exact ha.1 },
    apply set.inter_subset_left }
end


/-- A weaker version of `units.open_embedding_cont_diff_on_cont_mdiff` in which the model space H
coincides with the model vector space E via `model_with_corners_self`. -/
lemma open_embedding_cont_diff_on_cont_mdiff'
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {M : Type*} [topological_space M] [nonempty M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {M' : Type*} [topological_space M'] [nonempty M']
  {n : with_top ℕ} {f : E → E'} {g : M → M'}
  (e : M → E) (he : open_embedding e)
  (e' : M' → E') (he' : open_embedding e')
  (hf : cont_diff_on 𝕜 n f (set.range e))
  (hfg : f ∘ e = e' ∘ g) :
  @cont_mdiff _ _ _ _ _ _ _ 𝓘(𝕜, E) _ _ he.singleton_charted_space
    _ _ _ _ _ 𝓘(𝕜, E') _ _ he'.singleton_charted_space n g :=
begin
  haveI := he.singleton_smooth_manifold_with_corners 𝓘(𝕜, E),
  haveI := he'.singleton_smooth_manifold_with_corners 𝓘(𝕜, E'),
  apply open_embedding_cont_diff_on_cont_mdiff,
  show E → E', exact f,
  { rw model_with_corners_self_coe;
    apply is_open_map.id },
  { intro,
    simp },
  { intro,
    simp [hf] },
  { intros,
    ext,
    simp [hfg] }
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
  apply open_embedding_cont_diff_on_cont_mdiff,
  { apply is_open_map.prod;
    rw model_with_corners_self_coe;
    apply is_open_map.id },
  { simp },
  { intro,
    exact cont_diff.cont_diff_on cont_diff_mul },
  { intros,
    ext,
    simp }
end

lemma smooth_inv :
  smooth 𝓘(𝕜, R) 𝓘(𝕜, R) (λ (a : Rˣ), a⁻¹) :=
begin
  apply open_embedding_cont_diff_on_cont_mdiff',
  { intros x hx,
    apply cont_diff_at.cont_diff_within_at,
    rw set.mem_range at hx,
    cases hx with y hy,
    rw ←hy,
    apply cont_diff_at_ring_inverse },
  ext,
  simp
end

instance : lie_group 𝓘(𝕜, R) Rˣ :=
{ smooth_mul := smooth_mul,
  smooth_inv := smooth_inv }

end units
