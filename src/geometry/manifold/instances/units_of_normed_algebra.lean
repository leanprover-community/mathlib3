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

/-- If the `model_with_corners` `I` is an open map, then the target of the extended chart at any
point on a manifold modelled on `I` is a `nhds`, rather than just a `nhds_within`. -/
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

/-- The continuous differentiability of a map `g : M → M'` between manifolds can be stated in terms
of the continuous differentiability of a corresponding map `f : E → E'` between the model vector
spaces, if one assumes that the `model_with_corners` for `M` is an open map and the
`model_with_corners` for `M'` consists of a single chart.

TODO: How can the assumptions be relaxed? -/
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
  (hfg : ∀ x y, f ∘ (ext_chart_at I x) = (ext_chart_at I' y) ∘ g) :
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
coincides with the model vector space E via `model_with_corners_self`, and the charts are given by
open embeddings via `open_embedding.singleton_charted_space`. -/
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

lemma open_embedding.to_local_homeomorph_left_inv
 {α : Type*} {β : Type*} [topological_space α] [topological_space β]
 (f : α → β) (h : open_embedding f) [nonempty α] {x : α} :
 (open_embedding.to_local_homeomorph f h).symm (f x) = x :=
begin
  rw ←congr_fun (open_embedding.to_local_homeomorph_apply f h),
  rw local_homeomorph.left_inv,
  rw open_embedding.to_local_homeomorph_source,
  apply set.mem_univ
end

lemma open_embedding.to_local_homeomorph_right_inv
 {α : Type*} {β : Type*} [topological_space α] [topological_space β]
 (f : α → β) (h : open_embedding f) [nonempty α] {x : β} (hx : x ∈ set.range f) :
 f ((open_embedding.to_local_homeomorph f h).symm x) = x :=
begin
  rw ←congr_fun (open_embedding.to_local_homeomorph_apply f h),
  rw local_homeomorph.right_inv,
  rw open_embedding.to_local_homeomorph_target,
  exact hx
end

set_option trace.simplify.rewrite true
lemma cont_mdiff_open_embedding
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M] [nonempty M]
  {e : M → H} (h : open_embedding e) {n : with_top ℕ} :
  @cont_mdiff _ _ _ _ _ _ _ I _ _ h.singleton_charted_space _ _ _ _ _ I _ _ _ n e :=
begin
  haveI := h.singleton_smooth_manifold_with_corners I,
  rw cont_mdiff_iff,
  split,
  { apply h.continuous },
  intros,
  apply cont_diff_on.congr cont_diff_on_id,
  intros z hz,
  rw ext_chart_at_coe,
  rw ext_chart_at_coe_symm,
  rw chart_at_self_eq,
  repeat {rw function.comp_app},
  rw local_homeomorph.refl_apply,
  rw id.def,
  rw local_homeomorph.singleton_charted_space_chart_at_eq,
  rw open_embedding.to_local_homeomorph_right_inv e,
  { rw model_with_corners.right_inv,
    { refl },
    apply set.mem_of_subset_of_mem _ hz.1,
    apply ext_chart_at_target_subset_range },
  rw model_with_corners.symm,
  rw ←set.mem_preimage,
  have := hz.1,
  rw ext_chart_at at this,
  rw local_equiv.trans_target at this,
  have := this.2,
  revert this,
  apply set.mem_of_subset_of_mem,
  apply set.preimage_mono,
  rw local_homeomorph.singleton_charted_space_chart_at_eq,
  rw open_embedding.to_local_homeomorph_target
end
-- z ∈ ⇑(I.to_local_equiv.symm) ⁻¹' (chart_at H x).to_local_equiv.target
/- Generalise this to all local homeomorphs? -/
lemma cont_mdiff_on_open_embedding_symm
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M] [nonempty M]
  {e : M → H} (h : open_embedding e) {n : with_top ℕ} :
  @cont_mdiff_on _ _ _ _ _ _ _ I _ _ _ _ _ _ _ _ I _ _ h.singleton_charted_space
    n (open_embedding.to_local_homeomorph e h).symm (set.range e) :=
begin
  haveI := h.singleton_smooth_manifold_with_corners I,
  rw cont_mdiff_on_iff,
  split,
  { rw ←open_embedding.to_local_homeomorph_target,
    apply local_homeomorph.continuous_on_symm (open_embedding.to_local_homeomorph e h) },
  intros,
  apply cont_diff_on.congr cont_diff_on_id,
  intros z hz,
  rw ext_chart_at_coe,
  rw ext_chart_at_coe_symm,
  rw chart_at_self_eq,
  repeat {rw function.comp_app},
  rw local_homeomorph.refl_symm,
  rw local_homeomorph.refl_apply,
  rw id.def,
  rw local_homeomorph.singleton_charted_space_chart_at_eq,
  rw local_homeomorph.right_inv,
  { rw model_with_corners.right_inv,
    { refl },
    apply set.mem_of_subset_of_mem _ hz.1,
    apply ext_chart_at_target_subset_range },
  rw open_embedding.to_local_homeomorph_target,
  rw model_with_corners.symm,
  rw ←set.mem_preimage,
  have := hz.2,
  rw set.preimage_inter at this,
  exact this.1
end

lemma cont_mdiff.of_comp_open_embedding
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
  {M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {M' : Type*} [topological_space M'] [nonempty M']
  {e' : M' → H'} (h : open_embedding e') {n : with_top ℕ}
  {f : M → M'} (hf : cont_mdiff I I' n (e' ∘ f)) :
  @cont_mdiff _ _ _ _ _ _ _ I _ _ _ _ _ _ _ _ I' _ _ h.singleton_charted_space n f :=
begin
  have : f = (open_embedding.to_local_homeomorph e' h).symm ∘ e' ∘ f,
  { ext,
    rw function.comp_app,
    rw function.comp_app,
    rw open_embedding.to_local_homeomorph_left_inv },
  rw this,
  apply cont_mdiff_on.comp_cont_mdiff _ hf,
  show set H',
  { exact set.range e' },
  { intros,
    simp },
  exact cont_mdiff_on_open_embedding_symm I' h,
end

/-

Strategy:

E --f--> E'
↑        ↑
I        I'
|        |
H        H'
↑        ↑
e        e'
|        |
M --g--> M'

1. If e' : M' → H' is an open embedding, then e' is cont_mdiff as a manifold map, where the charted
  space on M' is induced by e', and the charted space on H' is given by charted_space_self.
2. For g : M → M', if the charted space on M' is induced by an open embedding e' : M' → H', and
  (e' ∘ g) : M → H' is cont_mdiff, then g is cont_mdiff.
3. If there exists f : E → E' such that f ∘ e = e' ∘ g on M, where e is an open embedding that
  induces a charted space on M (or coincides with its charted space), and f is cont_diff (therefore
  cont_mdiff), then g is cont_mdiff.
*. Let's prove it for open_embedding.singleton_charted_space first, prove smooth_inv, and then see
  how to generalise for smooth_mul.

R  ×  R
↑     ↑
I  ×  I (self × self)
|     |
R     R (prod)
↑     ↑
e     e (coe, open embedding)
|     |
Rˣ ×  Rˣ

-/




namespace units

variables {R : Type*} [normed_ring R] [complete_space R]

instance : charted_space R Rˣ := open_embedding_coe.singleton_charted_space

lemma chart_at_apply {a : Rˣ} {b : Rˣ} : chart_at R a b = b := rfl
lemma chart_at_source {a : Rˣ} : (chart_at R a).source = set.univ := rfl

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [normed_algebra 𝕜 R]

instance : smooth_manifold_with_corners 𝓘(𝕜, R) Rˣ :=
open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(𝕜, R)



-- /-- Multiplication of units of a complete normed ring is a smooth map between manifolds. -/
-- lemma smooth_mul :
--   smooth (𝓘(𝕜, R).prod 𝓘(𝕜, R)) 𝓘(𝕜, R) (λ (p : Rˣ × Rˣ), p.fst * p.snd) :=
-- begin
--   apply open_embedding_cont_diff_on_cont_mdiff,
--   { apply is_open_map.prod;
--     rw model_with_corners_self_coe;
--     apply is_open_map.id },
--   { simp },
--   { intro,
--     exact cont_diff.cont_diff_on cont_diff_mul },
--   { intros,
--     ext,
--     simp }
-- end

-- /-- Inversion of units of a complete normed ring is a smooth map between manifolds. -/
-- lemma smooth_inv :
--   smooth 𝓘(𝕜, R) 𝓘(𝕜, R) (λ (a : Rˣ), a⁻¹) :=
-- begin
--   apply open_embedding_cont_diff_on_cont_mdiff',
--   { intros x hx,
--     apply cont_diff_at.cont_diff_within_at,
--     rw set.mem_range at hx,
--     cases hx with y hy,
--     rw ←hy,
--     apply cont_diff_at_ring_inverse },
--   ext,
--   simp
-- end

-- /-- The units of a complete normed ring form a Lie group. -/
-- instance : lie_group 𝓘(𝕜, R) Rˣ :=
-- { smooth_mul := smooth_mul,
--   smooth_inv := smooth_inv }

end units
