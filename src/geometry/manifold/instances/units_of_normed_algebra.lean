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
  intros, -- show the function is actually the identity on the range of I ∘ e
  apply cont_diff_on.congr cont_diff_on_id,
  intros z hz, -- factorise into the chart (=e) and the model (=id)
  rw [ext_chart_at_coe, ext_chart_at_coe_symm, chart_at_self_eq],
  repeat {rw function.comp_app},
  rw [local_homeomorph.refl_apply, id.def, local_homeomorph.singleton_charted_space_chart_at_eq,
    open_embedding.to_local_homeomorph_right_inv e],
  { rw model_with_corners.right_inv,
    { refl },
    apply set.mem_of_subset_of_mem _ hz.1,
    apply ext_chart_at_target_subset_range },
  rw model_with_corners.symm, -- show hz implies z is in range of I ∘ e
  have := hz.1,
  rw [ext_chart_at, local_equiv.trans_target] at this,
  have := this.2,
  rw [set.mem_preimage, local_homeomorph.singleton_charted_space_chart_at_eq,
    open_embedding.to_local_homeomorph_target] at this,
  exact this
end

lemma cont_mdiff_on_open_embedding_symm
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
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
  intros, -- show the function is actually the identity on the range of I ∘ e
  apply cont_diff_on.congr cont_diff_on_id,
  intros z hz, -- factorise into the chart (=e) and the model (=id)
  rw [ext_chart_at_coe, ext_chart_at_coe_symm, chart_at_self_eq],
  repeat {rw function.comp_app},
  rw [local_homeomorph.refl_symm, local_homeomorph.refl_apply, id.def,
    local_homeomorph.singleton_charted_space_chart_at_eq, local_homeomorph.right_inv],
  { rw model_with_corners.right_inv,
    { refl },
    apply set.mem_of_subset_of_mem _ hz.1,
    apply ext_chart_at_target_subset_range }, -- show hz implies z is in range of I ∘ e
  rw [open_embedding.to_local_homeomorph_target, model_with_corners.symm, ←set.mem_preimage],
  have := hz.2,
  rw [set.preimage_inter] at this,
  exact this.1
end

lemma cont_mdiff.of_comp_open_embedding
  {𝕜 : Type*} [nontrivially_normed_field 𝕜]
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M]
  {E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
  {H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
  {M' : Type*} [topological_space M'] [nonempty M']
  {e' : M' → H'} (h : open_embedding e') {n : with_top ℕ}
  {f : M → M'} (hf : cont_mdiff I I' n (e' ∘ f)) :
  @cont_mdiff _ _ _ _ _ _ _ I _ _ _ _ _ _ _ _ I' _ _ h.singleton_charted_space n f :=
begin
  have : f = (open_embedding.to_local_homeomorph e' h).symm ∘ e' ∘ f,
  { ext,
    rw [function.comp_app, function.comp_app, open_embedding.to_local_homeomorph_left_inv] },
  rw this,
  apply cont_mdiff_on.comp_cont_mdiff _ hf,
  show set H',
  { exact set.range e' },
  { intros,
    simp },
  exact cont_mdiff_on_open_embedding_symm h
end

namespace units

variables {R : Type*} [normed_ring R] [complete_space R]

instance : charted_space R Rˣ := open_embedding_coe.singleton_charted_space

lemma chart_at_apply {a : Rˣ} {b : Rˣ} : chart_at R a b = b := rfl
lemma chart_at_source {a : Rˣ} : (chart_at R a).source = set.univ := rfl

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜] [normed_algebra 𝕜 R]

instance : smooth_manifold_with_corners 𝓘(𝕜, R) Rˣ :=
open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(𝕜, R)

lemma cont_mdiff_coe {m : with_top ℕ} : cont_mdiff 𝓘(𝕜, R) 𝓘(𝕜, R) m (coe : Rˣ → R) :=
cont_mdiff_open_embedding 𝓘(𝕜, R) units.open_embedding_coe

/-- Multiplication of units of a complete normed ring is a smooth map between manifolds.

It suffices to show that `coe ∘ mul : Rˣ × Rˣ → R` is smooth. This function is equal to the usual
ring multiplication composed with the embedding from `Rˣ × Rˣ` to `R × R`, and we know each of these
factors is smooth. -/
lemma smooth_mul :
  smooth (𝓘(𝕜, R).prod 𝓘(𝕜, R)) 𝓘(𝕜, R) (λ (p : Rˣ × Rˣ), p.fst * p.snd) :=
begin
  apply cont_mdiff.of_comp_open_embedding,
  have : (coe : Rˣ → R) ∘ (λ x : Rˣ × Rˣ, x.1 * x.2) =
    (λ x : R × R, x.1 * x.2) ∘ (λ x : Rˣ × Rˣ, (x.1, x.2)),
  { ext, simp },
  rw this,
  have : cont_mdiff (𝓘(𝕜, R).prod 𝓘(𝕜, R)) (𝓘(𝕜, R × R))
    ⊤ (λ x : Rˣ × Rˣ, ((x.1 : R), (x.2 : R))) :=
    cont_mdiff.prod_mk_space
      (cont_mdiff.comp cont_mdiff_coe cont_mdiff_fst)
      (cont_mdiff.comp cont_mdiff_coe cont_mdiff_snd),
  apply cont_mdiff.comp _ this,
  rw cont_mdiff_iff_cont_diff,
  apply cont_diff_mul
end

/-- Inversion of units of a complete normed ring is a smooth map between manifolds.

It suffices to show that `coe ∘ inv : Rˣ → R` is smooth. This function is equal to the composition
`ring.inverse ∘ coe`, and we know each of these factors is smooth. -/
lemma smooth_inv :
  smooth 𝓘(𝕜, R) 𝓘(𝕜, R) (λ (a : Rˣ), a⁻¹) :=
begin
  apply cont_mdiff.of_comp_open_embedding,
  have : (coe : Rˣ → R) ∘ (λ x : Rˣ, x⁻¹) = ring.inverse ∘ coe,
  { ext, simp },
  rw [this, cont_mdiff],
  intro,
  have : cont_mdiff 𝓘(𝕜, R) 𝓘(𝕜, R) ⊤ (coe : Rˣ → R) := cont_mdiff_coe,
  rw cont_mdiff at this,
  apply cont_mdiff_at.comp x _ (this x),
  rw cont_mdiff_at_iff_cont_diff_at,
  apply cont_diff_at_ring_inverse
end

/-- The units of a complete normed ring form a Lie group. -/
instance : lie_group 𝓘(𝕜, R) Rˣ :=
{ smooth_mul := smooth_mul,
  smooth_inv := smooth_inv }

end units
