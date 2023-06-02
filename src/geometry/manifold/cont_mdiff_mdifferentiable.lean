/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Floris van Doorn
-/
import geometry.manifold.cont_mdiff
import geometry.manifold.mdifferentiable

/-!
### Interactions between manifold-differentiability and manifold-smoothness

We give the relation between `mdifferentiable` and `cont_mdiff`.
-/

open set function filter charted_space smooth_manifold_with_corners
open_locale topology manifold

/-! ### Definition of smooth functions between manifolds -/

variables {𝕜 : Type*} [nontrivially_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
{M : Type*} [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
-- declare a smooth manifold `M'` over the pair `(E', H')`.
{E' : Type*} [normed_add_comm_group E'] [normed_space 𝕜 E']
{H' : Type*} [topological_space H'] {I' : model_with_corners 𝕜 E' H'}
{M' : Type*} [topological_space M'] [charted_space H' M'] [I's : smooth_manifold_with_corners I' M']
-- declare a smooth manifold `N` over the pair `(F, G)`.
{F : Type*} [normed_add_comm_group F] [normed_space 𝕜 F]
{G : Type*} [topological_space G] {J : model_with_corners 𝕜 F G}
{N : Type*} [topological_space N] [charted_space G N] [Js : smooth_manifold_with_corners J N]
-- declare a smooth manifold `N'` over the pair `(F', G')`.
{F' : Type*} [normed_add_comm_group F'] [normed_space 𝕜 F']
{G' : Type*} [topological_space G'] {J' : model_with_corners 𝕜 F' G'}
{N' : Type*} [topological_space N'] [charted_space G' N'] [J's : smooth_manifold_with_corners J' N']
-- declare some additional normed spaces, used for fibers of vector bundles
{F₁ : Type*} [normed_add_comm_group F₁] [normed_space 𝕜 F₁]
{F₂ : Type*} [normed_add_comm_group F₂] [normed_space 𝕜 F₂]
-- declare functions, sets, points and smoothness indices
{f f₁ : M → M'} {s s₁ t : set M} {x : M} {m n : ℕ∞}

/-! ### Deducing differentiability from smoothness -/

lemma cont_mdiff_within_at.mdifferentiable_within_at
  (hf : cont_mdiff_within_at I I' n f s x) (hn : 1 ≤ n) :
  mdifferentiable_within_at I I' f s x :=
begin
  suffices h : mdifferentiable_within_at I I' f (s ∩ (f ⁻¹' (ext_chart_at I' (f x)).source)) x,
  { rwa mdifferentiable_within_at_inter' at h,
    apply (hf.1).preimage_mem_nhds_within,
    exact ext_chart_at_source_mem_nhds I' (f x) },
  rw mdifferentiable_within_at_iff,
  exact ⟨hf.1.mono (inter_subset_left _ _),
    (hf.2.differentiable_within_at hn).mono (by mfld_set_tac)⟩,
end

lemma cont_mdiff_at.mdifferentiable_at (hf : cont_mdiff_at I I' n f x) (hn : 1 ≤ n) :
  mdifferentiable_at I I' f x :=
mdifferentiable_within_at_univ.1 $ cont_mdiff_within_at.mdifferentiable_within_at hf hn

lemma cont_mdiff_on.mdifferentiable_on (hf : cont_mdiff_on I I' n f s) (hn : 1 ≤ n) :
  mdifferentiable_on I I' f s :=
λ x hx, (hf x hx).mdifferentiable_within_at hn

lemma cont_mdiff.mdifferentiable (hf : cont_mdiff I I' n f) (hn : 1 ≤ n) :
  mdifferentiable I I' f :=
λ x, (hf x).mdifferentiable_at hn

lemma smooth_within_at.mdifferentiable_within_at
  (hf : smooth_within_at I I' f s x) : mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_within_at le_top

lemma smooth_at.mdifferentiable_at (hf : smooth_at I I' f x) : mdifferentiable_at I I' f x :=
hf.mdifferentiable_at le_top

lemma smooth_on.mdifferentiable_on (hf : smooth_on I I' f s) : mdifferentiable_on I I' f s :=
hf.mdifferentiable_on le_top

lemma smooth.mdifferentiable (hf : smooth I I' f) : mdifferentiable I I' f :=
cont_mdiff.mdifferentiable hf le_top

lemma smooth.mdifferentiable_at (hf : smooth I I' f) : mdifferentiable_at I I' f x :=
hf.mdifferentiable x

lemma smooth.mdifferentiable_within_at (hf : smooth I I' f) :
  mdifferentiable_within_at I I' f s x :=
hf.mdifferentiable_at.mdifferentiable_within_at
