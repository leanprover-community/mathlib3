/-
Copyright © 2021 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nicolò Cavalleri, Heather Macbeth, Winston Yin
-/

import geometry.manifold.smooth_manifold_with_corners
import geometry.manifold.algebra.lie_group
import analysis.normed_space.units

/-!
# Units of a normed algebra

We construct the Lie group structure on the group of units of a complete normed `𝕜`-algebra `R`. The
group of units `Rˣ` has a natural smooth manifold structure modelled on `R` given by its embedding
into `R`. Together with the smoothness of the multiplication and inverse of its elements, `Rˣ` forms
a Lie group.

An important special case of this construction is the general linear group.  For a normed space `V`
over a field `𝕜`, the `𝕜`-linear endomorphisms of `V` are a normed `𝕜`-algebra (see
`continuous_linear_map.to_normed_algebra`), so this construction provides a Lie group structure on
its group of units, the general linear group GL(`𝕜`, `V`), as demonstrated by:
```
example {V : Type*} [normed_add_comm_group V] [normed_space 𝕜 V] [complete_space V] [nontrivial V] :
  lie_group 𝓘(𝕜, V →L[𝕜] V) (V →L[𝕜] V)ˣ :=
by apply_instance
```
-/

noncomputable theory

open_locale manifold

/-- Let `M'` be a manifold whose chart structure is given by an open embedding `e'` into its model
space `H'`. Then the smoothness of `e' ∘ f : M → H'` implies the smoothness of `f`.

This is useful, for example, when `e' ∘ f = g ∘ e` for smooth maps `e : M → X` and `g : X → H'`. -/
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

/-- For any map `f` from a manifold `M` to the units `Rˣ` of a complete normed ring `R`, the
smoothness of `coe ∘ f`, where `coe : Rˣ → R` is the embedding, implies the smoothness of `f`.

This can be used to show that ring multiplication `Rˣ × Rˣ → Rˣ` and inverse `Rˣ → Rˣ` are
smooth. -/
lemma cont_mdiff.of_comp_units_coe
  {E : Type*} [normed_add_comm_group E] [normed_space 𝕜 E]
  {H : Type*} [topological_space H] {I : model_with_corners 𝕜 E H}
  {M : Type*} [topological_space M] [charted_space H M]
  {n : with_top ℕ}
  {f : M → Rˣ} (hf : cont_mdiff I 𝓘(𝕜, R) n ((coe : Rˣ → R) ∘ f)) :
  cont_mdiff I 𝓘(𝕜, R) n f :=
cont_mdiff.of_comp_open_embedding units.open_embedding_coe hf

/-- The units of a complete normed ring form a Lie group. -/
instance : lie_group 𝓘(𝕜, R) Rˣ :=
{ smooth_mul :=
  begin
    apply cont_mdiff.of_comp_units_coe,
    have : (coe : Rˣ → R) ∘ (λ x : Rˣ × Rˣ, x.1 * x.2) =
      (λ x : R × R, x.1 * x.2) ∘ (λ x : Rˣ × Rˣ, (x.1, x.2)),
    { ext, simp },
    rw this,
    have : cont_mdiff (𝓘(𝕜, R).prod 𝓘(𝕜, R)) (𝓘(𝕜, R × R))
      ∞ (λ x : Rˣ × Rˣ, ((x.1 : R), (x.2 : R))) :=
      cont_mdiff.prod_mk_space
        (cont_mdiff.comp cont_mdiff_coe cont_mdiff_fst)
        (cont_mdiff.comp cont_mdiff_coe cont_mdiff_snd),
    refine cont_mdiff.comp _ this,
    rw cont_mdiff_iff_cont_diff,
    apply cont_diff_mul
  end,
  smooth_inv :=
  begin
    apply cont_mdiff.of_comp_units_coe,
    have : (coe : Rˣ → R) ∘ (λ x : Rˣ, x⁻¹) = ring.inverse ∘ coe,
    { ext, simp },
    rw [this, cont_mdiff],
    intro x,
    refine cont_mdiff_at.comp x _ (cont_mdiff_coe x),
    rw cont_mdiff_at_iff_cont_diff_at,
    apply cont_diff_at_ring_inverse
  end }

end units
