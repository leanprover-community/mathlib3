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
  apply cont_mdiff.smooth,
  rw cont_mdiff_iff,
  split,
  { continuity },
  { intros x' y',
    simp,
    have : ∀ x : R × R, x ∈ set.range (coe : Rˣ → R) ×ˢ set.range (coe : Rˣ → R) → (coe ∘
      (λ (p : Rˣ × Rˣ), p.1 * p.2) ∘ λ (p : R × R),
        ((open_embedding.to_local_homeomorph coe open_embedding_coe).symm p.1,
          (open_embedding.to_local_homeomorph coe open_embedding_coe).symm p.2)) x =
      (λ (p : R × R), p.1 * p.2) x,
    { rintro x hx,
      rw [function.comp_app, function.comp_app, coe_mul],
      dsimp,
      rw set.mem_prod at hx,
      cases hx with hx1 hx2,
      cases hx1 with y1 hy1,
      cases hx2 with y2 hy2,
      rw [←hy1, ←hy2],
      unfold open_embedding.to_local_homeomorph
        local_homeomorph.of_continuous_open
        local_homeomorph.of_continuous_open_restrict,
      rw local_homeomorph.mk_coe_symm,
      simp,
      have : ∀ y : Rˣ, ∃ (a : Rˣ) (H : a ∈ (set.univ : set Rˣ)), (a : R) = (y : R) :=
        λ y : Rˣ, ⟨y, ⟨set.mem_univ y, rfl⟩⟩,
      rw @function.inv_fun_on_eq Rˣ R _ set.univ coe y1 (this y1),
      rw @function.inv_fun_on_eq Rˣ R _ set.univ coe y2 (this y2) },
    apply cont_diff_on.congr _ this,
    exact cont_diff.cont_diff_on (@cont_diff_mul 𝕜 _ ⊤ R _ _) }
end

lemma smooth_inv :
  smooth 𝓘(𝕜, R) 𝓘(𝕜, R) (λ (a : Rˣ), a⁻¹) :=
begin
  apply cont_mdiff.smooth,
  rw cont_mdiff_iff,
  split,
  { continuity },
  { intros x' y',
    simp,
    have : ∀ x : R, x ∈ set.range (coe : Rˣ → R) →
      (coe ∘ has_inv.inv ∘
        (open_embedding.to_local_homeomorph coe open_embedding_coe).symm) x =
        ring.inverse x,
    { intros x hx,
      cases hx with y hy,
      rw ←hy,
      simp,
      unfold open_embedding.to_local_homeomorph
        local_homeomorph.of_continuous_open
        local_homeomorph.of_continuous_open_restrict,
      rw local_homeomorph.mk_coe_symm,
      simp,
      have : ∃ (a : Rˣ) (H : a ∈ (set.univ : set Rˣ)), (a : R) = (y : R) :=
        ⟨y, ⟨set.mem_univ y, rfl⟩⟩,
      rw inv_unique,
      rw @function.inv_fun_on_eq Rˣ R _ set.univ coe y this },
    apply cont_diff_on.congr _ this,
    intros x hx,
    cases hx with y hy,
    rw ←hy,
    exact cont_diff_at.cont_diff_within_at (@cont_diff_at_ring_inverse 𝕜 _ ⊤ R _ _ _ y) }
end

instance : lie_group 𝓘(𝕜, R) Rˣ :=
{ smooth_mul := smooth_mul,
  smooth_inv := smooth_inv }

end units
