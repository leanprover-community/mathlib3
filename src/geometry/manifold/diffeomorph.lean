/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.times_cont_mdiff_map

/-!
# Diffeomorphisms
This file implements diffeomorphisms.

## Definitions

* `times_diffeomorph I I' M M' n`:  `n`-times continuously differentiable diffeomorphism between
                                    `M` and `M'` with respect to I and I'
* `diffeomorph  I I' M M'` : smooth diffeomorphism between `M` and `M'` with respect to I and I'

## Notations

* `M ≃ₘ^n⟮I, I'⟯ M'`  := `times_diffeomorph I J M N n`
* `M ≃ₘ⟮I, I'⟯ M'`    := `times_diffeomorph I J M N ⊤`

## Implementation notes

This notion of diffeomorphism is needed although there is already a notion of structomorphism
because structomorphisms do not allow the model spaces `H` and `H'` of the two manifolds to be
different, i.e. for a structomorphism one has to impose `H = H'` which is often not the case in
practice.

-/

open_locale manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(J : model_with_corners 𝕜 F G)

section diffeomorph

variables (M : Type*) [topological_space M] [charted_space H M]
(M' : Type*) [topological_space M'] [charted_space H' M']
(N : Type*) [topological_space N] [charted_space G N]
(n : with_top ℕ)

/--
`n`-times continuously differentiable diffeomorphism between `M` and `M'` with respect to I and I'
-/
@[protect_proj, nolint has_inhabited_instance]
structure times_diffeomorph extends M ≃ M' :=
(times_cont_mdiff_to_fun  : times_cont_mdiff I I' n to_fun)
(times_cont_mdiff_inv_fun : times_cont_mdiff I' I n inv_fun)

/-- A `diffeomorph` is just a smooth `times_diffeomorph`. -/
@[reducible] def diffeomorph := times_diffeomorph I I' M M' ⊤

infix ` ≃ₘ `:50 := times_diffeomorph _ _
localized "notation M ` ≃ₘ^ `n `⟮` I `,` J `⟯` N := times_diffeomorph I J M N n" in manifold
localized "notation M ` ≃ₘ⟮` I `,` J `⟯` N := times_diffeomorph I J M N ⊤" in manifold

namespace times_diffeomorph
instance : has_coe_to_fun (M ≃ₘ^n⟮I, I'⟯ M') := ⟨λ _, M → M', λe, e.to_equiv⟩

instance : has_coe (M ≃ₘ^n⟮I, I'⟯ M') C^n⟮I, M; I', M'⟯ := ⟨λ Φ, ⟨Φ, Φ.times_cont_mdiff_to_fun⟩⟩

protected lemma continuous (h : M ≃ₘ^n⟮I, I'⟯ M') : continuous h :=
h.times_cont_mdiff_to_fun.continuous
protected lemma times_cont_mdiff (h : M ≃ₘ^n⟮I, I'⟯ M') : times_cont_mdiff I I' n h :=
h.times_cont_mdiff_to_fun
protected lemma smooth (h : M ≃ₘ⟮I, I'⟯ M') : smooth I I' h := h.times_cont_mdiff_to_fun


lemma coe_eq_to_equiv (h : M ≃ₘ^n⟮I, I'⟯ M') (x : M) : h x = h.to_equiv x := rfl

/-- Identity map as a diffeomorphism. -/
protected def refl : M ≃ₘ^n⟮I, I⟯ M :=
{ times_cont_mdiff_to_fun := times_cont_mdiff_id,
  times_cont_mdiff_inv_fun := times_cont_mdiff_id,
  ..equiv.refl M }

/-- Composition of two diffeomorphisms. -/
protected def trans (h₁ : M ≃ₘ^n⟮I, I'⟯ M') (h₂ : M' ≃ₘ^n⟮I', J⟯ N) :
  M ≃ₘ^n⟮I, J⟯ N :=
{ times_cont_mdiff_to_fun  := h₂.times_cont_mdiff_to_fun.comp h₁.times_cont_mdiff_to_fun,
  times_cont_mdiff_inv_fun := h₁.times_cont_mdiff_inv_fun.comp h₂.times_cont_mdiff_inv_fun,
  .. equiv.trans h₁.to_equiv h₂.to_equiv }

/-- Inverse of a diffeomorphism. -/
protected def symm (h : M ≃ₘ^n⟮I, J⟯ N) : N ≃ₘ^n⟮J, I⟯ M :=
{ times_cont_mdiff_to_fun  := h.times_cont_mdiff_inv_fun,
  times_cont_mdiff_inv_fun := h.times_cont_mdiff_to_fun,
  .. h.to_equiv.symm }

end times_diffeomorph

end diffeomorph
