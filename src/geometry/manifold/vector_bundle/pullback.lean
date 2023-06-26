/-
Copyright (c) 2023 Floris van Doorn, Heather Macbeth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Heather Macbeth
-/
import geometry.manifold.cont_mdiff_map
import geometry.manifold.vector_bundle.basic

/-! # Pullbacks of smooth vector bundles

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines pullbacks of smooth vector bundles over a smooth manifold.

## Main definitions

* `smooth_vector_bundle.pullback`: For a smooth vector bundle `E` over a manifold `B` and a smooth
  map `f : B' → B`, the pullback vector bundle `f *ᵖ E` is a smooth vector bundle.

-/

open bundle set
open_locale manifold

variables {𝕜 B B' M : Type*} (F : Type*) (E : B → Type*)

variables [nontrivially_normed_field 𝕜] [∀ x, add_comm_monoid (E x)] [∀ x, module 𝕜 (E x)]
  [normed_add_comm_group F] [normed_space 𝕜 F]
  [topological_space (total_space E)] [∀ x, topological_space (E x)]

  {EB : Type*} [normed_add_comm_group EB] [normed_space 𝕜 EB]
  {HB : Type*} [topological_space HB] (IB : model_with_corners 𝕜 EB HB)
  [topological_space B] [charted_space HB B] [smooth_manifold_with_corners IB B]
  {EB' : Type*} [normed_add_comm_group EB'] [normed_space 𝕜 EB']
  {HB' : Type*} [topological_space HB'] (IB' : model_with_corners 𝕜 EB' HB')
  [topological_space B'] [charted_space HB' B'] [smooth_manifold_with_corners IB' B']
  [fiber_bundle F E] [vector_bundle 𝕜 F E] [smooth_vector_bundle F E IB]
  (f : smooth_map IB' IB B' B)

/-- For a smooth vector bundle `E` over a manifold `B` and a smooth map `f : B' → B`, the pullback
vector bundle `f *ᵖ E` is a smooth vector bundle. -/
instance smooth_vector_bundle.pullback : smooth_vector_bundle F (f *ᵖ E) IB' :=
{ smooth_on_coord_change := begin
    rintro _ _ ⟨e, he, rfl⟩ ⟨e', he', rfl⟩, resetI,
    refine ((smooth_on_coord_change e e').comp f.smooth.smooth_on
      (λ b hb, hb)).congr _,
    rintro b (hb : f b ∈ e.base_set ∩ e'.base_set), ext v,
    show ((e.pullback f).coord_changeL 𝕜 (e'.pullback f) b) v = (e.coord_changeL 𝕜 e' (f b)) v,
    rw [e.coord_changeL_apply e' hb, (e.pullback f).coord_changeL_apply' _],
    exacts [rfl, hb]
  end }
