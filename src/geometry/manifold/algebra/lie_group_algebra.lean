/-
Copyright © 2020 Nicolò Cavalleri. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Nicolò Cavalleri.
-/

import geometry.manifold.algebra.smooth_functions
import ring_theory.derivations

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
-- declare a smooth manifold `M` over the pair `(E, H)`.
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
{M : Type*} [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

@[reducible] def vector_field_derivation := derivation 𝕜 C∞(M, I) C∞(M, I)

instance lie_ring 

variables {G : Type*} [topological_space G] [charted_space H G] [smooth_manifold_with_corners I G]
