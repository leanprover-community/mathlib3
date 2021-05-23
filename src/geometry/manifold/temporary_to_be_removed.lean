import geometry.manifold.algebra.smooth_functions
import ring_theory.derivation

open_locale manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H] (I : model_with_corners 𝕜 E H)
(M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]

structure vector_field_derivation (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
  extends derivation 𝕜 (smooth_map I 𝓘(𝕜) M 𝕜) (smooth_map I 𝓘(𝕜) M 𝕜)
