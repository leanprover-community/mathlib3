import geometry.manifold.algebra.smooth_functions
import ring_theory.derivation

open_locale manifold

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{H : Type*} [topological_space H]

structure vector_field_derivation (I : model_with_corners 𝕜 E H)
  (M : Type*) [topological_space M] [charted_space H M] [Is : smooth_manifold_with_corners I M]
  extends derivation 𝕜 (@times_cont_mdiff_map 𝕜 _ E _ _ 𝕜 _ _ H _ 𝕜 _ I Isf(𝕜) M _ _ Is 𝕜 _ _ _ ⊤)
    (@times_cont_mdiff_map 𝕜 _ E _ _ 𝕜 _ _ H _ 𝕜 _ I Isf(𝕜) M _ _ Is 𝕜 _ _ _ ⊤)

/- Something weird is happening. Does not find the instance of smooth manifolds with corners.
Moreover if I define it as a reducible def .eval does not work... It also takes very long time to
typecheck -/
