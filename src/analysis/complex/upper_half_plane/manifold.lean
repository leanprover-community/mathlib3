import analysis.complex.upper_half_plane.topology
import geometry.manifold.cont_mdiff_mfderiv
/-!
# Manifold structure on the upper half plane.

In this file we define the complex manifold structure on the upper half-plane.
-/

open_locale upper_half_plane manifold

namespace upper_half_plane

noncomputable instance : charted_space ℂ ℍ :=
upper_half_plane.open_embedding_coe.singleton_charted_space

instance : smooth_manifold_with_corners 𝓘(ℂ) ℍ :=
upper_half_plane.open_embedding_coe.singleton_smooth_manifold_with_corners 𝓘(ℂ)

/-- The inclusion map `ℍ → ℂ` is a smooth map of manifolds. -/
lemma smooth_coe : smooth 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) :=
λ x, cont_mdiff_at_ext_chart_at

/-- The inclusion map `ℍ → ℂ` is a differentiable map of manifolds. -/
lemma mdifferentiable_coe : mdifferentiable 𝓘(ℂ) 𝓘(ℂ) (coe : ℍ → ℂ) :=
smooth_coe.mdifferentiable

end upper_half_plane
