import geometry.manifold.smooth_map

variables {𝕜 : Type*} [nondiscrete_normed_field 𝕜]
{E : Type*} [normed_group E] [normed_space 𝕜 E]
{E' : Type*} [normed_group E'] [normed_space 𝕜 E']
{F : Type*} [normed_group F] [normed_space 𝕜 F]
{F' : Type*} [normed_group F'] [normed_space 𝕜 F']
{H : Type*} [topological_space H]
{H' : Type*} [topological_space H']
{G : Type*} [topological_space G]
{G' : Type*} [topological_space G']
(I : model_with_corners 𝕜 E H) (I' : model_with_corners 𝕜 E' H')
(J : model_with_corners 𝕜 F G) (J' : model_with_corners 𝕜 F' G')

section diffeomorph

variables (M : Type*) [topological_space M] [charted_space H M] [smooth_manifold_with_corners I M]
(M' : Type*) [topological_space M'] [charted_space H' M'] [smooth_manifold_with_corners I' M']
(N : Type*) [topological_space N] [charted_space G N] [smooth_manifold_with_corners J N]
(N' : Type*) [topological_space N'] [charted_space G' N'] [smooth_manifold_with_corners J' N']
(n : with_top ℕ)

/-- α and β are homeomorph, also called topological isomoph -/
structure times_diffeomorph extends M ≃ M' :=
(times_cont_mdiff_to_fun  : times_cont_mdiff I I' n to_fun)
(times_cont_mdiff_inv_fun : times_cont_mdiff I' I n inv_fun)

@[reducible] def diffeomorph := times_diffeomorph I I' M M' ⊤

infix ` ≃ₘ `:50 := times_diffeomorph _ _
notation M ` ≃ₘ[ `n `](` I `|` J `)` N := times_diffeomorph I J M N n
notation M ` ≃ₘ[`:50 I `;`:50 J `]` N := diffeomorph I J M N

namespace times_diffeomorph
instance : has_coe_to_fun (times_diffeomorph I I' M M' n) := ⟨λ _, M → M', λe, e.to_equiv⟩

lemma coe_eq_to_equiv (h : times_diffeomorph I I' M M' n) (x : M) : h x = h.to_equiv x := rfl

/-- Identity map is a diffeomorphism. -/
protected def refl : M ≃ₘ[n](I|I) M :=
{ times_cont_mdiff_to_fun := times_cont_mdiff_id,
  times_cont_mdiff_inv_fun := times_cont_mdiff_id,
  ..equiv.refl M }

/-- Composition of two diffeomorphisms. -/
protected def trans (h₁ : times_diffeomorph I I' M M' n) (h₂ : times_diffeomorph I' J M' N n) :
  M ≃ₘ[n](I|J) N :=
{ times_cont_mdiff_to_fun  := h₂.times_cont_mdiff_to_fun.comp h₁.times_cont_mdiff_to_fun,
  times_cont_mdiff_inv_fun := h₁.times_cont_mdiff_inv_fun.comp h₂.times_cont_mdiff_inv_fun,
  .. equiv.trans h₁.to_equiv h₂.to_equiv }

/-- Inverse of a diffeomorphism. -/
protected def symm (h : M ≃ₘ[n](I|J) N) : N ≃ₘ[n](J|I) M :=
{ times_cont_mdiff_to_fun  := h.times_cont_mdiff_inv_fun,
  times_cont_mdiff_inv_fun := h.times_cont_mdiff_to_fun,
  .. h.to_equiv.symm }

end times_diffeomorph

end diffeomorph
