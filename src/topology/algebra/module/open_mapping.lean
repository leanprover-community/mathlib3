import topology.algebra.module.finite_dimension

/-!
-/

open function filter
open_locale topological_space

namespace continuous_linear_map

variables {R : Type*} {S : Type*} [semiring R] [semiring S] (σ : R →+* S)
  (M : Type*) [topological_space M] [add_comm_monoid M]
  (M₂ : Type*) [topological_space M₂] [add_comm_monoid M₂]
  [module R M] [module S M₂]

class open_mapping_class : Prop :=
(clm_is_open_map : ∀ f : M →SL[σ] M₂, surjective f → is_open_map f)

lemma open_mapping_class.of_right_inverse {R : Type*} {S : Type*} [semiring R] [semiring S]
  {σ : R →+* S} {M : Type*} [topological_space M] [add_comm_monoid M] [has_continuous_add M]
  {M₂ : Type*} [topological_space M₂] [add_comm_group M₂] [topological_add_group M₂]
  [module R M] [module S M₂]
  (h : ∀ f : M →SL[σ] M₂, surjective f →
    ∃ g : M₂ → M, right_inverse g f ∧ continuous_at g 0 ∧ g 0 = 0) :
  open_mapping_class σ M M₂ :=
begin
  refine ⟨λ f hf, is_open_map.of_sections $ λ x, _⟩,
  rcases h f hf with ⟨g, hgf, hgc, hg₀⟩,
  refine ⟨λ y, g (y - f x) + x, _, _, λ y, _⟩,
  { have H : tendsto (λ y, y - f x) (𝓝 (f x)) (𝓝 0),
      from (continuous_id.sub continuous_const).tendsto' _ _ (sub_self _),
    simpa only [continuous_at, zero_add, sub_self] using (hgc.tendsto.comp H).add_const x },
  { rw [sub_self, hg₀, zero_add] },
  { simp only [map_add, hgf _, sub_add_cancel] }
end

/-- A continuous linear map with finite dimensional codomain is an open map. -/
@[priority 100]
instance open_mapping_class.of_finite_dimensional
  {𝕜 E F : Type*} [nontrivially_normed_field 𝕜] [complete_space 𝕜]
  [add_comm_group E] [topological_space E] [topological_add_group E]
  [module 𝕜 E] [has_continuous_smul 𝕜 E]
  [add_comm_group F] [topological_space F] [topological_add_group F] [t2_space F]
  [module 𝕜 F] [has_continuous_smul 𝕜 F] [finite_dimensional 𝕜 F] :
  open_mapping_class (ring_hom.id 𝕜) E F :=
open_mapping_class.of_right_inverse $ λ f hf,
  let ⟨g, hg⟩ := f.to_linear_map.exists_right_inverse_of_surjective (linear_map.range_eq_top.2 hf)
  in ⟨g, fun_like.congr_fun hg, g.continuous_of_finite_dimensional.continuous_at, map_zero g⟩

variables {σ M M₂} [open_mapping_class σ M M₂] (f : M →SL[σ] M₂)

protected lemma is_open_map (hf : surjective f) : is_open_map f :=
open_mapping_class.clm_is_open_map f hf

protected lemma quotient_map (hf : surjective f) : quotient_map f :=
(f.is_open_map hf).to_quotient_map f.continuous hf

lemma interior_preimage (hsurj : surjective f) (s : set M₂) :
  interior (f ⁻¹' s) = f ⁻¹' (interior s) :=
((f.is_open_map hsurj).preimage_interior_eq_interior_preimage f.continuous s).symm

lemma closure_preimage (hsurj : surjective f) (s : set M₂) :
  closure (f ⁻¹' s) = f ⁻¹' (closure s) :=
((f.is_open_map hsurj).preimage_closure_eq_closure_preimage f.continuous s).symm

lemma frontier_preimage (hsurj : surjective f) (s : set M₂) :
  frontier (f ⁻¹' s) = f ⁻¹' (frontier s) :=
((f.is_open_map hsurj).preimage_frontier_eq_frontier_preimage f.continuous s).symm

end continuous_linear_map
