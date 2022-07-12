import algebraic_geometry.Spec
import algebraic_geometry.prime_spectrum.basic

universe u
noncomputable theory

open topological_space
open category_theory
open Top
open function
open ring_hom
open prime_spectrum

namespace spec_of_surjective

variables {R S : CommRing} (f : R →+* S)

postfix ` ^* ` : 80 := prime_spectrum.comap

lemma comap_inducing_of_surjective (hf : surjective f) : inducing (f ^*) :=
⟨begin
    simp_rw [topological_space_eq_iff,
             ← is_closed_compl_iff,
             is_closed_induced_iff],
    intro U,
    generalize : Uᶜ = Z,
    split,
    {   rw is_closed_iff_zero_locus,
        rintro ⟨F, rfl⟩,
        use zero_locus (f ⁻¹' F),
        exact ⟨(is_closed_iff_zero_locus _).mpr ⟨f ⁻¹' F, rfl⟩,
               by rw [preimage_comap_zero_locus,
                      surjective.image_preimage hf]⟩, },
    {   rintro ⟨C, ⟨hC1, rfl⟩⟩,
        exact hC1.preimage (comap f).continuous, },
    end⟩

-- prime_spectrum.comap_injective_of_surjective,

lemma image_of_spec_of_surjective (hf : surjective f) :
    set.range (f ^*) = prime_spectrum.zero_locus (ker f) :=
begin
    ext p, rw [set.mem_range, mem_zero_locus],
    split,
    { rintro ⟨p, rfl⟩ a ha,
      simp only [ideal.mem_comap, set_like.mem_coe, comap_as_ideal],
      rw (mem_ker _).mp ha, exact zero_mem _, },
    { intro h_ker_p,
      use ideal.map f p.as_ideal,
      apply ideal.map_is_prime_of_surjective hf h_ker_p,
      ext x,
      change f x ∈ p.as_ideal.map f ↔ _,
      rw ideal.mem_map_iff_of_surjective _ hf,
      split,
      { rintros ⟨x', ⟨hx', heq⟩⟩,
        rw (by ring : x = x' + (x - x')),
        apply p.as_ideal.add_mem hx',
        apply h_ker_p ((mem_ker _).mpr _),
        rw [map_sub, heq, sub_self], },
      intro hx, exact ⟨x, hx, rfl⟩,
    },
end

lemma is_closed_spec_of_surjective (hf : surjective f) : is_closed (set.range (f ^*)) :=
    begin
        rw image_of_spec_of_surjective _ hf,
        exact is_closed_zero_locus ↑(ker f),
    end


lemma closed_embedding_of_spec_of_surjective (hf : surjective f) : closed_embedding (f ^*) :=
    begin
        split, split,
        exact comap_inducing_of_surjective f hf,
        exact comap_injective_of_surjective f hf,
        exact is_closed_spec_of_surjective f hf,
    end

end spec_of_surjective
