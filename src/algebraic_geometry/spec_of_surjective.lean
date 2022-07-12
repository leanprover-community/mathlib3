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

lemma image_of_spec_of_surjective : set.range (f ^*) = prime_spectrum.zero_locus (ker f) :=
   begin
    ext x,
    split,
    { rintro ⟨p, rfl⟩ a ha,
      simp,
      -- need to use: linear_algebra.quotient.mk_eq_zero
      sorry,},

    { sorry, }
   end

lemma is_closed_spec_of_surjective : is_closed (set.range (f ^*)) :=
    begin
        rw image_of_spec_of_surjective,
        exact is_closed_zero_locus ↑(ker f),
    end


lemma closed_embedding_of_spec_of_surjective (hf : surjective f) : closed_embedding (f ^*) :=
    begin
        split, split,
        exact comap_inducing_of_surjective f hf,
        exact prime_spectrum.comap_injective_of_surjective f hf,
        exact is_closed_spec_of_surjective f,
    end

end spec_of_surjective
