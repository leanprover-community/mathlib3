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

variables {R S : CommRing}
variables (f : R →+* S)

postfix ` ^* ` : 80 := prime_spectrum.comap

example {X Y : Type} (f : X -> Y) (hf : surjective f) (A B : set Y) :
f ⁻¹' A ⊆ f ⁻¹' B -> A ⊆ B :=
begin
exact (surjective.preimage_subset_preimage_iff hf).mp
end

lemma comap_inducing_of_surjective (hf : surjective f) : inducing (f ^*) :=
    begin
    constructor,
    rw topological_space_eq_iff,
    intro U,
    simp_rw ← is_closed_compl_iff,
    generalize : Uᶜ = Z,
    split,
    {
        rw [is_closed_induced_iff, is_closed_iff_zero_locus],
        rintro ⟨F, hF⟩, rw hF,
        use zero_locus (f ⁻¹' F),
        split,
        rw is_closed_iff_zero_locus,
        use f ⁻¹' F,
        ext p, simp,
        apply (surjective.preimage_subset_preimage_iff hf),
    },
    {
        rw is_closed_induced_iff,
        rintro ⟨C, ⟨hC1, hC2⟩⟩,
        subst hC2,
        exact hC1.preimage (comap f).continuous,
    },
    end

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
