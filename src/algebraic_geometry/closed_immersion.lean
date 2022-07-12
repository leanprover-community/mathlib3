import algebraic_geometry.Spec
import algebraic_geometry.Scheme
import algebraic_geometry.AffineScheme
import algebraic_geometry.prime_spectrum.basic
import linear_algebra.quotient

universe u

/- An attempt at formalizing the equivalence of (2) and (4) in https://stacks.math.columbia.edu/tag/01QN
Started at LFTCM 2022 with Sam, Jake and Sina
-/

noncomputable theory

open topological_space
open category_theory
open Top
open opposite

namespace algebraic_geometry

variables {X Y : Scheme.{u}} (f : X ⟶ Y)

-- postfix ` ^# ` : 80 := λ f, f.val.c
def sharp := f.val.c
postfix ` ^# ` : 80 := sharp

-- Our definition here is item (4) in https://stacks.math.columbia.edu/tag/01QO

structure is_closed_immersion (f : X ⟶ Y) : Prop :=
    (is_closed_embedding_base : closed_embedding f.val.base)
    (is_epi : epi (f ^#))

-- We formalize the fact from https://stacks.math.columbia.edu/tag/01IG which should be a (very) special case of what we are trying to do

variables (R : CommRing) (I : ideal R)
local notation `π` := ideal.quotient.mk I
--local notation `ι` := Scheme.Spec_map (CommRing.of_hom π)
local notation `ι` := prime_spectrum.comap π

--looking at the proof of localization_comap_inducing in prime_spectrum.basic
lemma spec_of_quotient_inducing :
    inducing ι :=
    begin
    constructor,
    rw topological_space_eq_iff,
    intro U,
    simp_rw ← is_closed_compl_iff,
    generalize : Uᶜ = Z,
    rw [is_closed_induced_iff, prime_spectrum.is_closed_iff_zero_locus],
    split,
    { rintro ⟨S, rfl⟩,
    -- we want to take for t the inverse image of S
      sorry, },
    { rintro ⟨T, ⟨hclosed, hinv⟩⟩,
    -- we want to take for s the direct image of T
    sorry, }

    end

lemma spec_of_quotient_injective :
    function.injective ι :=
    begin
        apply prime_spectrum.comap_injective_of_surjective,
        exact ideal.quotient.mk_surjective,
    end

lemma image_of_spec_of_quotient :
   set.range ι = prime_spectrum.zero_locus I :=
   begin
    ext x,
    split,
    { rintro ⟨p, rfl⟩ a ha,
      simp,
      -- need to use: linear_algebra.quotient.mk_eq_zero
      sorry,},

    { sorry, }
   end

lemma spec_of_quotient_closed :
    is_closed (set.range ι) :=
    begin
        rw image_of_spec_of_quotient,
        exact prime_spectrum.is_closed_zero_locus ↑I,
    end

lemma spec_of_quotient_embedding : embedding ι :=
    ⟨ spec_of_quotient_inducing R I, spec_of_quotient_injective R I ⟩

lemma spec_of_quotient_closed_embedding : closed_embedding ι :=
    ⟨ spec_of_quotient_embedding R I, spec_of_quotient_closed R I⟩


/-
lemma ideal_gives_closed_immersion : is_closed_immersion ι :=
{
    is_closed_embedding_base := begin
    sorry
    end,
    is_epi := sorry,
}
-/

end algebraic_geometry
