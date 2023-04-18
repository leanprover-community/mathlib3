import analysis.normed_space.star.continuous_functional_calculus.basic
import analysis.normed_space.star.continuous_functional_calculus

open_locale nnreal

open polynomial

namespace spectrum

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] [complete_space A]

lemma real_is_compact (a : A) : is_compact (spectrum ℝ a) :=
(@spectrum.preimage_algebra_map ℝ ℂ A _ _ _ _ _ _ _ a) ▸
  complex.isometry_of_real.closed_embedding.is_compact_preimage (spectrum.is_compact a)

lemma nnreal_is_compact (a : A) : is_compact (spectrum ℝ≥0 a) :=
(@spectrum.preimage_algebra_map ℝ≥0 ℂ A _ _ _ _ _ _ _ a) ▸
  (show isometry (coe : ℝ≥0 → ℝ), from isometry_subtype_coe).closed_embedding.is_compact_preimage
  (real_is_compact a)

instance compact_space (a : A) : compact_space (spectrum ℂ a) :=
is_compact_iff_compact_space.1 (spectrum.is_compact a)

instance real_compact_space (a : A) : compact_space (spectrum ℝ a) :=
is_compact_iff_compact_space.1 (real_is_compact a)

instance nnreal_compact_space (a : A) : compact_space (spectrum ℝ≥0 a) :=
is_compact_iff_compact_space.1 (nnreal_is_compact a)

end spectrum

section standard_cfc

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A]
variables [star_ring A] [cstar_ring A] [star_module ℂ A]
variables [complete_space A] (a : A) [is_star_normal a]

/-- The usual continuous functional calculus (over `ℂ`) for normal elements
in a C⋆-algebra over `ℂ`. -/
noncomputable instance is_star_normal.continuous_functional_calculus_isometry_class :
  continuous_functional_calculus_isometry_class ℂ a :=
{ to_star_alg_hom := (elemental_star_algebra ℂ a).subtype.comp (continuous_functional_calculus a),
  hom_isometry := isometry_subtype_coe.comp
    (@star_alg_equiv.isometry _ _ _ _ _ _ _ _ _ _ _ _ _ star_alg_equiv.star_alg_equiv_class $
    continuous_functional_calculus a),
  hom_map_X :=
  begin
    convert congr_arg coe (continuous_functional_calculus_map_id a),
    simp only [star_alg_hom.comp_apply, star_alg_hom.coe_coe, star_subalgebra.subtype_apply],
    congr' 2,
    exact continuous_map.ext (λ _, eval_X),
  end }

/-- The usual continuous functional calculus (over `ℂ`) for normal elements
in a C⋆-algebra over `ℂ`. -/
noncomputable instance is_star_normal.continuous_functional_calculus_spectrum_class :
  continuous_functional_calculus_spectrum_class ℂ a :=
{ to_star_alg_hom := (elemental_star_algebra ℂ a).subtype.comp (continuous_functional_calculus a),
  hom_map_spectrum := λ f,
  begin
    simp only [star_subalgebra.coe_subtype, star_alg_hom.coe_coe, star_alg_hom.comp_apply],
    rw [←star_subalgebra.spectrum_eq (elemental_star_algebra.is_closed ℂ a), alg_equiv.spectrum_eq,
      continuous_map.spectrum_eq_range],
  end,
  .. continuous_functional_calculus_isometry_class.to_continuous_functional_calculus_injective_class ℂ a }

-- just checking it works!
example (f g : C(ℂ, ℂ)) : cfc₂ a (g.comp f) = cfc₂ (cfc₂ a f) g := cfc₂_comp a f g

variable (A)
/-- The usual continuous functional calculus (over `ℝ`) for selfadjoint elements
in a C⋆-algebra over `ℂ`. -/
noncomputable instance standard_cfc.complex_to_real (a : self_adjoint A) :
  continuous_functional_calculus_spectrum_class ℝ (a : A) :=
a.prop.spectrum_restricts.cfc_spectrum continuous_map.complex_re

-- this lemma is probably not necessary, but it's useful to show how this works.
-- It is significantly more important for positive elements.
lemma self_adjoint.cfc_spectrum_restricts (a : self_adjoint A) (g : C(spectrum ℝ (a : A), ℝ)) :
  spectrum_restricts (cfc₁ g) continuous_map.complex_re :=
a.prop.spectrum_restricts.cfc_spectrum_restricts _ g

/-- This is a hack to make it so that we can apply the continuous functional calculus iteratively.
Maybe it's not so useful, but I would expect it could be. -/
noncomputable instance standard_cfc.complex_to_real_comp (a : self_adjoint A) (f : C(ℝ, ℝ)) :
  continuous_functional_calculus_spectrum_class ℝ (cfc₂ (a : A) f) :=
begin
  refine cast _ (standard_cfc.complex_to_real A ⟨_, (is_self_adjoint_star_hom_apply (cfc₂ (a : A)) f : is_self_adjoint (cfc₂ (a : A) f))⟩),
  by rw subtype.coe_mk,
end

-- composition still works
example (a : self_adjoint A) (f g : C(ℝ, ℝ)) : cfc₂ (a : A) (g.comp f) = cfc₂ (cfc₂ (a : A) f) g :=
cfc₂_comp (a : A) f g



end standard_cfc
