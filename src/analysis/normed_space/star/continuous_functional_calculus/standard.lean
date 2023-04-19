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
variable {A}

lemma self_adjoint.cfc₂_is_self_adjoint (a : self_adjoint A) (f : C(ℝ, ℝ)) :
  is_self_adjoint (cfc₂ (a : A) f) :=
show star _ = _, by rw [←map_star, star_trivial]

-- composition still works as long as we have propositinal equality of the intermediate elements.
lemma self_adjoint.cfc₂_comp (a b : self_adjoint A) (f g : C(ℝ, ℝ)) (h : cfc₂ (a : A) f = b) :
  cfc₂ (a : A) (g.comp f) = cfc₂ (b : A) g :=
begin
  letI : continuous_functional_calculus_spectrum_class ℝ (cfc₂ (a : A) f),
   from cast (by rw h) (standard_cfc.complex_to_real A b),
  rw cfc₂_comp (a : A) f g,
  congr' 3,
  simp only [cast_heq],
end

lemma self_adjoint.cfc₂_comp_coe_mk (a : self_adjoint A) (f g : C(ℝ, ℝ))
  (h := self_adjoint.cfc₂_is_self_adjoint a f) :
  cfc₂ (a : A) (g.comp f) = cfc₂ ((⟨cfc₂ (a : A) f, h⟩ : self_adjoint A) : A) g :=
self_adjoint.cfc₂_comp a _ f g rfl

open_locale polynomial

lemma self_adjoint.comp_neg (a : self_adjoint A) (f : C(ℝ, ℝ)) :
  cfc₂ (↑-a : A) f = cfc₂ (a : A) (f.comp (-(X : ℝ[X]).to_continuous_map)) :=
begin
  have := self_adjoint.cfc₂_comp a (-a) (-X : ℝ[X]).to_continuous_map_alg_hom f
    (by rw [map_neg, map_neg, to_continuous_map_alg_hom_apply, cfc₂_map_X, add_subgroup.coe_neg]),
  rw ← this,
  refine fun_like.congr_arg _ (continuous_map.ext $ λ x, _),
  simp only [to_continuous_map_alg_hom_apply, continuous_map.comp_apply, to_continuous_map_apply, eval_neg,
  continuous_map.neg_apply],
end

noncomputable instance selfadjoint.has_pos_part : has_pos_part (self_adjoint A) :=
{ pos := λ a, ⟨cfc₂ (a : A) (continuous_map.id ℝ ⊔ 0), self_adjoint.cfc₂_is_self_adjoint a _⟩ }

lemma self_adjoint.pos_part_def (a : self_adjoint A) (h := self_adjoint.cfc₂_is_self_adjoint a _) :
  a⁺ = ⟨cfc₂ (a : A) (continuous_map.id ℝ ⊔ 0), h⟩ := rfl

lemma self_adjoint.coe_pos_part (a : self_adjoint A) :
  (↑(a⁺) : A) = cfc₂ (a : A) (continuous_map.id ℝ ⊔ 0) :=
rfl

noncomputable instance selfadjoint.has_neg_part : has_neg_part (self_adjoint A) :=
{ neg := λ a, (-a)⁺ }

lemma self_adjoint.neg_part_def (a : self_adjoint A) : a⁻ = (-a)⁺ := rfl

lemma self_adjoint.coe_neg_part (a : self_adjoint A) :
  (↑(a⁻) : A) = cfc₂ (↑-a : A) (continuous_map.id ℝ ⊔ 0) := rfl

lemma self_adjoint.neg_part_neg (a : self_adjoint A) : (-a)⁻ = a⁺ :=
by rw [self_adjoint.neg_part_def, neg_neg]

lemma self_adjoint.pos_part_sub_neg_part (a : self_adjoint A) : a⁺ - a⁻ = a :=
sorry

#exit

-- this lemma is probably not necessary, but it's useful to show how this works.
-- It is significantly more important for positive elements.
lemma self_adjoint.cfc_spectrum_restricts (a : self_adjoint A) (g : C(spectrum ℝ (a : A), ℝ)) :
  spectrum_restricts (cfc₁ g) continuous_map.complex_re :=
a.prop.spectrum_restricts.cfc_spectrum_restricts _ g

/-- `to_nnreal` as a bundled continuous map. -/
noncomputable def continuous_map.to_nnreal : C(ℝ, ℝ≥0) :=
⟨real.to_nnreal,
 (@continuous_induced_rng ℝ≥0 ℝ _ coe real.to_nnreal _ _).mpr (continuous_id'.max continuous_const)⟩

@[protect_proj]
structure is_positive (a : A) : Prop :=
(is_self_adjoint : is_self_adjoint a)
(spectrum_subset : spectrum ℝ a ⊆ set.range (algebra_map ℝ≥0 ℝ))

protected lemma is_positive.spectrum_restricts {a : A} (ha : is_positive a) :
  spectrum_restricts a continuous_map.to_nnreal :=
spectrum_restricts_of_subset_range_algebra_map a continuous_map.to_nnreal
  (λ r, real.to_nnreal_coe) ha.spectrum_subset



variable (A)
def positive := {a : A // is_positive a}



#exit

end standard_cfc
