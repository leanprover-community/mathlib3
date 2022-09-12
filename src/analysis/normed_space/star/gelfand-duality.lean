import analysis.normed_space.star.spectrum
import analysis.normed_space.units
import analysis.normed.group.quotient
import analysis.normed_space.algebra
import topology.continuous_function.units
import topology.continuous_function.compact
import topology.algebra.algebra
import topology.continuous_function.stone_weierstrass

.

section algebra_map

variables {A : Type*} [normed_ring A] [normed_algebra ℂ A] (hA : ∀ (a : A), is_unit a ↔ a ≠ 0)
  [complete_space A]

/- This wouldn't be necessary if either we assumed `[norm_one_class A]`, or if we knew that algebra
homomorphisms into the base field were continuous. This requires generalizing things in
`analysis/normed_space/spectrum` away from `norm_one_class`, or else proving that any Banach algebra
is equivalent to a `norm_one_class` Banach algebra. -/
lemma normed_ring.alg_equiv_complex_of_complete_symm_continuous :
  continuous ((normed_ring.alg_equiv_complex_of_complete hA).symm : A → ℂ) :=
begin
  have one_pos := norm_pos_iff.mpr ((hA 1).mp ⟨⟨1, 1, mul_one _, mul_one _⟩, rfl⟩),
  refine add_monoid_hom_class.continuous_of_bound _ (∥(1 : A)∥⁻¹) _,
  intros x,
  obtain ⟨y, rfl⟩ := (normed_ring.alg_equiv_complex_of_complete hA).surjective x,
  simpa only [←inv_mul_le_iff (inv_pos.mpr one_pos), inv_inv, mul_comm, alg_equiv.symm_apply_apply]
    using (norm_algebra_map A (y : ℂ)).ge,
end

end algebra_map

.

section
open weak_dual

variables {A : Type*} [normed_comm_ring A] [normed_algebra ℂ A] [complete_space A]
  [norm_one_class A] (I : ideal A) [hI : I.is_maximal]

/-- The equivalence between characters and algebra homomorphisms into the base field. This requires
`norm_one_class` for technical reasons, but with enough work could be replaced with `nontrivial`. -/
def weak_dual.character_space.equiv_alg_hom {𝕜 A : Type*} [normed_field 𝕜] [normed_ring A]
  [normed_algebra 𝕜 A] [complete_space A] [norm_one_class A] : (character_space 𝕜 A) ≃ (A →ₐ[𝕜] 𝕜)  :=
{ to_fun := λ f, character_space.to_alg_hom f,
  inv_fun := λ f,
  { val := f.to_continuous_linear_map,
    property := by { rw character_space.eq_set_map_one_map_mul, exact ⟨map_one f, map_mul f⟩ } },
  left_inv := λ f, subtype.ext $ continuous_linear_map.ext $ λ x, rfl,
  right_inv := λ f, alg_hom.ext $ λ x, rfl }

@[simp] lemma weak_dual.character_space.equiv_alg_hom_coe {𝕜 A : Type*} [normed_field 𝕜]
  [normed_ring A] [normed_algebra 𝕜 A] [complete_space A] [norm_one_class A]
  (f : character_space 𝕜 A) : ⇑(weak_dual.character_space.equiv_alg_hom f) = f := rfl

@[simp] lemma weak_dual.character_space.equiv_alg_hom_symm_coe {𝕜 A : Type*} [normed_field 𝕜]
  [normed_ring A] [normed_algebra 𝕜 A] [complete_space A] [norm_one_class A] (f : A →ₐ[𝕜] 𝕜) :
  ⇑(weak_dual.character_space.equiv_alg_hom.symm f) = f := rfl

include hI

lemma ideal.quotient.is_unit_iff_ne_zero : ∀ x : A ⧸ I, is_unit x ↔ x ≠ 0 :=
by { letI := ideal.quotient.field I, exact @is_unit_iff_ne_zero (A ⧸ I) _ }

/-- Every maximal ideal in a commutative complex Banach algebra gives rise to a character on that
algebra. In particular, the character, which may be identified as an algebra homomorphism due to
`weak_dual.character_space.equiv_alg_hom`, is given by the composition of the quotient map and
the Gelfand-Mazur isomorphism `normed_ring.alg_equiv_complex_of_complete`. -/
noncomputable def ideal.is_maximal.character_space : character_space ℂ A :=
weak_dual.character_space.equiv_alg_hom.symm $
  ((@normed_ring.alg_equiv_complex_of_complete (A ⧸ I) _ _
  (ideal.quotient.is_unit_iff_ne_zero I) _).symm : A ⧸ I →ₐ[ℂ] ℂ).comp
  (ideal.quotient.mkₐ ℂ I)

lemma ideal.is_maximal.character_space_apply_zero_of_mem (a : A) (ha : a ∈ I) :
  (ideal.is_maximal.character_space I) a = 0 :=
begin
  unfold ideal.is_maximal.character_space,
  simpa only [weak_dual.character_space.equiv_alg_hom_symm_coe, alg_hom.coe_comp,
    alg_equiv.coe_alg_hom, ideal.quotient.mkₐ_eq_mk, function.comp_app,
    ideal.quotient.eq_zero_iff_mem.mpr ha, spectrum.zero_eq,
    normed_ring.alg_equiv_complex_of_complete_symm_apply]
    using set.eq_of_mem_singleton (set.nonempty.some_mem (set.singleton_nonempty (0 : ℂ))),
end
.

.

example : compact_space (character_space ℂ A) := infer_instance
omit hI
lemma ideal.span_singleton_ne_top {R : Type*} [comm_semiring R] {r : R} (hr : ¬ is_unit r) :
  ideal.span ({r} : set R) ≠ ⊤ :=
begin
  refine (ideal.ne_top_iff_one _).mpr (λ h1, _),
  obtain ⟨x, hx⟩ := ideal.mem_span_singleton'.mp h1,
  exact hr ⟨⟨r, x, mul_comm x r ▸ hx, hx⟩, rfl⟩,
end

lemma key₀ (a : A) (ha : ¬ is_unit a) : ∃ f : character_space ℂ A, f a = 0 :=
begin
  obtain ⟨M, hM, haM⟩ := ideal.exists_le_maximal (ideal.span {a}) (ideal.span_singleton_ne_top ha),
  haveI := hM,
  exact ⟨ideal.is_maximal.character_space M, ideal.is_maximal.character_space_apply_zero_of_mem _ _
    (haM (ideal.mem_span_singleton.mpr ⟨1, (mul_one a).symm⟩))⟩,
end
.

lemma key₁ (a : A) (z : ℂ) (hz : z ∈ spectrum ℂ a) : z ∈ spectrum ℂ (gelfand_transform ℂ A a) :=
begin
  rw [continuous_map.spectrum_eq_range],
  obtain ⟨f, hf⟩ := key₀ (algebra_map ℂ A z - a) hz,
  simp only [map_sub, sub_eq_zero, alg_hom_class.commutes, algebra.id.map_eq_id, ring_hom.id_apply]
    at hf,
  refine ⟨f, hf.symm⟩,
end

.

lemma key₂ (a : A) : spectrum ℂ a = spectrum ℂ (gelfand_transform ℂ A a) :=
set.subset.antisymm (λ z hz, key₁ a z hz) (alg_hom.spectrum_apply_subset (gelfand_transform ℂ A) a)

--local attribute [instance] norm_one_class.nontrivial
variables [star_ring A] [cstar_ring A] [star_module ℂ A] [nontrivial A]

lemma key₃  (a : A) : spectrum ℂ a = spectrum ℂ (gelfand_star_transform A a) :=
key₂ a

instance : nonempty (character_space ℂ A) :=
⟨classical.some $ key₀ (0 : A) (zero_mem_nonunits.mpr zero_ne_one)⟩

instance foo {X E : Type*} [topological_space X] [compact_space X] [nonempty X] [normed_ring E]
  [norm_one_class E] : norm_one_class C(X, E) :=
⟨by simp [continuous_map.norm_eq_supr_norm]⟩

open_locale nnreal

variables (A)
lemma key₄ : isometry (gelfand_star_transform A) :=
begin
  refine add_monoid_hom_class.isometry_of_norm (gelfand_star_transform A) (λ a, _),
  have : spectral_radius ℂ (gelfand_star_transform A (star a * a)) = spectral_radius ℂ (star a * a),
  { unfold spectral_radius, rw key₃, },
  simp only [map_mul, map_star, (is_self_adjoint.star_mul_self _).spectral_radius_eq_nnnorm,
    ennreal.coe_eq_coe, cstar_ring.nnnorm_star_mul_self, ←sq] at this,
  simpa only [function.comp_app, nnreal.sqrt_sq]
    using congr_arg ((coe : ℝ≥0 → ℝ) ∘ ⇑nnreal.sqrt) this,
end

.
lemma bar : ⇑(gelfand_transform ℂ A) = gelfand_star_transform A :=
funext $ λ a, continuous_map.ext $ λ φ, rfl

lemma key₅ : function.surjective (gelfand_star_transform A) :=
begin
  have clsd := (key₄ A).closed_embedding.closed_range,
  change function.surjective (gelfand_transform ℂ A),
  rw ←bar at clsd,
  have clsd' : (gelfand_transform ℂ A).range.topological_closure = (gelfand_transform ℂ A).range,
  from le_antisymm (subalgebra.topological_closure_minimal _ le_rfl clsd)
    (subalgebra.subalgebra_topological_closure _),
  have : (gelfand_transform ℂ A).range = ⊤,
  { rw ← clsd',
    refine continuous_map.subalgebra_is_R_or_C_topological_closure_eq_top_of_separates_points _ _ _,
    { intros φ ψ,
      contrapose!,
      intro h,
      apply subtype.ext, apply continuous_linear_map.ext, rintro a,
      simp only [character_space.coe_coe],
      exact h (gelfand_transform ℂ A a) ⟨gelfand_transform ℂ A a, ⟨a, rfl⟩, rfl⟩, },
    { intros φ hφ,
      simp only [subalgebra.mem_restrict_scalars, alg_hom.mem_range],
      rcases subalgebra.mem_map.mp hφ with ⟨ψ, ⟨a, ha⟩, rfl⟩,
      simp only [alg_hom.to_ring_hom_eq_coe, alg_hom.coe_to_ring_hom] at ha,
      use star a,
      rw [bar, map_star, ←bar, ha],
      ext1,
      simp only [ring_hom.coe_monoid_hom, alg_equiv.coe_alg_hom, ring_hom.to_monoid_hom_eq_coe,
        alg_equiv.to_alg_hom_eq_coe, ring_hom.to_fun_eq_coe, continuous_map.coe_mk,
        is_R_or_C.conj_ae_coe, alg_hom.coe_to_ring_hom, monoid_hom.to_fun_eq_coe,
        ring_hom.comp_left_continuous_apply, monoid_hom.comp_left_continuous_apply,
        continuous_map.comp_apply, alg_hom.to_ring_hom_eq_coe, alg_hom.comp_left_continuous_apply],
      refl,
       },
    },
  exact λ x, this.symm ▸ (gelfand_transform ℂ A).mem_range.mp (this.symm ▸ algebra.mem_top),
end




end

.
