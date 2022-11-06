import topology.algebra.uniform_field
import analysis.complex.basic
import field_theory.adjoin

section complex_subfield

open_locale complex_conjugate

lemma complex.subfield_eq_of_closed {K : subfield ℂ} (hc : is_closed (K : set ℂ)) :
  K = complex.of_real.field_range ∨ K = ⊤ :=
begin
  suffices : set.range (coe : ℝ → ℂ) ⊆ K,
  { rw [set.range_subset_iff, ← complex.coe_algebra_map] at this,
    have := (subalgebra.is_simple_order_of_finrank complex.finrank_real_complex).eq_bot_or_eq_top
      (subfield.to_intermediate_field K this).to_subalgebra,
    simp_rw ← set_like.coe_set_eq at this ⊢,
    convert this using 2,
    ext,
    simp only [ring_hom.coe_field_range, set.mem_range, complex.of_real_eq_coe, algebra.coe_bot,
      complex.coe_algebra_map], },
  suffices : set.range (coe : ℝ → ℂ) ⊆ closure (set.range ((coe : ℝ → ℂ) ∘ (coe : ℚ → ℝ))),
  { refine subset_trans this _,
    rw ← is_closed.closure_eq hc,
    apply closure_mono,
    rintros _ ⟨_, rfl⟩,
    simp only
      [function.comp_app, complex.of_real_rat_cast, set_like.mem_coe, subfield_class.coe_rat_mem] },
  nth_rewrite 1 set.range_comp,
  refine subset_trans _ (image_closure_subset_closure_image complex.continuous_of_real),
  rw dense_range.closure_range rat.dense_embedding_coe_real.dense,
  simp only [set.image_univ],
end

lemma subfield.eq_id_or_conj_uniform_continuous (K : subfield ℂ) {ψ : K →+* ℂ}
  (hc : uniform_continuous ψ) : ψ.to_fun = K.subtype ∨ ψ.to_fun = conj ∘ K.subtype :=
begin

  letI : topological_division_ring ℂ := topological_division_ring.mk,
  letI : topological_ring K.topological_closure :=
      subring.topological_ring K.topological_closure.to_subring,
  set ι := subfield.inclusion (subfield.subfield_topological_closure K),
  have ui : uniform_inducing ι :=
    ⟨ by { erw [uniformity_subtype, uniformity_subtype, filter.comap_comap], congr, } ⟩,
  let di := ui.dense_inducing (dense_range_of_subset_closure K),
  let extψ := dense_inducing.extend_hom ui di.dense hc,
  have hK : is_closed (K.topological_closure : set ℂ) := subfield.is_closed_topological_closure K,
  haveI := (uniform_continuous_uniformly_extend ui di.dense hc).continuous,
  cases complex.subfield_eq_of_closed hK,
  { left,
    let j := ring_equiv.subfield_congr h,
    -- ψ₁ is the continuous ring hom `ℝ →+* ℂ` constructed from `j : clos (K) ≃+* ℝ`
    -- and `extψ : clos (K) →+* ℂ`
    let ψ₁ := ring_hom.comp extψ (ring_hom.comp j.symm.to_ring_hom complex.of_real.range_restrict),
    ext1 x,
    rsuffices ⟨r, hr⟩ : ∃ r : ℝ, complex.of_real.range_restrict r = j (ι x),
    { have := ring_hom.congr_fun
        (complex.ring_hom_eq_of_real_of_continuous (by continuity! : continuous ψ₁)) r,
      rw [ring_hom.comp_apply, ring_hom.comp_apply, hr, ring_equiv.to_ring_hom_eq_coe] at this,
      erw ring_equiv.symm_apply_apply at this,
      convert this using 1,
      { exact (dense_inducing.extend_eq di hc.continuous _).symm, },
      { rw [← complex.of_real.coe_range_restrict, hr], refl, }},
    obtain ⟨r, hr⟩ := set_like.coe_mem (j (ι x)),
    use r,
    rw ← ring_hom.coe_range_restrict at hr,
    exact_mod_cast hr, },
  { -- ψ₁ is the continuous ring hom `ℂ →+* ℂ` constructed from `clos (K) ≃+* ℂ`
    -- and `extψ : clos (K) →+* ℂ`
    let ψ₁ := ring_hom.comp extψ (ring_hom.comp (ring_equiv.subfield_congr h).symm.to_ring_hom
      (@subfield.top_equiv ℂ _).symm.to_ring_hom),
    cases complex.ring_hom_eq_id_or_conj_of_continuous (by continuity! : continuous ψ₁) with h h,
    { left, ext1 z,
      convert (ring_hom.congr_fun h z) using 1,
      exact (dense_inducing.extend_eq di hc.continuous z).symm, },
    { right, ext1 z,
      convert (ring_hom.congr_fun h z) using 1,
      exact (dense_inducing.extend_eq di hc.continuous z).symm, }},
end

end complex_subfield
