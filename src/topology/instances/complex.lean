/-
Copyright (c) 2022 Xavier Roblot. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Xavier Roblot
-/

import topology.algebra.uniform_field
import analysis.complex.basic
import field_theory.adjoin

/-!
# Some results about the topology of ℂ
-/

section complex_subfield

open complex set

open_locale complex_conjugate

/-- The only closed subfields of `ℂ` are `ℝ` and `ℂ`. -/
lemma complex.subfield_eq_of_closed {K : subfield ℂ} (hc : is_closed (K : set ℂ)) :
  K = of_real.field_range ∨ K = ⊤ :=
begin
  suffices : range (coe : ℝ → ℂ) ⊆ K,
  { rw [range_subset_iff, ← coe_algebra_map] at this,
    have := (subalgebra.is_simple_order_of_finrank finrank_real_complex).eq_bot_or_eq_top
      (subfield.to_intermediate_field K this).to_subalgebra,
    simp_rw ← set_like.coe_set_eq at this ⊢,
    convert this using 2,
    simpa only [ring_hom.coe_field_range, algebra.coe_bot, coe_algebra_map], },
  suffices : range (coe : ℝ → ℂ) ⊆ closure (set.range ((coe : ℝ → ℂ) ∘ (coe : ℚ → ℝ))),
  { refine subset_trans this _,
    rw ← is_closed.closure_eq hc,
    apply closure_mono,
    rintros _ ⟨_, rfl⟩,
    simp only [function.comp_app, of_real_rat_cast, set_like.mem_coe, subfield_class.coe_rat_mem] },
  nth_rewrite 1 range_comp,
  refine subset_trans _ (image_closure_subset_closure_image continuous_of_real),
  rw dense_range.closure_range rat.dense_embedding_coe_real.dense,
  simp only [image_univ],
end

/-- Let `K` a subfield of `ℂ` and let `ψ : K →+* ℂ` a ring homomorphism. Assume that `ψ` is uniform
continuous, then `ψ` is either the inclusion map or the composition of the inclusion map with the
complex conjugation. -/
lemma complex.uniform_continuous_ring_hom_eq_id_or_conj (K : subfield ℂ) {ψ : K →+* ℂ}
  (hc : uniform_continuous ψ) : ψ.to_fun = K.subtype ∨ ψ.to_fun = conj ∘ K.subtype :=
begin
  letI : topological_division_ring ℂ := topological_division_ring.mk,
  letI : topological_ring K.topological_closure :=
      subring.topological_ring K.topological_closure.to_subring,
  set ι : K → K.topological_closure := subfield.inclusion K.le_topological_closure,
  have ui : uniform_inducing ι :=
    ⟨ by { erw [uniformity_subtype, uniformity_subtype, filter.comap_comap], congr, } ⟩,
  let di := ui.dense_inducing _,
  { -- extψ : closure(K) →+* ℂ is the extension of ψ : K →+* ℂ
    let extψ := dense_inducing.extend_ring_hom ui di.dense hc,
    haveI := (uniform_continuous_uniformly_extend ui di.dense hc).continuous,
    cases complex.subfield_eq_of_closed (subfield.is_closed_topological_closure K),
    { left,
      let j := ring_equiv.subfield_congr h,
      -- ψ₁ is the continuous ring hom `ℝ →+* ℂ` constructed from `j : closure (K) ≃+* ℝ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ := ring_hom.comp extψ (ring_hom.comp j.symm.to_ring_hom of_real.range_restrict),
      ext1 x,
      rsuffices ⟨r, hr⟩ : ∃ r : ℝ, of_real.range_restrict r = j (ι x),
      { have := ring_hom.congr_fun
          (ring_hom_eq_of_real_of_continuous (by continuity! : continuous ψ₁)) r,
        rw [ring_hom.comp_apply, ring_hom.comp_apply, hr, ring_equiv.to_ring_hom_eq_coe] at this,
        convert this using 1,
        { exact (dense_inducing.extend_eq di hc.continuous _).symm, },
        { rw [← of_real.coe_range_restrict, hr], refl, }},
      obtain ⟨r, hr⟩ := set_like.coe_mem (j (ι x)),
      exact ⟨r, subtype.ext hr⟩, },
    { -- ψ₁ is the continuous ring hom `ℂ →+* ℂ` constructed from `closure (K) ≃+* ℂ`
      -- and `extψ : closure (K) →+* ℂ`
      let ψ₁ := ring_hom.comp extψ (ring_hom.comp (ring_equiv.subfield_congr h).symm.to_ring_hom
        (@subfield.top_equiv ℂ _).symm.to_ring_hom),
      cases ring_hom_eq_id_or_conj_of_continuous (by continuity! : continuous ψ₁) with h h,
      { left, ext1 z,
        convert (ring_hom.congr_fun h z) using 1,
        exact (dense_inducing.extend_eq di hc.continuous z).symm, },
      { right, ext1 z,
        convert (ring_hom.congr_fun h z) using 1,
        exact (dense_inducing.extend_eq di hc.continuous z).symm, }}},
  { let j : { x // x ∈ closure (id '' {x | (K : set ℂ) x })} → (K.topological_closure : set ℂ) :=
      λ x, ⟨x, by { convert x.prop, simpa only [id.def, set.image_id'], }⟩,
    convert dense_range.comp (function.surjective.dense_range _)
      (dense_embedding.subtype (dense_embedding_id) (K : set ℂ)).dense
      (by continuity : continuous j),
    rintros ⟨y, hy⟩,
    use ⟨y, by { convert hy, simpa only [id.def, set.image_id'], }⟩,
    simp only [subtype.mk_eq_mk, subtype.coe_mk], }
end

end complex_subfield
