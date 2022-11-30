/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.module.pi
import algebra.module.pointwise_pi
import analysis.convex.measure
import measure_theory.group.fundamental_domain

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

- `exists_sub_mem_lattice_of_volume_lt_volume`: Blichfeldt's principle, existence of two points
  within a set whose difference lies in a subgroup when the covolume of the subgroup is larger than
  the set.
- `exists_nonzero_mem_lattice_of_volume_mul_two_pow_card_lt_measure`: Minkowski's theorem, existence
  of a non-zero lattice point inside a convex symmetric domain of large enough covolume.

## TODO

* A finite index subgroup has given fundamental domain and covolume
* Some existence result in a metric space
* Voronoi

See https://arxiv.org/pdf/1405.2119.pdf for some more ideas.
-/

section
variables {E G H : Type*} [group G] [group H] [mul_equiv_class E G H]

@[simp, to_additive]
lemma mul_equiv.coe_to_equiv_symm (e : G ≃* H) : (e.symm : H ≃ G) = (e : G ≃ H).symm := rfl

namespace subgroup

/-- A subgroup is isomorphic to its image under an isomorphism. If you only have an injective map,
use `subgroup.equiv_map_of_injective`. -/
@[to_additive  "An additive subgroup is isomorphic to its image under an an isomorphism. If you only
have an injective map, use `add_subgroup.equiv_map_of_injective`. "]
def equiv_map (L : subgroup G) (e : E) : L ≃* L.map (e : G →* H) :=
{ map_mul' := λ _ _, subtype.ext (map_mul e _ _), ..(e : G ≃ H).image L }

@[simp, to_additive]
lemma coe_equiv_map_apply (L : subgroup G) (e : E) (g : L) :
  ((L.equiv_map e g : L.map (e : G →* H)) : H) = e g := rfl

@[simp, to_additive]
lemma equiv_map_symm_apply (L : subgroup G) (e : G ≃* H) (g : L.map (e : G →* H)) :
  (L.equiv_map e).symm g = ⟨e.symm g, set_like.mem_coe.1 $ set.mem_image_equiv.1 g.2⟩ := rfl

@[simp, to_additive]
lemma equiv_map_of_injective_equiv (L : subgroup G) (e : E) :
  L.equiv_map_of_injective (e : G →* H) (by exact equiv_like.injective e) = L.equiv_map e :=
by { ext, refl }

@[to_additive] instance (L : subgroup G) [countable L] (e : E) : countable (L.map (e : G →* H)) :=
(L.equiv_map e).symm.injective.countable

end subgroup
end

section
variables {𝕜 α β : Type*} [semiring 𝕜] [add_comm_group α] [add_comm_group β] [module 𝕜 α]
  [module 𝕜 β]

@[simp]
lemma add_subgroup.linear_equiv_map_symm_apply (e : α ≃ₗ[𝕜] β) {L : add_subgroup α}
  {g : L.map (e : α →+ β)} :
  (L.equiv_map e).symm g = ⟨e.symm g, set_like.mem_coe.1 $ (@set.mem_image_equiv α β _ e _).1 g.2⟩ :=
L.equiv_map_symm_apply (e : α ≃+ β) _

end

namespace linear_equiv
variables {𝕜 α β : Type*} [semiring 𝕜] [add_comm_monoid α] [add_comm_monoid β] [module 𝕜 α]
  [module 𝕜 β]

@[simp] lemma symm_comp_self (e : α ≃ₗ[𝕜] β) : e.symm ∘ e = id := e.to_equiv.symm_comp_self
@[simp] lemma self_comp_symm (e : α ≃ₗ[𝕜] β) : e ∘ e.symm = id := e.to_equiv.self_comp_symm

end linear_equiv

namespace measure_theory
open finite_dimensional fintype function measure set topological_space
open_locale pointwise

namespace measure
variables {E : Type*} [normed_add_comm_group E] [measurable_space E] [normed_space ℝ E]
  [finite_dimensional ℝ E] [borel_space E] (μ : measure_theory.measure E) [is_add_haar_measure μ]

lemma add_haar_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (s : set E) :
  μ (r • s) = ennreal.of_real (r ^ finrank ℝ E) * μ s :=
by rw [add_haar_smul, abs_pow, abs_of_nonneg hr]

end measure

section
variables {α β : Type*} [measurable_space α] [measurable_space β]

lemma quasi_measure_preserving_map (μ : measure α) (e : α ≃ᵐ β) :
  quasi_measure_preserving e.symm (map e μ) μ :=
{ measurable := e.symm.measurable,
  absolutely_continuous := by rw [map_map, e.symm_comp_self, map_id]; measurability }

end

section
variables {𝕜 G H : Type*} [nontrivially_normed_field 𝕜] [complete_space 𝕜] [measurable_space G]
  [topological_space G] [add_comm_group G] [module 𝕜 G] [finite_dimensional 𝕜 G]
  [has_continuous_smul 𝕜 G] (μ : measure G) [is_add_haar_measure μ] [borel_space G] [t2_space G]
  [topological_add_group G] [topological_space H] [add_comm_group H] [module 𝕜 H]
  [finite_dimensional 𝕜 H] [has_continuous_smul 𝕜 H] [measurable_space H] [borel_space H]
  [t2_space H] [topological_add_group H]

instance (e : G ≃ₗ[𝕜] H) : is_add_haar_measure (μ.map e) :=
e.to_add_equiv.is_add_haar_measure_map _ (e : G →ₗ[𝕜] H).continuous_of_finite_dimensional
  (e.symm : H →ₗ[𝕜] G).continuous_of_finite_dimensional

end

lemma rescale (ι : Type*) [fintype ι] {r : ℝ} (hr : 0 < r) :
  comap ((•) r) (volume : measure (ι → ℝ)) = ennreal.of_real r ^ card ι • volume :=
begin
  suffices : (ennreal.of_real r ^ card ι)⁻¹ • comap ((•) r) (volume : measure (ι → ℝ)) = volume,
  { conv_rhs { rw ←this },
    rw [ennreal.inv_pow, smul_smul, ←mul_pow, ennreal.mul_inv_cancel (ennreal.of_real_pos.2 hr).ne'
      ennreal.of_real_ne_top, one_pow, one_smul] },
  refine (pi_eq $ λ s hS, _).symm,
  simp only [smul_eq_mul, measure.coe_smul, pi.smul_apply],
  rw [comap_apply _ (smul_right_injective (ι → ℝ) hr.ne') (λ S hS, hS.const_smul₀ r) _
    (measurable_set.univ_pi hS), image_smul, smul_univ_pi, volume_pi_pi],
  simp only [add_haar_smul, finite_dimensional.finrank_self, pow_one, abs_of_pos hr, pi.smul_apply,
    finset.prod_mul_distrib, finset.card_univ, ←mul_assoc, finset.prod_const],
  rw [ennreal.inv_mul_cancel _ (ennreal.pow_ne_top ennreal.of_real_ne_top), one_mul],
  positivity,
end

namespace is_fundamental_domain
variables {G H α β E : Type*} [group G] [group H]
  [mul_action G α] [measurable_space α]
  [mul_action H β] [measurable_space β]
  [normed_add_comm_group E] {s t : set α} {μ : measure α} {ν : measure β}

@[to_additive measure_theory.is_add_fundamental_domain.preimage_of_equiv']
lemma preimage_of_equiv' [measurable_space H]
  [has_measurable_smul H β] [smul_invariant_measure H β ν]
  {s : set β} (h : is_fundamental_domain H s ν) {f : α → β}
  (hf : quasi_measure_preserving f μ ν) {e : H → G} (he : bijective e)
  (hef : ∀ g, semiconj f ((•) (e g)) ((•) g)) :
  is_fundamental_domain G (f ⁻¹' s) μ :=
{ null_measurable_set := h.null_measurable_set.preimage hf,
  ae_covers := (hf.ae h.ae_covers).mono $ λ x ⟨g, hg⟩, ⟨e g, by rwa [mem_preimage, hef g x]⟩,
  ae_disjoint := λ g hg,
    begin
      lift e to H ≃ G using he,
      have : (e.symm g⁻¹)⁻¹ ≠ (e.symm 1)⁻¹, by simp [hg],
      convert (h.pairwise_ae_disjoint this).preimage hf using 1,
      { simp only [←preimage_smul_inv, preimage_preimage, ←hef _ _, e.apply_symm_apply, inv_inv] },
      { ext1 x,
        simp only [mem_preimage, ←preimage_smul, ←hef _ _, e.apply_symm_apply, one_smul] }
    end }

@[to_additive measure_theory.is_add_fundamental_domain.image_of_equiv']
lemma image_of_equiv' [measurable_space G] [has_measurable_smul G α] [smul_invariant_measure G α μ]
  (h : is_fundamental_domain G s μ)
  (f : α ≃ β) (hf : quasi_measure_preserving f.symm ν μ)
  (e : H ≃ G) (hef : ∀ g, semiconj f ((•) (e g)) ((•) g)) :
  is_fundamental_domain H (f '' s) ν :=
begin
  rw f.image_eq_preimage,
  refine h.preimage_of_equiv' hf e.symm.bijective (λ g x, _),
  rcases f.surjective x with ⟨x, rfl⟩,
  rw [←hef, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]
end

end is_fundamental_domain

namespace is_fundamental_domain
variables {G α : Type*} [group G] [mul_action G α] [measurable_space G] [measurable_space α]
  [has_measurable_mul G] {L : subgroup G}

/- TODO: Prove the version giving `⌈volume S / volume F⌉` points whose difference is in a subgroup.
This needs the `m`-fold version of `exists_nonempty_inter_of_measure_univ_lt_tsum_measure` when
`m * measure < measure`, giving some element in `m` sets. -/
@[to_additive]
lemma exists_ne_div_mem {μ : measure G} [countable L] {s t : set G} (hs : null_measurable_set s μ)
 (fund : is_fundamental_domain L t μ) (hlt : μ t < μ s)
  [is_mul_left_invariant (μ : measure G)] :
  ∃ x y ∈ s, x ≠ y ∧ y / x ∈ L :=
let ⟨x, hx, y, hy, g, hg, rfl⟩ := fund.exists_ne_one_smul_eq hs hlt in
  by refine ⟨x, hx, _, hy, _, _⟩; simp [subgroup.smul_def]; assumption

end is_fundamental_domain

namespace is_add_fundamental_domain
variables {E G : Type*} [normed_add_comm_group E] [normed_add_comm_group G] [normed_space ℝ E]
  [normed_space ℝ G] [measurable_space E] [measurable_space G] [borel_space E] [borel_space G]
  [finite_dimensional ℝ E] {L : add_subgroup E} {F : set E}

lemma map_linear_equiv (μ : measure E) [is_add_haar_measure μ]
  (fund : is_add_fundamental_domain L F μ) (e : E ≃ₗ[ℝ] G) :
  is_add_fundamental_domain (L.map (e : E →+ G)) (e '' F) (map e μ) :=
begin
  refine fund.image_of_equiv'  e.to_equiv _ (L.equiv_map e).symm.to_equiv (λ g x, _),
  { convert quasi_measure_preserving_map _
      e.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv; ext; refl },
  { simp [←add_equiv.coe_to_equiv_symm, _root_.map_add, add_subgroup.vadd_def, vadd_eq_add] }
end

end is_add_fundamental_domain
end measure_theory

open ennreal finite_dimensional fintype measure_theory measure_theory.measure set topological_space
  topological_space.positive_compacts
open_locale pointwise

namespace measure_theory
variables {ι E : Type*} [fintype ι]

-- TODO: The proof shows that there is a point in the interior of T, perhaps we should expose this
private lemma exists_ne_zero_mem_subgroup_of_volume_mul_two_pow_card_lt_measure
  {L : add_subgroup (ι → ℝ)} [countable L] {F T : set (ι → ℝ)} (μ : measure (ι → ℝ))
  [is_add_haar_measure μ] (fund : is_add_fundamental_domain L F μ) (h : μ F * 2 ^ card ι < μ T)
  (h_symm : ∀ x ∈ T, -x ∈ T) (h_conv : convex ℝ T) :
  ∃ x : L, x ≠ 0 ∧ (x : ι → ℝ) ∈ T :=
begin
  rw [add_haar_measure_unique μ (pi_Icc01 ι), add_haar_measure_eq_volume_pi] at fund,
  have fund_vol : is_add_fundamental_domain L F volume,
  { refine fund.mono (absolutely_continuous.mk $ λ s hs h, _),
    rw [measure.smul_apply, smul_eq_zero] at h,
    -- TODO nice lemma for this?
    exact h.resolve_left (measure_pos_of_nonempty_interior _ (pi_Icc01 _).interior_nonempty).ne' },
  rw [add_haar_measure_unique μ (pi_Icc01 ι), add_haar_measure_eq_volume_pi, measure.smul_apply,
    measure.smul_apply, smul_mul_assoc, smul_eq_mul, smul_eq_mul] at h,
  rw ←measure_interior_of_null_frontier (h_conv.add_haar_frontier volume) at *,
  set S := interior T,
  have h2 : volume F < volume ((2⁻¹ : ℝ) • S),
  { rw [←ennreal.mul_lt_mul_right (pow_ne_zero (card ι) $ two_ne_zero' _) (pow_ne_top two_ne_top),
      add_haar_smul_of_nonneg],
    simpa [ennreal.of_real_pow, ←inv_pow, ←ennreal.of_real_inv_of_pos zero_lt_two, mul_right_comm,
      ←mul_pow, ennreal.inv_mul_cancel _root_.two_ne_zero] using lt_of_mul_lt_mul_left' h,
    positivity },
  rw [←one_smul ℝ T, ←_root_.add_halves (1 : ℝ), one_div, h_conv.add_smul (inv_nonneg.2 zero_le_two)
    (inv_nonneg.2 zero_le_two)],
  obtain ⟨x, hx, y, hy, hne, hsub⟩ := fund_vol.exists_ne_sub_mem
    (measurable_set_interior.const_smul₀ _).null_measurable_set h2,
  refine ⟨⟨y - x, hsub⟩, subtype.ne_of_val_ne $ sub_ne_zero.2 hne.symm, y, -x,
    smul_set_mono interior_subset hy, _, rfl⟩,
  rw mem_inv_smul_set_iff₀ (two_ne_zero' ℝ) at ⊢ hx,
  rw smul_neg,
  exact h_symm _ (interior_subset hx),
end

lemma exists_ne_zero_mem_lattice_of_measure_mul_two_pow_finrank_lt_measure
  [normed_add_comm_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ] {L : add_subgroup E}
  [countable L] {F T : set E} (fund : is_add_fundamental_domain L F μ)
  (h : μ F * 2 ^ finrank ℝ E < μ T) (h_symm : ∀ x ∈ T, -x ∈ T) (h_conv : convex ℝ T) :
  ∃ x ≠ 0, ((x : L) : E) ∈ T :=
begin
  let ι := fin (finrank ℝ E),
  have : finrank ℝ E = finrank ℝ (ι → ℝ), by simp,
  have e : E ≃ₗ[ℝ] ι → ℝ := linear_equiv.of_finrank_eq E (ι → ℝ) this,
  obtain ⟨x, hx, hxT⟩ := exists_ne_zero_mem_subgroup_of_volume_mul_two_pow_card_lt_measure (map e μ)
      (fund.map_linear_equiv μ e) (_ : map e μ (e '' F) * _ < map e μ (e '' T)) _
      (h_conv.linear_image e.to_linear_map),
  { refine ⟨(L.equiv_map e).symm x, (add_equiv_class.map_ne_zero_iff _).2 hx, _⟩,
    simp only [add_subgroup.linear_equiv_map_symm_apply, add_subgroup.coe_mk],
    exact (@set.mem_image_equiv E (ι → ℝ) _ e _).1 hxT },
  { erw [e.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv.map_apply,
      e.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv.map_apply,
      preimage_image_eq _ e.injective, preimage_image_eq _ e.injective, card_fin],
    exact h },
  { rintro _ ⟨x, hx, rfl⟩,
    exact ⟨-x, h_symm _ hx, map_neg _ _⟩ }
end

end measure_theory
