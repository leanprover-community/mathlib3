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

-- TODO: `example : (0 : ℝ≥0∞) < 2 := by positivity` fails

namespace tactic
open positivity
open_locale ennreal

/-- Extension for the `positivity` tactic: raising a positive number in a canonically ordered
semiring gives a positive number. -/
@[positivity]
meta def positivity_canon_pow : expr → tactic strictness
| `(%%r ^ %%n) := do
    typ_n ← infer_type n,
    unify typ_n `(ℕ),
    positive p ← core r,
    positive <$> mk_app ``canonically_ordered_comm_semiring.pow_pos [p, n]
    -- The nonzero never happens because of `tactic.positivity_canon`
| e := pp e >>= fail ∘ format.bracket "The expression `"
    "` is not of the form `r ^ n` for `r : ℝ` and `n : ℕ`"

example {R : Type*} [canonically_ordered_comm_semiring R] {a : R} (h : 0 < a) (n : ℕ) : 0 < a ^ n :=
by positivity

end tactic

instance function.no_zero_smul_divisors {ι α β : Type*} {r : semiring α} {m : add_comm_monoid β}
  [module α β] [no_zero_smul_divisors α β] :
  no_zero_smul_divisors α (ι → β) :=
pi.no_zero_smul_divisors _

@[simp, to_additive]
lemma subgroup.coe_equiv_map_of_injective_symm_apply {G H : Type*} [group G] [group H] (e : G ≃* H)
  {L : subgroup G} {g : L.map (e : G →* H)} {hh} :
  (((L.equiv_map_of_injective _ hh).symm g) : G) = e.symm g :=
begin
  rcases g with ⟨-, h, h_prop, rfl⟩,
  rw [subtype.coe_mk, subtype.coe_eq_iff],
  refine ⟨_, _⟩,
  { simpa only [monoid_hom.coe_coe, mul_equiv.symm_apply_apply] },
  erw [mul_equiv.symm_apply_eq, subtype.ext_iff, subgroup.coe_equiv_map_of_injective_apply,
    subtype.coe_mk, mul_equiv.apply_symm_apply],
end

namespace linear_equiv
variables {𝕜 α β : Type*} [semiring 𝕜] [add_comm_monoid α] [add_comm_monoid β] [module 𝕜 α]
  [module 𝕜 β]

@[simp] lemma symm_comp_self (e : α ≃ₗ[𝕜] β) : e.symm ∘ e = id := e.to_equiv.symm_comp_self
@[simp] lemma self_comp_symm (e : α ≃ₗ[𝕜] β) : e ∘ e.symm = id := e.to_equiv.self_comp_symm

end linear_equiv

namespace measure_theory
open function measure set topological_space

namespace measure
variables {E : Type*} [normed_add_comm_group E] [measurable_space E] [normed_space ℝ E]
  [finite_dimensional ℝ E] [borel_space E] (μ : measure_theory.measure E) [is_add_haar_measure μ]

open finite_dimensional
open_locale pointwise

lemma add_haar_smul_of_nonneg {r : ℝ} (hr : 0 ≤ r) (s : set E) :
  μ (r • s) = ennreal.of_real (r ^ finrank ℝ E) * μ s :=
by rw [add_haar_smul, abs_pow, abs_of_nonneg hr]

end measure

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
      { simp only [← preimage_smul_inv, preimage_preimage, ← hef _ _, e.apply_symm_apply,
          inv_inv] },
      { ext1 x,
        simp only [mem_preimage, ← preimage_smul, ← hef _ _, e.apply_symm_apply, one_smul] }
    end }

@[to_additive measure_theory.is_add_fundamental_domain.image_of_equiv']
lemma image_of_equiv' [measurable_space G]
  [has_measurable_smul G α] [smul_invariant_measure G α μ]
  (h : is_fundamental_domain G s μ)
  (f : α ≃ β) (hf : quasi_measure_preserving f.symm ν μ)
  (e : H ≃ G) (hef : ∀ g, semiconj f ((•) (e g)) ((•) g)) :
  is_fundamental_domain H (f '' s) ν :=
begin
  rw f.image_eq_preimage,
  refine h.preimage_of_equiv' hf e.symm.bijective (λ g x, _),
  rcases f.surjective x with ⟨x, rfl⟩,
  rw [← hef _ _, f.symm_apply_apply, f.symm_apply_apply, e.apply_symm_apply]
end

end is_fundamental_domain

variables {G α β E : Type*} [group G] [measurable_space G]
  [mul_action G α] [measurable_space α]
  [mul_action G β] [measurable_space β]
  [normed_add_comm_group E] {s t : set α} {μ : measure α} {ν : measure β}

-- TODO not needed but maybe useful?
-- @[to_additive is_add_fundamental_domain.image_of_equiv']
-- lemma smul_invariant_measure_map (f : α ≃ β) (hf : measurable f)
--   [smul_invariant_measure G α μ] :
--   smul_invariant_measure G β (μ.map f) :=
-- ⟨begin
--   intros c s hs,
--   simp,
--   rw map_apply hf hs,
--   rw map_apply hf,
--   rw preimage_smul,
--   rw preimage_smul_set,
--   rw measure_preimage_smul,
--   -- simp,
--   -- rw measurable_equiv.map_apply,
-- end⟩

end measure_theory

open_locale ennreal pointwise
open has_inv set function measure_theory measure_theory.measure

-- TODO move to measure_theory.group.basic
namespace measure_theory
variables {α G V : Type*} [measurable_space α] [measurable_space V] {μ : measure α}

open smul_invariant_measure

--TODO given subgroup we don't get has_scalar in the same way as mul_action
@[to_additive]
instance smul_invariant_measure.to_subgroup_smul_invariant_measure {G : Type*} [group G]
  [measurable_space G] (S : subgroup G) [mul_action G V] [has_measurable_smul G V]
  {μ : measure V} [smul_invariant_measure G V μ] :
  smul_invariant_measure S V μ := ⟨λ g A hA, by {convert measure_preimage_smul (g : G) μ A }⟩

-- TODO generalize
@[to_additive]
instance is_mul_left_invariant.to_smul_invariant_measure [measurable_space G] [has_mul G]
  [has_measurable_mul G] {μ : measure G} [h : is_mul_left_invariant μ] :
  smul_invariant_measure G G μ :=
⟨λ g s hs, by simp_rw [smul_eq_mul, ←map_apply (measurable_const_mul g) hs, map_mul_left_eq_self]⟩

end measure_theory

namespace measure_theory
namespace is_fundamental_domain
variables {ι : Type*} [fintype ι] {X Y : Type*} [measure_space Y] [group X] [mul_action X Y]
  {F : set Y} (fund : is_fundamental_domain X F)
include fund

-- @[to_additive]
-- lemma volume_set_eq_tsum_volume_inter [measurable_space X] [has_measurable_smul X Y]
--   [encodable X]
--   {S : set Y} (hS : measurable_set S) [smul_invariant_measure X Y (volume : measure Y)] :
--   ∑' (x : X), volume (x • S ∩ F) = volume S :=
-- begin
--   rw (_ : ∑' (x : X), volume (x • S ∩ F) = ∑' (x : X), volume (x⁻¹ • (x • S ∩ F))),
--   { simp only [smul_set_inter, inv_smul_smul],
--     rw ←measure_Union₀,
--     { library_search,
--       congr,
--       rw [←set.inter_Union, set.inter_eq_self_of_subset_left],
--       convert set.subset_univ _,
--       rw set.eq_univ_iff_forall,
--       intros x,
--       rw set.mem_Union,
--       obtain ⟨l, hl⟩ := fund.ae_covers x,
--       use [l],
--       refine ⟨_, hl, _⟩,
--       rw [inv_smul_smul] },
--     { intros x y hxy,
--       change volume _ = 0,
--       rw inter_assoc,
--       apply measure_inter_null_of_null_right,
--       rw [inter_comm, inter_assoc],
--       apply measure_inter_null_of_null_right,
--       rw ←smul_invariant_measure.volume_smul y,
--         -- ((F.measurable_set_smul y⁻¹).inter (F.measurable_set_smul x⁻¹)),
--       rw [smul_set_inter, smul_inv_smul],
--       -- simp [smul_set_inter, smul_inv_smul],
--       rw [smul_smul],
--       apply measure_mono_null (F.domain.inter_subset_inter_right _) F.almost_disjoint,
--       intros t ht,
--       rw mem_Union,
--       use y * x⁻¹,
--       rw [ne.def, mul_inv_eq_one, mem_Union],
--       exact ⟨hxy.symm, ht⟩,
--       apply_instance,
--       apply_instance },
--     { intro l,
--       simp,
--       exact hS.inter (F.measurable_set_smul l⁻¹) } },
--   { congr,
--     ext1 l,
--     rw h_smul_left.volume_smul,
--     exact (_root_.measurable_set_smul l hS).inter F.measurable_set_domain }
-- end

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
  [finite_dimensional ℝ E] [finite_dimensional ℝ G] {L : add_subgroup E} {F : set E}

lemma map_linear_equiv (μ : measure E) [is_add_haar_measure μ]
  (fund : is_add_fundamental_domain L F μ) (e : E ≃ₗ[ℝ] G) :
  is_add_fundamental_domain (L.map (e : E →+ G)) (e '' F) (map e μ) :=
begin
  refine fund.image_of_equiv'  e.to_equiv _ _ (λ g x, _),
  { refine ⟨_, _⟩, -- TODO lemma
    convert e.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv.symm.measurable,
    ext,
    refl,
    simp only [linear_equiv.coe_to_equiv_symm],
    rw [map_map, e.symm_comp_self, map_id],
    convert e.symm.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv.measurable,
    convert e.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv.measurable,
    ext,
    refl },
  { refine ((L.equiv_map_of_injective _ _).symm.to_equiv : L.map (e : E →+ G) ≃ L),
    exact e.injective },
  { simp only [add_subgroup.vadd_def, add_equiv.to_equiv_symm, add_equiv.to_equiv_eq_coe,
      vadd_eq_add, linear_equiv.coe_to_equiv, _root_.map_add, _root_.add_left_inj],
    refine e.symm.injective _,
    simp only [add_equiv.coe_to_equiv, linear_equiv.symm_apply_apply],
    convert add_subgroup.coe_equiv_map_of_injective_symm_apply e.to_add_equiv,
    exact e.injective }
end

end is_add_fundamental_domain

open fintype

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

end measure_theory

open ennreal finite_dimensional fintype measure_theory measure_theory.measure set topological_space
  topological_space.positive_compacts

variables {ι : Type*} [fintype ι]

-- TODO: The proof shows that there is a point in the interior of T, perhaps we should expose this
lemma exists_ne_zero_mem_subgroup_of_volume_mul_two_pow_card_lt_measure {L : add_subgroup (ι → ℝ)}
  [countable L] {F T : set (ι → ℝ)} (μ : measure (ι → ℝ)) [is_add_haar_measure μ]
  (fund : is_add_fundamental_domain L F μ) (h : μ F * 2 ^ card ι < μ T) (h_symm : ∀ x ∈ T, -x ∈ T)
  (h_conv : convex ℝ T) :
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
  rw ← measure_interior_of_null_frontier (h_conv.add_haar_frontier volume) at *,
  set S := interior T,
  have h2 : volume F < volume ((2⁻¹ : ℝ) • S),
  { have : (0 : ℝ) ≤ 2⁻¹, by norm_num,
    rw [←ennreal.mul_lt_mul_right (pow_ne_zero (card ι) two_ne_zero') (pow_ne_top two_ne_top),
      add_haar_smul_of_nonneg],
    simpa [ennreal.of_real_pow, ←inv_pow, ←ennreal.of_real_inv_of_pos zero_lt_two, mul_right_comm,
      ←mul_pow, inv_mul_cancel _root_.two_ne_zero] using lt_of_mul_lt_mul_left' h,
    positivity },
  rw [←one_smul ℝ T, ←_root_.add_halves (1 : ℝ), one_div, h_conv.add_smul (inv_nonneg.2 zero_le_two)
    (inv_nonneg.2 zero_le_two)],
  obtain ⟨x, hx, y, hy, hne, hsub⟩ := fund_vol.exists_ne_sub_mem
    (measurable_set_interior.const_smul₀ _).null_measurable_set h2,
  refine ⟨⟨y - x, hsub⟩, subtype.ne_of_val_ne $ sub_ne_zero.2 hne.symm, y, -x,
    smul_set_mono interior_subset hy, _, rfl⟩,
  rw mem_inv_smul_set_iff₀ (@_root_.two_ne_zero ℝ _ _) at ⊢ hx,
  rw smul_neg,
  exact h_symm _ (interior_subset hx),
end

lemma exists_nonzero_mem_lattice_of_measure_mul_two_pow_finrank_lt_measure
  {E : Type*} [normed_add_comm_group E] [normed_space ℝ E] [measurable_space E] [borel_space E]
  [finite_dimensional ℝ E] (μ : measure E) [is_add_haar_measure μ] {L : add_subgroup E}
  [countable L] {F T : set E} (fund : is_add_fundamental_domain L F μ)
  (h : μ F * 2 ^ finrank ℝ E < μ T) (h_symm : ∀ x ∈ T, -x ∈ T) (h_conv : convex ℝ T) :
  ∃ (x : L) (h : x ≠ 0), (x : E) ∈ T :=
begin
  let ι := fin (finrank ℝ E),
  have : finrank ℝ E = finrank ℝ (ι → ℝ), by simp,
  have e : E ≃ₗ[ℝ] ι → ℝ := linear_equiv.of_finrank_eq E (ι → ℝ) this,
  have hfund : is_add_fundamental_domain (L.map (e : E →+ ι → ℝ)) (e '' F) (map e μ),
  { convert fund.map_linear_equiv μ e },
  haveI : countable (L.map (e : E →+ ι → ℝ)),
  { refine (L.equiv_map_of_injective _ _).symm.injective.countable,
    exact equiv_like.injective e },
  obtain ⟨x, hx, hxT⟩ :=
    exists_ne_zero_mem_subgroup_of_volume_mul_two_pow_card_lt_measure (map e μ) hfund
      (_ : map e μ (e '' F) * _ < map e μ (e '' T)) _
      (h_conv.linear_image e.to_linear_map),
  { refine ⟨(L.equiv_map_of_injective _ _).symm x, _, _⟩,
    { exact equiv_like.injective e },
    { simp only [hx, ne.def, add_equiv_class.map_eq_zero_iff, not_false_iff, exists_true_left] },
    erw add_subgroup.coe_equiv_map_of_injective_symm_apply e.to_add_equiv,
    exact mem_image_equiv.mp hxT },
  { erw [measurable_equiv.map_apply e.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv,
      measurable_equiv.map_apply e.to_continuous_linear_equiv.to_homeomorph.to_measurable_equiv,
      preimage_image_eq _ e.injective, preimage_image_eq _ e.injective],
    convert h,
    simp [ι] },
  { rintro _ ⟨x, hx, rfl⟩,
    exact ⟨-x, h_symm _ hx, map_neg _ _⟩ }
end
