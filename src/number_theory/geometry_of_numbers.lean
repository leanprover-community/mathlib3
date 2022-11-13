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
-/

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
  { convert h_prop,
    erw [mul_equiv.symm_apply_apply] },
  erw [mul_equiv.symm_apply_eq, subtype.ext_iff, subgroup.coe_equiv_map_of_injective_apply,
    subtype.coe_mk, mul_equiv.apply_symm_apply],
end

namespace set
variables {ι : Type*} {α β : ι → Type*}

lemma preimage_pi (s : set ι) (t : Π i, set (β i)) (f : Π i, α i → β i) :
  (λ (g : Π i, α i) i, f _ (g i)) ⁻¹' univ.pi t = univ.pi (λ i, f i ⁻¹' t i) := rfl

end set

namespace linear_equiv
variables {𝕜 α β : Type*} [semiring 𝕜] [add_comm_monoid α] [add_comm_monoid β] [module 𝕜 α]
  [module 𝕜 β]

@[simp] lemma symm_comp_self (e : α ≃ₗ[𝕜] β) : e.symm ∘ e = id := e.to_equiv.symm_comp_self
@[simp] lemma self_comp_symm (e : α ≃ₗ[𝕜] β) : e ∘ e.symm = id := e.to_equiv.self_comp_symm

end linear_equiv

namespace measure_theory
open function measure set topological_space

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

section
variables {G H α β E : Type*} [group G] [group H]
  [mul_action G α] [measurable_space α]
  [mul_action H β] [measurable_space β]
  [normed_add_comm_group E] {s t : set α} {μ : measure α} {ν : measure β}

@[to_additive is_add_fundamental_domain.preimage_of_equiv']
lemma is_fundamental_domain.preimage_of_equiv' [measurable_space H]
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

@[to_additive is_add_fundamental_domain.image_of_equiv']
lemma is_fundamental_domain.image_of_equiv' [measurable_space G]
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

end

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
⟨λ g s hs,
  by simp_rw [smul_eq_mul, ← measure.map_apply (measurable_const_mul g) hs, map_mul_left_eq_self]⟩

end measure_theory

noncomputable theory
open set topological_space

variables {ι : Type*} [fintype ι]

-- /-- A fundamental domain for an additive group acting on a measure space. -/
-- structure add_fundamental_domain (Y X : Type*) [measure_space Y] [add_group X] [has_vadd X Y] :=
-- (domain : set Y)
-- (measurable_set_domain : measurable_set domain)
-- (almost_disjoint : volume (domain ∩ ⋃ (l : X) (h : l ≠ 0), (l +ᵥ domain)) = 0)
-- (covers : ∀ (y : Y), ∃ (l : X), l +ᵥ y ∈ domain)
-- --TODO should these be set_like or something?

-- /-- A fundamental domain for a group acting on a measure space. -/
-- @[to_additive add_fundamental_domain, nolint has_inhabited_instance]
-- structure fundamental_domain (Y X : Type*) [measure_space Y] [group X] [has_scalar X Y] :=
-- (domain : set Y)
-- (measurable_set_domain : measurable_set domain)
-- (almost_disjoint : volume (domain ∩ ⋃ (l : X) (h : l ≠ 1), l • domain) = 0)
-- (covers : ∀ (y : Y), ∃ (l : X), l • y ∈ domain)

namespace measure_theory
namespace is_fundamental_domain
variables {X Y : Type*} [measure_space Y] [group X] [mul_action X Y] {F : set Y}
  (fund : is_fundamental_domain X F)
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
end measure_theory

--TODO all f.d.s have same measure https://arxiv.org/pdf/1405.2119.pdf
-- TODO fin index subgroup has given fundamental domain and covolume
-- TODO some existence result? in presence of metric? voronoi

-- instance : inhabited (is_add_fundamental_domain (fin 0 → ℝ) (fin 0 → ℝ)) :=
-- { default := { domain := ⊤,
--   measurable_set_domain := subsingleton.measurable_set,
--   almost_disjoint := by simp,
--   covers := λ v, by simp } }

open measure_theory

-- TODO: Prove version giving `⌈volume S / volume F⌉` points whose difference is in a subgroup
-- needs the `m`-fold version of `exists_nonempty_inter_of_measure_univ_lt_tsum_measure` when
-- measure > m * measure giving some x in m sets
@[to_additive]
lemma exists_mul_inv_mem_lattice_of_volume_lt_volume {X : Type*} [measure_space X] [group X]
  [has_measurable_mul X] (L : subgroup X) [countable L] {S : set X} (hS : null_measurable_set S)
  {F : set X} (fund : is_fundamental_domain L F) (hlt : volume F < volume S)
  [is_mul_left_invariant (volume : measure X)] :
  ∃ (x y ∈ S), x ≠ y ∧ y * x⁻¹ ∈ L :=
let ⟨x, hx, y, hy, g, hg, rfl⟩ := fund.exists_ne_one_smul_eq hS hlt in
  by refine ⟨x, hx, _, hy, _, _⟩; simp [subgroup.smul_def]; assumption

open measure_theory measure_theory.measure topological_space set fintype

lemma rescale (ι : Type*) [fintype ι] {r : ℝ} (hr : 0 < r) :
  measure.comap ((•) r) (volume : measure (ι → ℝ)) =
  ennreal.of_real r ^ card ι • (volume : measure (ι → ℝ)) :=
begin
  have hrzero : ennreal.of_real r ≠ 0,
  { intro h,
    rw ennreal.of_real_eq_zero at h,
    linarith },
  have hrtop : ennreal.of_real r ≠ ⊤, from ennreal.of_real_ne_top,
  suffices : (ennreal.of_real r)⁻¹ ^ card ι •
    measure.comap ((•) r) (volume : measure (ι → ℝ)) = volume,
  { conv_rhs { rw ←this },
    rw [smul_smul, ←mul_pow, ennreal.mul_inv_cancel hrzero hrtop],
    simp only [one_pow, one_smul] },
  refine (pi_eq $ λ s hS, _).symm,
  simp only [algebra.id.smul_eq_mul, measure.coe_smul, pi.smul_apply],
  rw [comap_apply, image_smul, smul_univ_pi],
  { erw pi_pi,
    dsimp,
    conv in (r • _)
    { rw ←inv_inv r },
    conv in (volume (r⁻¹⁻¹ • _))
    { rw ←preimage_smul₀ (inv_ne_zero (ne_of_gt hr)) },
    simp only [algebra.id.smul_eq_mul],
    rw [fintype.card, ←finset.prod_const, ←finset.prod_mul_distrib],
    congr' with i,
    erw ←measure.map_apply (measurable_const_mul r⁻¹) (hS i),
    conv_rhs { rw ←real.smul_map_volume_mul_left (inv_ne_zero hr.ne') },
    rw [ennreal.of_real_inv_of_pos hr, abs_of_pos (inv_pos.mpr hr)],
    refl },
  { exact smul_right_injective (ι → ℝ) hr.ne' },
  { exact λ S hS, hS.const_smul₀ r },
  { exact measurable_set.univ_pi hS }
end

open ennreal topological_space.positive_compacts

-- TODO version for any real vector space in terms of dimension
-- actually the proof shows that there is a point in the interior of T, perhaps we should expose
-- this
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
  have hS : measurable_set (interior T) := measurable_set_interior,
  rw ← measure_interior_of_null_frontier (h_conv.add_haar_frontier volume) at *,
  set S := interior T,
  have : volume ((2⁻¹ : ℝ) • S) * 2 ^ card ι = volume S,
  { suffices : volume ((2⁻¹ : ℝ) • S) = 2⁻¹ ^ card ι * volume S,
    { rw [this, mul_comm _ (volume S), mul_assoc, ←mul_pow,
        ennreal.inv_mul_cancel ennreal.two_ne_zero two_ne_top, one_pow, mul_one] },
    have := rescale ι (inv_pos_of_pos two_pos),
    rw ←ennreal.of_real_inv_of_pos (two_pos : 0 < (2 : ℝ)) at this,
    simp only [zero_le_one, of_real_one, of_real_bit0] at this,
    rw [←smul_eq_mul, ←measure.smul_apply, ←this, comap_apply _ _ _ _ hS, image_smul],
    { exact smul_right_injective _ (by norm_num) },
    intros S hS,
    rw [image_smul, ←preimage_smul₀],
    { exact measurable_id'.const_smul _ hS },
    { exact two_ne_zero } },
  have h2 : volume F < volume ((2⁻¹ : ℝ) • S),
  { rw ←ennreal.mul_lt_mul_right (pow_ne_zero (card ι) two_ne_zero') (pow_ne_top two_ne_top),
    convert lt_of_mul_lt_mul_left' h },
  rw [←one_smul ℝ T, ←_root_.add_halves (1 : ℝ), one_div, h_conv.add_smul (inv_nonneg.2 zero_le_two)
    (inv_nonneg.2 zero_le_two)],
  obtain ⟨x, hx, y, hy, hne, hsub⟩ := exists_add_neg_mem_lattice_of_volume_lt_volume
    L (hS.const_smul₀ _).null_measurable_set fund_vol h2,
  refine ⟨⟨y - x, hsub⟩, subtype.ne_of_val_ne $ sub_ne_zero.2 hne.symm, y, -x,
    smul_set_mono interior_subset hy, _, rfl⟩,
  rw mem_inv_smul_set_iff₀ (@_root_.two_ne_zero ℝ _ _) at ⊢ hx,
  rw smul_neg,
  exact h_symm _ (interior_subset hx),
end

open finite_dimensional

lemma measure_theory.is_add_fundamental_domain.map_linear_equiv
  {E G : Type*} [normed_add_comm_group E] [normed_add_comm_group G] [normed_space ℝ E]
  [normed_space ℝ G] [measurable_space E] [measurable_space G] [borel_space E] [borel_space G]
  [finite_dimensional ℝ E] [finite_dimensional ℝ G] (μ : measure E) [is_add_haar_measure μ]
  {L : add_subgroup E} {F : set E} (fund : is_add_fundamental_domain L F μ) (e : E ≃ₗ[ℝ] G) :
  is_add_fundamental_domain (L.map (e : E →+ G)) (e '' F) (map e μ) :=
begin
  refine is_add_fundamental_domain.image_of_equiv' fund e.to_equiv _ _ _,
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
    change injective e,
    exact equiv_like.injective _ },
  { intros g x,
    simp only [add_subgroup.vadd_def, add_equiv.to_equiv_symm, add_equiv.to_equiv_eq_coe,
      vadd_eq_add, linear_equiv.coe_to_equiv, _root_.map_add, _root_.add_left_inj],
    apply_fun e.symm,
    simp only [add_equiv.coe_to_equiv, linear_equiv.symm_apply_apply],
    convert add_subgroup.coe_equiv_map_of_injective_symm_apply e.to_add_equiv,
    change injective e,
    exact equiv_like.injective _,
    exact equiv_like.injective _ }
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
  have hfund : is_add_fundamental_domain (L.map (e : E →+ ι → ℝ)) ((e : E → ι → ℝ) '' F) (map e μ)
    := by convert fund.map_linear_equiv μ e,
  haveI : countable (L.map (e : E →+ ι → ℝ)),
  { refine (L.equiv_map_of_injective _ _).symm.injective.countable,
    exact equiv_like.injective e },
  obtain ⟨x, hx, hxT⟩ :=
    exists_ne_zero_mem_subgroup_of_volume_mul_two_pow_card_lt_measure (map e μ) hfund
      (_ : (map e μ) ((e : E → ι → ℝ) '' F) * _ < (map e μ) ((e : E → ι → ℝ) '' T)) _
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
