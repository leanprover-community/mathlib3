/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.module.pointwise_pi
import measure_theory.group.fundamental_domain
import analysis.convex.measure

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as studied by
Hermann Minkowski.

## Main results

- `exists_sub_mem_lattice_of_volume_lt_volume`: Blichfeldt's principle, existence of two points
  within a set whose difference lies in a subgroup when the covolume of the subgroup is larger than
  the set.
- `exists_nonzero_mem_lattice_of_volume_mul_two_pow_card_lt_volume`: Minkowski's theorem, existence
  of a non-zero lattice point inside a convex symmetric domain of large enough covolume.
-/

namespace measure_theory
variables {α : Type*} (μ : outer_measure α)

@[simp] lemma outer_measure.measure_Union_null_iff' {ι : Prop} {s : ι → set α} :
  μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 :=
by by_cases i : ι; simp [i]

@[simp] lemma measure.measure_Union_null_iff' [measurable_space α] {μ : measure α} {ι : Prop}
  {s : ι → set α} : μ (⋃ i, s i) = 0 ↔ ∀ i, μ (s i) = 0 :=
μ.to_outer_measure.measure_Union_null_iff'

end measure_theory


open measure_theory measure_theory.measure set topological_space
open_locale pointwise
section
-- TODO move to measure_theory.group.basic
noncomputable theory

open_locale ennreal pointwise
open has_inv set function measure_theory.measure
section
end
variables {α : Type*} [measurable_space α] {μ : measure α}

namespace measure_theory

variables {G V : Type*}

section

variables [measurable_space V]

open smul_invariant_measure
-- #check smul_invaria.nt_measure.measure_preimage_smul
--TODO given subgroup we don't get has_scalar in the same way as mul_action
@[to_additive]
instance smul_invariant_measure.to_subgroup_smul_invariant_measure {G : Type*} [group G]
  [measurable_space G] (S : subgroup G) [mul_action G V] [has_measurable_smul G V]
  {μ : measure V} [smul_invariant_measure G V μ] :
  smul_invariant_measure S V μ := ⟨λ g A hA, by {convert measure_preimage_smul (g : G) μ A }⟩

@[to_additive]
lemma smul_invariant_measure.volume_smul {G : Type*} [group G] [measurable_space G] [mul_action G V]
  [has_measurable_smul G V] {μ : measure V}
  [smul_invariant_measure G V μ] (g : G) {S : set V} : μ (g • S) = μ S :=
by rw [←measure_preimage_smul (g⁻¹) μ S, preimage_smul, inv_inv]

-- @[to_additive]
-- lemma is_mul_left_invariant.to_smul_invariant_measure [measurable_space G] [has_mul G]
--   {μ : measure G} [is_mul_left_invariant μ] :
-- smul_invariant_measure G G μ := ⟨h⟩

end
end measure_theory
end

section
variables {X Y : Type*} [measure_space Y] [group X] [mul_action X Y] [measurable_space X]
  [has_measurable_smul X Y]

@[to_additive]
lemma measurable_set.smul (x : X) {S : set Y} (h : measurable_set S) : measurable_set (x • S) :=
by { rw [←inv_inv x, ←preimage_smul (x⁻¹)], exact has_measurable_smul.measurable_const_smul _ h }

end

section
variables {X Y : Type*} [measure_space Y] [group_with_zero X] [mul_action X Y]
  [measurable_space X] [has_measurable_smul X Y] {S : set Y} {x : X}

lemma measurable_set_smul₀ (hx : x ≠ 0) (h : measurable_set S) : measurable_set (x • S) :=
begin
  rw [←inv_inv x, ←preimage_smul₀ (inv_ne_zero hx)],
  exact has_measurable_smul.measurable_const_smul _ h,
end

end

section
variables {X Y : Type*} [measure_space Y] [group_with_zero X] [measurable_space X]

lemma measurable_set_smul₀_of_measurable_singleton_class [has_zero Y] [mul_action_with_zero X Y]
  [measurable_singleton_class Y] [has_measurable_smul X Y]
  {x : X} {S : set Y} (h : measurable_set S) :
  measurable_set (x • S) :=
begin
  by_cases hx : x = 0,
  { by_cases hS : S.nonempty,
    { rw [hx, zero_smul_set hS],
      exact measurable_set_singleton 0 },
    { convert measurable_set.empty,
      rw not_nonempty_iff_eq_empty at hS,
      rw hS,
      simp } },
  { exact measurable_set_smul₀ hx h }
end

end

variables (ι : Type*) [fintype ι]
noncomputable theory
open set

lemma is_add_left_invariant_pi_volume {K : ι → Type*} [Π i, measure_space (K i)]
  [Π i, add_group (K i)] [∀ i, has_measurable_add (K i)] -- TODO???
  [∀ i, sigma_finite (volume : measure (K i))]
  [∀ i, is_add_left_invariant (volume : measure (K i))] :
  is_add_left_invariant ((volume : measure (Π i, K i))) :=
begin
  constructor,
  refine λ v, (pi_eq $ λ s hs, _).symm,
  rw [map_apply, volume_pi],
  rw (_ : (+) v ⁻¹' (univ : set _).pi s = (univ : set _).pi (λ (i : ι), (+) (v i) ⁻¹' (s i))),
  { rw pi_pi,
    { congr',
      ext i : 1,
      exact measure_preimage_add _ _ _, }, },
  { refl, },
  { exact measurable_const_add v, },
  { exact measurable_set.univ_pi hs, },
end

/-- The closed unit cube with sides the intervals [0,1] as a positive compact set, for inducing the
    Haar measure equal to the lebesgue measure on ℝ^n. -/
def unit_cube : positive_compacts (ι → ℝ) :=
{ carrier := Icc 0 1,
  compact' := by { rw ←pi_univ_Icc, exact is_compact_univ_pi (λ i, is_compact_Icc) },
  interior_nonempty' := begin
    simp_rw [←pi_univ_Icc, pi.zero_apply, pi.one_apply, interior_pi_set finite_univ, interior_Icc,
      univ_pi_nonempty_iff],
    exact λ i, nonempty_Ioo.2 zero_lt_one,
  end }

@[simp] lemma coe_unit_cube : (unit_cube ι : set (ι → ℝ)) = Icc 0 1 := rfl

lemma volume_Icc : volume (Icc 0 1 : set (ι → ℝ)) = 1 :=
begin
  simp_rw [←pi_univ_Icc, pi.zero_apply, pi.one_apply],
  rw [volume_pi_pi, real.volume_Icc, sub_zero, ennreal.of_real_one, finset.prod_const_one],
end

lemma pi_haar_measure_eq_lebesgue_measure : add_haar_measure (unit_cube ι) = volume :=
begin
  convert (add_haar_measure_unique _ (unit_cube ι)).symm,
  { rw [coe_unit_cube, volume_Icc, one_smul] },
  { apply_instance },
  { exact is_add_left_invariant_pi_volume ι }
end

variable {ι}

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

/-- The boundary of a fundamental domain, those points of the domain that also lie in a nontrivial
translate. -/
@[nolint unused_arguments, to_additive "The boundary of a fundamental domain, those points of the
domain that also lie in a nontrivial translate."]
protected def boundary : set Y := F ∩ ⋃ (l : X) (h : l ≠ 1), l • F

/-- The interior of a fundamental domain, those points of the domain not lying in any translate. -/
@[nolint unused_arguments, to_additive "The interior of a fundamental domain, those points of the
domain not lying in any translate."]
protected def interior : set Y := F \ ⋃ (l : X) (h : l ≠ 1), l • F

@[to_additive] lemma disjoint_interior_boundary : disjoint fund.interior fund.boundary :=
disjoint_sdiff_self_left.mono_right inf_le_right

@[simp, to_additive] lemma interior_union_boundary : fund.interior ∪ fund.boundary = F :=
diff_union_inter _ _

@[simp, to_additive] lemma sdiff_interior : F \ fund.interior = fund.boundary :=
sdiff_sdiff_right_self

@[simp, to_additive] lemma sdiff_boundary : F \ fund.boundary = fund.interior := diff_self_inter

variables [encodable X]

@[to_additive] lemma volume_boundary : volume fund.boundary = 0 :=
by simpa only [is_fundamental_domain.boundary, Union₂_inter, measure_Union_null_iff',
  measure_Union_null_iff, inter_comm F] using fund.ae_disjoint

@[to_additive] lemma volume_interior : volume fund.interior = volume F :=
measure_diff_null' fund.volume_boundary

variables [measurable_space X] [has_measurable_smul X Y] [smul_invariant_measure X Y volume]

@[to_additive] lemma null_measurable_set_nontrivial_translates :
  null_measurable_set (⋃ (l : X) (h : l ≠ 1), l • F) :=
begin
  refine null_measurable_set.Union (λ b, _),
  obtain rfl | hb := eq_or_ne b 1,
  { simp },
  { simp only [hb, set.Union_true, ne.def, not_false_iff],
    exact fund.null_measurable_set.smul _ }
end

@[to_additive] lemma null_measurable_set_boundary : null_measurable_set fund.boundary :=
fund.null_measurable_set.inter fund.null_measurable_set_nontrivial_translates

@[to_additive] lemma null_measurable_set_interior : null_measurable_set fund.interior :=
fund.null_measurable_set.diff fund.null_measurable_set_nontrivial_translates

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

-- instance subtype.measure_space {V : Type*} [measure_space V] {p : set V} :
--   measure_space (subtype p) :=
-- { volume := measure.comap subtype.val volume,
--   ..subtype.measurable_space }

-- lemma volume_subtype_univ {V : Type*} [measure_space V] {p : set V} (hmp : measurable_set p) :
--   volume (set.univ : set (subtype p)) = volume p :=
-- begin
--   dsimp only [measure_space.volume],
--   rw [measure.comap_apply _ subtype.val_injective, set.image_univ],
--   { congr,
--     exact subtype.range_val, },
--   { intros x,
--     exact measurable_set.subtype_image hmp, },
--   { exact measurable_set.univ, }
-- end

namespace subtype


variables {V : Type*} [measure_space V] {p : V → Prop}
variables [measure_space V] {s t : set V}

lemma volume_def {s : set V} : (volume : measure s) = volume.comap subtype.val := rfl


lemma measurable_set.null_measurable_set_subtype_image {s : set V} {t : set s}
  (hs : null_measurable_set s) (ht : measurable_set t) :
  null_measurable_set ((coe : s → V) '' t) :=
sorry

open function
lemma comap_apply₀ {α β} {s} [measurable_space α] {mβ : measurable_space β} (f : α → β)
  (μ : measure β)
  (hfi : injective f) (hf : ∀ s, measurable_set s → null_measurable_set (f '' s) μ)
  (hs : measurable_set s) :
comap f μ s = μ (f '' s) := sorry

@[simp] lemma volume_preimage_coe (hs : null_measurable_set s) (ht : measurable_set t) :
  volume ((coe : s → V) ⁻¹' t) = volume (t ∩ s) :=
begin
  dsimp only [measure_space.volume],
  rw [comap_apply₀ _ _ subtype.coe_injective
    (λ h, measurable_set.null_measurable_set_subtype_image hs) (measurable_subtype_coe ht),
    image_preimage_eq_inter_range, subtype.range_coe],
end

@[simp] lemma volume_univ (hs : null_measurable_set s) : volume (univ : set s) = volume s :=
(volume_preimage_coe hs measurable_set.univ).trans $ by rw univ_inter

end subtype
open measure_theory

/-- **Blichfeldt's Principle** --/
@[to_additive "**Blichfeldt's Principle**"]
lemma exists_mul_inv_mem_lattice_of_volume_lt_volume {X Y : Type*} [measurable_space X]
  [measure_space Y] [group X] [mul_action X Y] [has_measurable_smul X Y] [encodable X] {S : set Y}
  (hS : measurable_set S) (F : set Y) (fund : is_fundamental_domain X F) (hlt : volume F < volume S)
  [smul_invariant_measure X Y volume]
  (hnostab : ∀ (p₁ p₂ : X) (q : Y) (hq : q ∈ S) (hppq : p₁ • q = p₂ • q), p₁ = p₂) :
  ∃ (x y : Y) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y), y ∈ (• x) '' (univ : set X) :=
begin
  suffices : ∃ (p₁ p₂ : X) (hne : p₁ ≠ p₂), ((p₁ • S ∩ F) ∩ (p₂ • S ∩ F)).nonempty,
  { obtain ⟨p₁, p₂, hne, u, ⟨⟨q₁, hS₁, ht₁⟩, hu⟩, ⟨q₂, hS₂, ht₂⟩, hu⟩ := this,
    refine ⟨q₁, q₂, hS₁, hS₂, _, p₂⁻¹ * p₁, mem_univ _, _⟩,
    { rintro rfl,
      rw ←ht₂ at *,
      exact hne (hnostab _ _ _ hS₁ ht₁) },
    { simp only,
      rw [mul_smul, ht₁, ←ht₂, inv_smul_smul] } },
  refine Exists₃.imp _ (exists_nonempty_inter_of_measure_univ_lt_tsum_measure
    (set_coe.measure_space _).volume (_ : (∀ p : X, measurable_set ((coe : F → Y) ⁻¹' (p • S)))) _),
  { exact λ i j hij ⟨x, hi, hj⟩, ⟨x, ⟨hi, x.2⟩, hj, x.2⟩ },
  { exact λ p, measurable_id'.subtype_coe (hS.smul p) },
  rw ←subtype.volume_univ fund.null_measurable_set at hlt,
  simp_rw subtype.volume_preimage_coe fund.null_measurable_set (hS.smul _),
  exact hlt.trans_eq (fund.measure_eq_tsum _),
end

-- TODO version giving `⌈volume S / volume F⌉` points whose difference is in a subgroup
-- needs the m-fold version of exists_nonempty_inter_of_measure_univ_lt_tsum_measure when
-- measure > m * measure giving some x in m sets
@[to_additive]
lemma exists_mul_inv_mem_lattice_of_volume_lt_volume' {X : Type*} [measure_space X] [group X]
  [has_measurable_mul X] (L : subgroup X) [encodable L] {S : set X} (hS : measurable_set S)
  {F : set X} (fund : is_fundamental_domain L F) (hlt : volume F < volume S)
  -- [smul_invariant_measure X Y (volume : measure Y)]
  [is_mul_left_invariant (volume : measure X)] :
  ∃ (x y : X) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y), y * x⁻¹ ∈ L :=
begin
  haveI : smul_invariant_measure L X measure_space.volume,
  { apply smul_invariant_measure.to_subgroup_smul_invariant_measure L,
    apply_instance,
    constructor,
    intros c S hS,
    exact measure_preimage_mul volume c S },
  obtain ⟨x, y, hx, hy, hne, h⟩ := exists_mul_inv_mem_lattice_of_volume_lt_volume hS F fund hlt _,
  { refine ⟨x, y, hx, hy, hne, _⟩,
    simp only [image_univ, mem_range] at h,
    obtain ⟨l, rfl⟩ := h,
    simp [subgroup.smul_def] },
  -- { exact smul_invariant_measure.to_subgroup_smul_invariant_measure _  },
  { rintro ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ q hq hleft,
    simpa [subgroup.smul_def] using hleft }
end

open measure_theory measure_theory.measure topological_space set

lemma rescale (ι : Type*) [fintype ι] {r : ℝ} (hr : 0 < r) :
  measure.comap ((•) r) (volume : measure (ι → ℝ)) =
  (ennreal.of_real r) ^ (fintype.card ι) • (volume : measure (ι → ℝ)) :=
begin
  have hrzero : ennreal.of_real r ≠ 0,
  { intro h,
    rw ennreal.of_real_eq_zero at h,
    linarith },
  have hrtop : ennreal.of_real r ≠ ⊤, from ennreal.of_real_ne_top,
  suffices : (1 / ennreal.of_real r) ^ (fintype.card ι) •
    measure.comap ((•) r) (volume : measure (ι → ℝ)) = (volume : measure (ι → ℝ)),
  { conv_rhs { rw ←this },
    rw [one_div, smul_smul, ←mul_pow, ennreal.mul_inv_cancel hrzero hrtop],
    simp only [one_pow, one_smul] },
  refine (pi_eq $ λ s hS, _).symm,
  simp only [one_div, algebra.id.smul_eq_mul, coe_smul, pi.smul_apply],
  rw [comap_apply, image_smul, smul_univ_pi],
  { erw pi_pi,
    dsimp,
    conv in (r • _)
    { rw ←inv_inv r },
    conv in (volume (r⁻¹⁻¹ • _))
    { rw ←preimage_smul₀ (inv_ne_zero (ne_of_gt hr)) },
    simp only [algebra.id.smul_eq_mul],
    rw [fintype.card, ←finset.prod_const, ←finset.prod_mul_distrib],
    congr,
    ext i : 1,
    erw ←measure.map_apply (measurable_const_mul r⁻¹) (hS i),
    conv_rhs { rw [←real.smul_map_volume_mul_left (inv_ne_zero (ne_of_gt hr))] },
    rw [ennreal.of_real_inv_of_pos hr, abs_of_pos (inv_pos.mpr hr)],
    refl },
  { exact smul_right_injective (ι → ℝ) (ne_of_gt hr) },
  { exact λ S hS, hS.const_smul₀ r },
  { exact measurable_set.univ_pi hS }
end

open ennreal fintype

-- TODO version for any real vector space in terms of dimension
lemma exists_nonzero_mem_lattice_of_volume_mul_two_pow_card_lt_volume {L : add_subgroup (ι → ℝ)}
  [encodable L] {F T : set (ι → ℝ)} (fund : is_add_fundamental_domain L F)
  (h : volume F * 2 ^ (card ι) < volume T) (h_symm : has_neg.neg '' T ⊆ T) (h_conv : convex ℝ T) :
  ∃ (x : L) (h : x ≠ 0), (x : ι → ℝ) ∈ T :=
begin
  have hS : measurable_set (interior T) := measurable_set_interior,
  rw ← measure_interior_of_null_frontier (h_conv.add_haar_frontier measure_space.volume) at *,
  set S := interior T,
  have mhalf : measurable_set ((1/2 : ℝ) • S),
  { convert measurable_const_smul (2 : ℝ) hS,
    ext x,
    simp only [one_div, set.mem_preimage],
    exact mem_inv_smul_set_iff₀ two_ne_zero _ x },
  have : volume ((1/2 : ℝ) • S) * 2 ^ (card ι) = volume S,
  { suffices : volume ((1/2 : ℝ) • S) = (1 / 2) ^ (card ι) * volume S,
    { rw [this, mul_comm _ (volume S), mul_assoc, ←mul_pow, one_div,
        ennreal.inv_mul_cancel two_ne_zero two_ne_top, one_pow, mul_one] },
    have := rescale ι (half_pos zero_lt_one),
    simp only [one_div, fintype.card_fin] at this ⊢,
    rw ←ennreal.of_real_inv_of_pos (by norm_num : 0 < (2 : ℝ)) at this,
    simp only [zero_le_one, of_real_one, of_real_bit0] at this,
    rw [←smul_eq_mul, ←measure.smul_apply, ←this, comap_apply _ _ _ _ hS],
    { simp },
    { exact smul_right_injective _ (by norm_num) },
    intros S hS,
    rw [image_smul, ←preimage_smul₀],
    { apply measurable_set_preimage _ hS,
      rw measurable_const_smul_iff₀,
      exact measurable_id',
      exact two_ne_zero },
    { exact two_ne_zero } },
  have h2 : volume F < volume ((1/2 : ℝ) • S),
  { rw ←ennreal.mul_lt_mul_right (pow_ne_zero (card ι) two_ne_zero') (pow_ne_top two_ne_top),
    convert h },
  rw [←one_smul ℝ T, ←_root_.add_halves (1 : ℝ), h_conv.add_smul one_half_pos.le one_half_pos.le],
  obtain ⟨x, y, hx, hy, hne, hsub⟩ :=
    exists_add_neg_mem_lattice_of_volume_lt_volume' L mhalf fund h2,
  refine ⟨⟨y - x, hsub⟩, subtype.ne_of_val_ne $ sub_ne_zero.2 hne.symm, y, -x,
    smul_set_mono interior_subset hy, _, rfl⟩,
  obtain ⟨x, hx, rfl⟩ := hx,
  rw ←smul_neg,
  exact smul_mem_smul_set (h_symm ⟨x, interior_subset hx, rfl⟩),
end
