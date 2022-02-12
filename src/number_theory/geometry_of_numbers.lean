/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import measure_theory.measure.haar_lebesgue
import measure_theory.group.action
import measure_theory.group.fundamental_domain
import analysis.convex.basic
import algebra.order.pointwise
import topology.bases
import algebra.module.pointwise_pi

/-!
# Geometry of numbers

In this file we prove some of the fundamental theorems in the geometry of numbers, as
studied by Hermann Minkowski.

## Main results

- `exists_sub_mem_lattice_of_volume_lt_volume`: Blichfeldt's principle, existence of two points
  within a set whose difference lies in a subgroup when the covolume of the subgroup is larger than
  the set.
- `exists_nonzero_mem_lattice_of_volume_mul_two_pow_card_lt_volume`: Minkowski's theorem, existence
  of a non-zero lattice point inside a convex symmetric domain of large enough covolume.

-/
open measure_theory measure_theory.measure topological_space set
open_locale pointwise
section
-- TODO move to measure_theory.group.basic
noncomputable theory

open_locale ennreal pointwise
open has_inv set function measure_theory.measure
section
variables {α :Type*} [measurable_space α] (μ : outer_measure α)
@[simp] lemma measure_theory.outer_measure.measure_Union_null_iff' {ι : Prop} {s : ι → set α} :
  μ (⋃ i : ι, s i) = 0 ↔ ∀ i : ι, μ (s i) = 0 :=
begin
  by_cases i : ι;
  simp [i],
end
end
variables {α :Type*} [measurable_space α] {μ : measure α}
@[simp] lemma measure_Union_null_iff' {ι : Prop} {s : ι → set α} :
  μ (⋃ i : ι, s i) = 0 ↔ ∀ i : ι, μ (s i) = 0 :=
μ.to_outer_measure.measure_Union_null_iff'

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
  smul_invariant_measure S V μ := ⟨λ g A hA, by {convert measure_preimage_smul (g : G) μ A, }⟩

@[to_additive]
lemma smul_invariant_measure.volume_smul {G : Type*} [group G] [measurable_space G] [mul_action G V]
  [has_measurable_smul G V] {μ : measure V}
  [smul_invariant_measure G V μ] (g : G) {S : set V} : μ (g • S) = μ S :=
by rw [← measure_preimage_smul (g⁻¹) μ S, preimage_smul, inv_inv]

-- @[to_additive]
-- lemma is_mul_left_invariant.to_smul_invariant_measure [measurable_space G] [has_mul G]
--   {μ : measure G} [is_mul_left_invariant μ] :
-- smul_invariant_measure G G μ := ⟨h⟩

end
end measure_theory
end

section
variables {X Y : Type*} [measure_space Y] [group X] [mul_action X Y]
  [measurable_space X] [has_measurable_smul X Y]

@[to_additive]
lemma measurable_set_smul (x : X) {S : set Y} (h : measurable_set S) : measurable_set (x • S) :=
begin
  rw [← inv_inv x, ← preimage_smul (x⁻¹)],
  exact has_measurable_smul.measurable_const_smul _ h,
end

end
section
variables {X Y : Type*} [measure_space Y] [group_with_zero X] [mul_action X Y]
  [measurable_space X] [has_measurable_smul X Y]

-- TODO is there a version of this for x = 0 as well

lemma measurable_set_smul₀ {x : X} (hx : x ≠ 0) {S : set Y} (h : measurable_set S) :
  measurable_set (x • S) :=
begin
  rw [← inv_inv₀ x, ← preimage_smul₀ (inv_ne_zero hx)],
  exact has_measurable_smul.measurable_const_smul _ h,
end
end
section
variables {X Y : Type*} [measure_space Y] [group_with_zero X]
  [measurable_space X]

lemma measurable_set_smul₀_of_measurable_singleton_class [has_zero Y] [mul_action_with_zero X Y]
  [measurable_singleton_class Y] [has_measurable_smul X Y]
  {x : X} {S : set Y} (h : measurable_set S) :
  measurable_set (x • S) :=
begin
  by_cases hx : x = 0,
  { by_cases hS : S.nonempty,
    { rw [hx, zero_smul_set hS],
      exact measurable_set_singleton 0, },
    { convert measurable_set.empty,
      rw not_nonempty_iff_eq_empty at hS,
      rw hS,
      simp, }, },
  { exact measurable_set_smul₀ hx h, },
end

end

section geometry_of_numbers

universe u
variables (ι : Type u)
noncomputable theory
open set

lemma is_add_left_invariant_pi_volume [fintype ι] {K : ι → Type*} [∀ i, measure_space (K i)]
  [∀ i, add_group (K i)] [∀ i, topological_space (K i)] [∀ i, has_continuous_add (K i)]
  [∀ i, has_measurable_add (K i)] -- TODO???
  [borel_space (Π i, K i)] [∀ i, sigma_finite (volume : measure (K i))]
  [∀ i, is_add_left_invariant (volume : measure (K i))] :
  is_add_left_invariant ((volume : measure (Π i, K i))) :=
begin
  constructor,
  -- rw [← map_add_left_eq_self],
  intro v,
  refine (pi_eq _).symm,
  intros s hS,
  rw [map_apply, volume_pi],
  rw (_ : (+) v ⁻¹' (univ : set _).pi s = (univ : set _).pi (λ (i : ι), (+) (v i) ⁻¹' (s i))),
  { rw pi_pi,
    { congr',
      ext i : 1,
      exact measure_preimage_add _ _ _, }, },
  { refl, },
  { exact measurable_const_add v, },
  { exact measurable_set.univ_pi_fintype hS, },
end

/-- The closed unit cube with sides the intervals [0,1] as a positive compact set, for inducing the
    Haar measure equal to the lebesgue measure on ℝ^n. -/
def unit_cube [fintype ι] : positive_compacts (ι → ℝ) :=
⟨Icc 0 1, begin
  simp_rw [← pi_univ_Icc, pi.zero_apply, pi.one_apply],
  exact is_compact_univ_pi (λ i, is_compact_Icc),
end,
begin
  -- rw interior_Icc,
  simp_rw [← pi_univ_Icc, pi.zero_apply, pi.one_apply,
    interior_pi_set finite_univ, interior_Icc, univ_pi_nonempty_iff],
  exact (λ i, nonempty_Ioo.mpr zero_lt_one),
end⟩

lemma volume_Icc [fintype ι] : volume (Icc 0 1 : set (ι → ℝ)) = 1 :=
begin
  simp_rw [← pi_univ_Icc, pi.zero_apply, pi.one_apply],
  rw [volume_pi_pi, real.volume_Icc, sub_zero, ennreal.of_real_one, finset.prod_const_one],
end

lemma pi_haar_measure_eq_lebesgue_measure [fintype ι] : add_haar_measure (unit_cube ι) = volume :=
begin
  convert (add_haar_measure_unique _ (unit_cube ι)).symm,
  { rw [unit_cube],
    suffices : measure_space.volume (Icc (0 : ι → ℝ) 1) = 1,
    { rw [this, one_smul], },
    exact volume_Icc ι, },
  { apply_instance },
  { exact is_add_left_invariant_pi_volume ι, },
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
variables (fund : is_fundamental_domain X F)
include fund

-- @[to_additive]
-- lemma measurable_set_smul [measurable_space X] [has_measurable_smul X Y] (x : X) :
--   measurable_set (x • F) := measurable_set_smul x fund.measurable_set

/-- The interior of a fundamental domain, those points of the domain not lying in any translate. -/
@[to_additive "The interior of a fundamental domain, those points of the domain not lying in any
translate."]
protected def interior : set Y := F \ ⋃ (l : X) (h : l ≠ 1), (l • F)

@[to_additive]
lemma measurable_set_nontrivial_translates [measurable_space X] [has_measurable_smul X Y]
  [encodable X] : measurable_set ⋃ (l : X) (h : l ≠ 1), l • F :=
begin
  apply measurable_set.Union,
  intros b,
  cases eq_or_ne b 1 with h h,
  { simp [h], },
  { -- TODO squeeze_simp output wrong
    simp [h, -set.image_smul, set.Union_true, ne.def, not_false_iff, set.Union_congr_Prop],
    exact measurable_set_smul fund _, },
end

@[to_additive]
lemma measurable_set_interior [measurable_space X] [has_measurable_smul X Y] [encodable X] :
  measurable_set fund.interior :=
measurable_set.diff fund.measurable_set fund.measurable_set_nontrivial_translates


/-- The boundary of a fundamental domain, those points of the domain that also lie in a nontrivial
translate. -/
@[to_additive "The boundary of a fundamental domain, those points of the domain that also lie in a
nontrivial translate."]
protected def boundary : set Y := F ∩ ⋃ (l : X) (h : l ≠ 1), l • F

@[to_additive]
lemma eq_interior_union_boundary : F = fund.interior ∪ fund.boundary :=
(diff_union_inter _ _).symm

@[to_additive]
lemma measurable_set_boundary [measurable_space X] [has_measurable_smul X Y] [encodable X] :
  measurable_set fund.boundary :=
measurable_set.inter fund.measurable_set fund.measurable_set_nontrivial_translates

open set

@[to_additive]
lemma volume_boundary [encodable X] : volume fund.boundary = 0 :=
begin
  rw is_fundamental_domain.boundary,
  simp only [inter_Union, measure_Union_null_iff, measure_Union_null_iff'],
  intros i hi,
  rw [inter_comm], -- why wouldn't simp do this?
  exact fund.ae_disjoint i hi,
end

@[to_additive]
lemma disjoint_interior_boundary : disjoint fund.interior fund.boundary :=
begin
  rw [is_fundamental_domain.interior, is_fundamental_domain.boundary],
  -- TODO from here is general lemma
  apply' disjoint.symm,
  apply disjoint_of_subset_left (inter_subset_right _ _),
  exact disjoint_diff,
end

@[to_additive]
lemma volume_interior [encodable X] : volume fund.interior = volume F :=
measure_diff_null' (volume_boundary fund)

open measure_theory

-- @[to_additive]
-- lemma volume_set_eq_tsum_volume_inter [measurable_space X] [has_measurable_smul X Y] [encodable X]
--   {S : set Y} (hS : measurable_set S) [smul_invariant_measure X Y (volume : measure Y)] :
--   ∑' (x : X), volume (x • S ∩ F) = volume S :=
-- begin
--   rw (_ : ∑' (x : X), volume (x • S ∩ F) = ∑' (x : X), volume (x⁻¹ • (x • S ∩ F))),
--   { simp only [smul_set_inter, inv_smul_smul],
--     rw ← measure_Union₀,
--     { library_search,
--       congr,
--       rw [← set.inter_Union, set.inter_eq_self_of_subset_left],
--       convert set.subset_univ _,
--       rw set.eq_univ_iff_forall,
--       intros x,
--       rw set.mem_Union,
--       obtain ⟨l, hl⟩ := fund.ae_covers x,
--       use [l],
--       refine ⟨_, hl, _⟩,
--       rw [inv_smul_smul], },
--     { intros x y hxy,
--       change volume _ = 0,
--       rw inter_assoc,
--       apply measure_inter_null_of_null_right,
--       rw [inter_comm, inter_assoc],
--       apply measure_inter_null_of_null_right,
--       rw ← smul_invariant_measure.volume_smul y,
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
--       apply_instance, },
--     { intro l,
--       simp,
--       exact hS.inter (F.measurable_set_smul l⁻¹), },
--  },
--   { congr,
--     ext1 l,
--     rw h_smul_left.volume_smul,
--     exact (_root_.measurable_set_smul l hS).inter F.measurable_set_domain, },
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

instance subtype.measure_space {V : Type*} [measure_space V] {p : set V} :
  measure_space (subtype p) :=
{ volume := measure.comap subtype.val volume,
  ..subtype.measurable_space }

lemma volume_subtype_univ {V : Type*} [measure_space V] {p : set V} (hmp : measurable_set p) :
  volume (set.univ : set (subtype p)) = volume p :=
begin
  dsimp only [measure_space.volume],
  rw [measure.comap_apply _ subtype.val_injective, set.image_univ],
  { congr,
    exact subtype.range_val, },
  { intros x,
    exact measurable_set.subtype_image hmp, },
  { exact measurable_set.univ, }
end

open measure_theory

/-- Blichfeldt's Principle --/
@[to_additive]
lemma exists_mul_inv_mem_lattice_of_volume_lt_volume {X Y : Type*} [measurable_space X]
  [measure_space Y] [group X] [mul_action X Y]
  [has_measurable_smul X Y] [encodable X] {S : set Y} (hS : measurable_set S)
  (F : set Y) (fund : is_fundamental_domain X F) (hlt : volume F < volume S)
  [smul_invariant_measure X Y (volume : measure Y)]
  -- (h_smul_left : smul_invariant_measure X ⇑(volume : measure Y))
  (hnostab : ∀ (p₁ p₂ : X) (q : Y) (hq : q ∈ S) (hppq : p₁ • q = p₂ • q), p₁ = p₂) :
  ∃ (x y : Y) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y), y ∈ (• x) '' (univ : set X) :=
begin
  suffices : ∃ (p₁ p₂ : X) (hne : p₁ ≠ p₂),
    ((p₁ • S ∩ F) ∩ (p₂ • S ∩ F)).nonempty,
  { rcases this with ⟨p₁, p₂, hne, u, ⟨⟨q₁, ⟨hS₁, ht₁⟩⟩, hu⟩, ⟨⟨q₂, ⟨hS₂, ht₂⟩⟩, hu⟩⟩,
    use [q₁, q₂, hS₁, hS₂],
    split,
    { rintros rfl,
      rw ← ht₂ at *,
      exact hne (hnostab _ _ _ hS₁ ht₁), },
    { simp only [mem_image, set_like.mem_coe],
      use [p₂⁻¹ * p₁],
      split,
      exact mem_univ (p₂⁻¹ * p₁),
      rw [mul_smul, ht₁, ← ht₂, ← mul_smul, inv_mul_self, one_smul], }, },
  rw ← volume_subtype_univ fund.measurable_set at hlt,
  have := exists_nonempty_inter_of_measure_univ_lt_tsum_measure subtype.measure_space.volume
    (_ : (∀ p : X, measurable_set (λ a, (p • S) a : set F))) _,
  { rcases this with ⟨i, j, hij, t, ht⟩,
    use [i, j, hij, t],
    simp only [and_true, mem_inter_eq, subtype.coe_prop, image_smul],
    exact ht, },
  { intro p,
    exact measurable_set_preimage (measurable_id'.subtype_coe) (measurable_set_smul p hS), },
  convert hlt,
  symmetry,
  convert fund.measure_eq_tsum S,
  ext1 l,
  dsimp only [subtype.measure_space], -- TODO lemma
  rw measure.comap_apply _ subtype.val_injective _ _ _,
  { congr,
    ext1 v,
    simp only [mem_image, mem_inter_eq, exists_and_distrib_right, exists_eq_right, subtype.exists,
      subtype.coe_mk, subtype.val_eq_coe],
    split; { intros a, rcases a with ⟨a_left, a_right⟩, split; assumption, }, },
  { intros X hX,
    convert measurable_set.subtype_image fund.measurable_set hX, },
  { erw [← inv_inv l, ← preimage_smul (l⁻¹ : X) S],
    exact measurable_set_preimage
      ((measurable_const_smul (l⁻¹ : X)).comp measurable_subtype_coe) hS, },
end

-- TODO version giving `ceiling (volume S / volume F)` points whose difference is in a subgroup
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
  haveI : smul_invariant_measure L X measure_space.volume :=
  begin
    apply smul_invariant_measure.to_subgroup_smul_invariant_measure L,
    apply_instance,
    constructor,
    intros c S hS,
    exact measure_preimage_mul volume c S,
  end,
  obtain ⟨x, y, hx, hy, hne, h⟩ := exists_mul_inv_mem_lattice_of_volume_lt_volume hS F fund hlt _,
  { refine ⟨x, y, hx, hy, hne, _⟩,
    simp only [image_univ, mem_range] at h,
    obtain ⟨l, rfl⟩ := h,
    simp [subgroup.smul_def], },
  -- { exact smul_invariant_measure.to_subgroup_smul_invariant_measure _ , },
  { rintros ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ q hq hleft,
    simpa [subgroup.smul_def] using hleft, },
end

open measure_theory measure_theory.measure topological_space set

lemma rescale (ι : Type*) [fintype ι] {r : ℝ} (hr : 0 < r) :
  measure.comap ((•) r) (volume : measure (ι → ℝ)) =
  (ennreal.of_real r) ^ (fintype.card ι) • (volume : measure (ι → ℝ)) :=
begin
  have hrzero : ennreal.of_real r ≠ 0,
  { intro h,
    rw ennreal.of_real_eq_zero at h,
    linarith, },
  have hrtop : ennreal.of_real r ≠ ⊤, from ennreal.of_real_ne_top,
  suffices : (1 / ennreal.of_real r) ^ (fintype.card ι) •
    measure.comap ((•) r) (volume : measure (ι → ℝ)) = (volume : measure (ι → ℝ)),
  { conv_rhs { rw ← this, },
    rw [one_div, smul_smul, ← mul_pow, ennreal.mul_inv_cancel hrzero hrtop],
    simp only [one_pow, one_smul], },
  refine (pi_eq _).symm,
  intros s hS,
  simp only [one_div, algebra.id.smul_eq_mul, coe_smul, pi.smul_apply],
  rw [comap_apply, image_smul, smul_univ_pi],
  { erw pi_pi,
    dsimp,
    { conv in (r • _)
      { rw ← inv_inv₀ r, },
      conv in (volume (r⁻¹⁻¹ • _))
      { rw ← preimage_smul₀ (inv_ne_zero (ne_of_gt hr)), },
      simp only [algebra.id.smul_eq_mul],
      rw [fintype.card, ← finset.prod_const, ← finset.prod_mul_distrib],
      congr,
      ext i : 1,
      erw ← measure.map_apply (measurable_const_mul r⁻¹) (hS i),
      conv_rhs { rw [← real.smul_map_volume_mul_left (inv_ne_zero (ne_of_gt hr))], },
      congr,
      rw [ennreal.of_real_inv_of_pos hr, abs_of_pos (inv_pos.mpr hr)], }, },
  { exact smul_right_injective (ι → ℝ) (ne_of_gt hr), },
  { intros S hS,
    rw [image_smul],
    exact measurable_set.const_smul₀ hS r, },
  { exact measurable_set.univ_pi_fintype hS, },
end

open ennreal fintype

-- TODO version for any real vector space in terms of dimension
lemma exists_nonzero_mem_lattice_of_volume_mul_two_pow_card_lt_volume [fintype ι]
  {L : add_subgroup (ι → ℝ)} [encodable.{u} L] {F S : set (ι → ℝ)}
  (fund : is_add_fundamental_domain L F)
  (hS : measurable_set S) (h : volume F * 2 ^ (card ι) < volume S)
  (h_symm : ∀ x ∈ S, -x ∈ S) (h_conv : convex ℝ S) : ∃ (x : L) (h : x ≠ 0), (x : ι → ℝ) ∈ S :=
begin
  have mhalf : measurable_set ((1/2 : ℝ) • S),
  { convert measurable_const_smul (2 : ℝ) hS,
    ext x,
    simp only [one_div, set.mem_preimage],
    exact mem_inv_smul_set_iff₀ two_ne_zero S x, },
  have : volume ((1/2 : ℝ) • S) * 2 ^ (card ι) = volume S,
  { suffices : volume ((1/2 : ℝ) • S) = (1 / 2) ^ (card ι) * volume S,
    { rw [this, mul_comm _ (volume S), mul_assoc, ← mul_pow, one_div,
        ennreal.inv_mul_cancel two_ne_zero two_ne_top, one_pow, mul_one], },
    have := rescale ι (half_pos zero_lt_one),
    simp only [one_div, fintype.card_fin] at this ⊢,
    rw ← ennreal.of_real_inv_of_pos (by norm_num : 0 < (2 : ℝ)) at this,
    simp only [zero_le_one, of_real_one, of_real_bit0] at this,
    rw [← measure.smul_apply, ← this, comap_apply _ _ _ _ hS],
    { simp, },
    { exact smul_right_injective _ (by norm_num), },
    { intros S hS,
      rw [image_smul, ← preimage_smul₀],
      { apply measurable_set_preimage _ hS,
        rw measurable_const_smul_iff₀,
        exact measurable_id',
        exact two_ne_zero, },
      { exact two_ne_zero, }, }, },
  have h2 : volume F < volume ((1/2 : ℝ) • S),
  { rw ← ennreal.mul_lt_mul_right (pow_ne_zero (card ι) two_ne_zero') (pow_ne_top two_ne_top),
    convert h, },

  have : (1 / 2 + 1 / 2 : ℝ) • S = (1/2 : ℝ) • S + (1/2 : ℝ) • S,
  from h_conv.add_smul one_half_pos.le one_half_pos.le,
  rw [(show (1 / 2 : ℝ) + 1 / 2 = 1, by norm_num), one_smul] at this,
  rw this,
  suffices : ∃ (x y : ι → ℝ) (hx : x ∈ (1/2 : ℝ) • S) (hy : y ∈ (1/2 : ℝ) • S) (hne : x ≠ y),
    y - x ∈ L,
  { rcases this with ⟨x, y, hx, hy, hne, hsub⟩,
    use ⟨y - x, hsub⟩,
    split,
    { apply subtype.ne_of_val_ne,
      simp [sub_eq_zero, hne.symm], },
    have : ∀ t ∈ (1/2 : ℝ) • S, -t ∈ (1/2 : ℝ) • S,
    { intros t ht,
      rcases ht with ⟨v, hv, rfl⟩,
      rw ← smul_neg,
      exact set.smul_mem_smul_set (h_symm _ hv), },
    use [y, -x, hy, this _ hx],
    refl, },
  { exact exists_add_neg_mem_lattice_of_volume_lt_volume' L mhalf fund h2,
    -- rw [← pi_haar_measure_eq_lebesgue_measure _],
    -- exact measure.is_add_left_invariant_add_haar_measure (unit_cube _),
    },
end

end geometry_of_numbers
