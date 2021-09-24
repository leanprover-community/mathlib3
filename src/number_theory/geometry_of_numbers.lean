/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import measure_theory.measure.haar_lebesgue
import analysis.convex.basic
import algebra.order.pointwise
import topology.bases

/-!
# Geometry of numbers

In this file we introduce prove some of the fundamental theorems in the geometry of numbers, as
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

-- TODO
-- @[to_additive /-"The additive action by an add_subgroup is the action by the underlying
-- add_group. "-/]
@[to_additive]
instance submonoid.has_measurable_smul {G α : Type*} [monoid G] [mul_action G α]
  [measurable_space G] [measurable_space α] [has_measurable_smul G α] (S : submonoid G) :
  has_measurable_smul S α :=
{ measurable_const_smul := λ c, (measurable_const_smul (c : G)).comp measurable_id,
  measurable_smul_const := λ x, measurable_id'.subtype_coe.smul_const x, }

-- TODO
-- @[to_additive /-"The additive action by an add_subgroup is the action by the underlying
-- add_group. "-/]
@[to_additive]
instance subgroup.has_measurable_smul {G α : Type*} [group G] [mul_action G α] [measurable_space G]
  [measurable_space α] [has_measurable_smul G α] (S : subgroup G) : has_measurable_smul S α :=
S.to_submonoid.has_measurable_smul

-- { measurable_const_smul := λ c, (measurable_const_smul (c : G)).comp measurable_id,
--   measurable_smul_const := λ x, measurable_id'.subtype_coe.smul_const x, }

namespace measure_theory

variables {G V : Type*}

section

variables [measurable_space V]

/-- A measure `μ` on a topological group is left invariant for an action
  if the measure of left translations of a set are equal to the measure of the set itself.
  To left translate sets we use preimage under left multiplication,
  since preimages are nicer to work with than images. -/
@[to_additive "A measure on a topological group is left invariant for an action
  if the measure of left translations of a set are equal to the measure of the set itself.
  To left translate sets we use preimage under left addition,
  since preimages are nicer to work with than images."]
def is_smul_left_invariant (G) [has_scalar G V] (μ : set V → ℝ≥0∞) : Prop :=
∀ (g : G) {A : set V} (h : measurable_set A), μ ((λ h, g • h) ⁻¹' A) = μ A

--TODO given subgroup we don't get has_scalar in the same way as mul_action
@[to_additive]
lemma is_smul_left_invariant.to_subgroup_is_smul_left_invariant {G : Type*} [group G]
  (S : subgroup G) [mul_action G V] {μ : set V → ℝ≥0∞} (h : is_smul_left_invariant G μ) :
  is_smul_left_invariant S μ := λ g A hA, h g hA

@[to_additive]
lemma is_smul_left_invariant.volume_smul {G : Type*} [group G] [mul_action G V] {μ : measure V}
  (h : is_smul_left_invariant G μ) (g : G) {S : set V} (hS : measurable_set S) : μ (g • S) = μ S :=
by rw [← h (g⁻¹) hS, preimage_smul, inv_inv]

@[to_additive]
lemma is_mul_left_invariant.to_is_smul_left_invariant [measurable_space G] [has_mul G]
  {μ : set G → ℝ≥0∞} (h : is_mul_left_invariant μ) :
is_smul_left_invariant G μ := h

end
end measure_theory
end

lemma smul_univ_pi {K : Type*} [has_mul K] (ι : Type*) {r : K} (t : ι → set K) :
  r • pi (univ : set ι) t = pi (univ : set ι) (λ (i : ι), r • t i) :=
begin
  ext x,
  simp only [mem_smul_set, mem_univ_pi],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp only [pi.smul_apply],
    intro i,
    refine ⟨h_w i, h_h_left i, rfl⟩, },
  { use (λ i, classical.some (h i)),
    split,
    { exact λ i, (classical.some_spec (h i)).left, },
    { ext i,
      exact (classical.some_spec (h i)).right, }, },
end

lemma smul_pi' {K : Type*} [group_with_zero K] (ι : Type*) {r : K} (t : ι → set K) (S : set ι)
  (hr : r ≠ 0) : r • S.pi t = S.pi (λ (i : ι), r • t i) :=
begin
  ext x,
  simp only [mem_smul_set, mem_pi],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp only [mul_eq_mul_left_iff, pi.smul_apply],
    intros i hi,
    refine ⟨h_w i, h_h_left i hi, rfl⟩, },
  classical,
  { use (λ i, if hiS : i ∈ S then classical.some (h i hiS) else r⁻¹ * x i),
    split,
    { intros i hiS,
      split_ifs,
      exact (classical.some_spec (h i hiS)).left, },
    { ext i,
      rw [pi.smul_apply, smul_eq_mul],
      split_ifs with hiS,
      exact (classical.some_spec (h i hiS)).right,
      rw mul_inv_cancel_left' hr, }, },
end

lemma smul_pi {K : Type*} [group K] (ι : Type*) {r : K} (t : ι → set K) (S : set ι) :
  r • S.pi t = S.pi (λ (i : ι), r • t i) :=
begin
  ext x,
  simp only [mem_smul_set, mem_pi],
  split; intro h,
  { rcases h with ⟨h_w, h_h_left, rfl⟩,
    simp only [mul_eq_mul_left_iff, pi.smul_apply],
    intros i hi,
    refine ⟨h_w i, h_h_left i hi, rfl⟩, },
  classical,
  { use (λ i, if hiS : i ∈ S then classical.some (h i hiS) else r⁻¹ * x i),
    split,
    { intros i hiS,
      split_ifs,
      exact (classical.some_spec (h i hiS)).left, },
    { ext i,
      rw [pi.smul_apply, smul_eq_mul],
      split_ifs with hiS,
      exact (classical.some_spec (h i hiS)).right,
      rw mul_inv_cancel_left, }, },
end

section
variables {X Y : Type*} [measure_space Y] [group X] [mul_action X Y]
  [measurable_space X] [has_measurable_smul X Y]
@[to_additive]
lemma measurable_set_smul (x : X) {S : set Y} (h : measurable_set S) : measurable_set (x • S) :=
begin
  rw [← inv_inv x, ← preimage_smul (x⁻¹)],
  apply has_measurable_smul.measurable_const_smul,
  exact h,
end


--TODO move
@[to_additive]
lemma smul_set_inter {α β : Type*} [group α] (a : α) [mul_action α β] {s t : set β} :
  a • (s ∩ t) = a • s ∩ a • t :=
begin
  erw [← image_smul, image_inter],
  exact mul_action.injective a,
end

end

namespace geometry_of_numbers

universe u
variables (ι : Type u)
noncomputable theory
open set

lemma is_add_left_invariant_pi_volume [fintype ι] {K : ι → Type*} [∀ i, measure_space (K i)]
  [∀ i, has_add (K i)] [∀ i, topological_space (K i)] [∀ i, has_continuous_add (K i)]
  [∀ i, has_measurable_add (K i)] [borel_space (Π i, K i)]
  [∀ i, sigma_finite (volume : measure (K i))]
  (h : ∀ i, is_add_left_invariant ⇑(volume : measure (K i))) :
  is_add_left_invariant (⇑(volume : measure (Π i, K i))) :=
begin
  rw [← map_add_left_eq_self],
  intro v,
  refine (pi_eq _).symm,
  intros s hS,
  rw [map_apply, volume_pi],
  rw (_ : (+) v ⁻¹' (univ : set _).pi s = (univ : set _).pi (λ (i : ι), (+) (v i) ⁻¹' (s i))),
  { rw pi_pi,
    { congr',
      ext i : 1,
      rw h _ _ (hS i), },
    { intro i,
      exact measurable_set_preimage (measurable_const_add (v i)) (hS i), }, },
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
  simp_rw [← pi_univ_Icc, pi.zero_apply, pi.one_apply],
  rw [interior_pi_set, interior_Icc, univ_pi_nonempty_iff],
  exact (λ i, nonempty_Ioo.mpr zero_lt_one),
end⟩

lemma volume_Icc [fintype ι] : volume (Icc 0 1 : set (ι → ℝ)) = 1 :=
begin
  simp_rw [← pi_univ_Icc, pi.zero_apply, pi.one_apply],
  rw [volume_pi_pi, real.volume_Icc, sub_zero, ennreal.of_real_one, finset.prod_const_one],
  exact (λ i, measurable_set_Icc),
end

lemma pi_haar_measure_eq_lebesgue_measure [fintype ι] : add_haar_measure (unit_cube ι) = volume :=
begin
  convert (add_haar_measure_unique _ (unit_cube ι)).symm,
  { rw [unit_cube],
    suffices : measure_space.volume (Icc (0 : ι → ℝ) 1) = 1,
    { rw [this, one_smul], },
    exact volume_Icc ι, },
  { apply_instance },
  { exact is_add_left_invariant_pi_volume ι (λ i, is_add_left_invariant_real_volume), },
end

variable {ι}

/-- A fundamental domain for an additive group acting on a measure space. -/
structure add_fundamental_domain (Y X : Type*) [measure_space Y] [add_group X] [has_vadd X Y] :=
(domain : set Y)
(measurable_set_domain : measurable_set domain)
(almost_disjoint : volume (domain ∩ ⋃ (l : X) (h : l ≠ 0), (l +ᵥ domain)) = 0)
(covers : ∀ (y : Y), ∃ (l : X), l +ᵥ y ∈ domain)
--TODO should these be set_like or something?

/-- A fundamental domain for a group acting on a measure space. -/
@[to_additive add_fundamental_domain, nolint has_inhabited_instance]
structure fundamental_domain (Y X : Type*) [measure_space Y] [group X] [has_scalar X Y] :=
(domain : set Y)
(measurable_set_domain : measurable_set domain)
(almost_disjoint : volume (domain ∩ ⋃ (l : X) (h : l ≠ 1), l • domain) = 0)
(covers : ∀ (y : Y), ∃ (l : X), l • y ∈ domain)

namespace fundamental_domain
variables {X Y : Type*} [measure_space Y] [group X] [mul_action X Y] (F : fundamental_domain Y X)

@[to_additive]
lemma measurable_set_smul [measurable_space X] [has_measurable_smul X Y] (x : X) :
  measurable_set (x • F.domain) := measurable_set_smul x F.measurable_set_domain

/-- The interior of a fundamental domain, those points of the domain not lying in any translate. -/
@[to_additive "The interior of a fundamental domain, those points of the domain not lying in any
translate."]
protected def interior : set Y := F.domain \ ⋃ (l : X) (h : l ≠ 1), (l • F.domain)

@[to_additive]
lemma measurable_set_nontrivial_translates [measurable_space X] [has_measurable_smul X Y]
  [encodable X] : measurable_set ⋃ (l : X) (h : l ≠ 1), l • F.domain :=
begin
  apply measurable_set.Union,
  intros b,
  cases eq_or_ne b 1 with h h,
  { simp [h], },
  { -- TODO squeeze_simp output wrong
    simp [h, -set.image_smul, set.Union_true, ne.def, not_false_iff, set.Union_congr_Prop],
    exact measurable_set_smul _ _, },
end

@[to_additive]
lemma measurable_set_interior [measurable_space X] [has_measurable_smul X Y] [encodable X] :
  measurable_set F.interior :=
begin
  rw fundamental_domain.interior,
  exact measurable_set.diff F.measurable_set_domain F.measurable_set_nontrivial_translates,
end

/-- The boundary of a fundamental domain, those points of the domain that also lie in a nontrivial
translate. -/
@[to_additive "The boundary of a fundamental domain, those points of the domain that also lie in a
nontrivial translate."]
protected def boundary : set Y := F.domain ∩ ⋃ (l : X) (h : l ≠ 1), l • F.domain

@[to_additive]
lemma eq_interior_union_boundary : F.domain = F.interior ∪ F.boundary :=
by rw [fundamental_domain.interior, fundamental_domain.boundary, diff_union_inter]

@[to_additive]
lemma measurable_set_boundary [measurable_space X] [has_measurable_smul X Y] [encodable X] :
  measurable_set F.boundary :=
begin
  rw fundamental_domain.boundary,
  apply measurable_set.inter F.measurable_set_domain,
  exact F.measurable_set_nontrivial_translates,
end

open set

@[to_additive]
lemma volume_boundary : volume F.boundary = 0 := F.almost_disjoint

@[to_additive]
lemma disjoint_interior_boundary : disjoint F.interior F.boundary :=
begin
  rw [fundamental_domain.interior, fundamental_domain.boundary],
  -- TODO from here is general lemma
  apply' disjoint.symm,
  apply disjoint_of_subset_left (inter_subset_right _ _),
  exact disjoint_diff,
end

@[to_additive]
lemma volume_interior : volume F.interior = volume F.domain :=
by { rw [fundamental_domain.interior], exact measure_diff_null' (volume_boundary _), }
open measure_theory

@[to_additive]
lemma volume_set_eq_tsum_volume_inter [measurable_space X] [has_measurable_smul X Y] [encodable X]
  {S : set Y} (hS : measurable_set S) (h_smul_left : is_smul_left_invariant X ⇑(volume : measure Y))
  : ∑' (x : X), volume (x • S ∩ F.domain) = volume S :=
begin
  rw (_ : ∑' (x : X), volume (x • S ∩ F.domain) = ∑' (x : X), volume (x⁻¹ • (x • S ∩ F.domain))),
  { simp only [smul_set_inter, inv_smul_smul],
    rw ← measure_Union_of_null_inter,
    { congr,
      rw [← set.inter_Union, set.inter_eq_self_of_subset_left],
      convert set.subset_univ _,
      rw set.eq_univ_iff_forall,
      intros x,
      rw set.mem_Union,
      obtain ⟨l, hl⟩ := F.covers x,
      use [l],
      refine ⟨_, hl, _⟩,
      rw [inv_smul_smul], },
    { intro l,
      exact hS.inter (F.measurable_set_smul l⁻¹), },
    { intros x y hxy,
      change volume _ = 0,
      rw inter_assoc,
      apply measure_inter_null_of_null_right,
      rw [inter_comm, inter_assoc],
      apply measure_inter_null_of_null_right,
      rw ← h_smul_left.volume_smul y
        ((F.measurable_set_smul y⁻¹).inter (F.measurable_set_smul x⁻¹)),
      simp only [smul_set_inter, smul_inv_smul],
      rw [smul_smul],
      apply measure_mono_null (F.domain.inter_subset_inter_right _) F.almost_disjoint,
      intros t ht,
      rw mem_Union,
      use y * x⁻¹,
      rw [ne.def, mul_inv_eq_one, mem_Union],
      exact ⟨hxy.symm, ht⟩, }, },
  { congr,
    ext1 l,
    rw h_smul_left.volume_smul,
    exact (_root_.measurable_set_smul l hS).inter F.measurable_set_domain, },
end


end fundamental_domain
--TODO all f.d.s have same measure https://arxiv.org/pdf/1405.2119.pdf
-- TODO fin index subgroup has given fundamental domain and covolume
-- TODO some existence result? in presence of metric? voronoi

instance : inhabited (add_fundamental_domain (fin 0 → ℝ) (fin 0 → ℝ)) :=
{ default := { domain := ⊤,
  measurable_set_domain := subsingleton.measurable_set,
  almost_disjoint := by simp,
  covers := λ v, by simp } }

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
  (F : fundamental_domain Y X) (hlt : volume F.domain < volume S)
  (h_smul_left : is_smul_left_invariant X ⇑(volume : measure Y))
  (hnostab : ∀ (p₁ p₂ : X) (q : Y) (hq : q ∈ S) (hppq : p₁ • q = p₂ • q), p₁ = p₂) :
  ∃ (x y : Y) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y), y ∈ (• x) '' (univ : set X) :=
begin
  suffices : ∃ (p₁ p₂ : X) (hne : p₁ ≠ p₂),
    ((p₁ • S ∩ F.domain) ∩ (p₂ • S ∩ F.domain)).nonempty,
  begin
    rcases this with ⟨p₁, p₂, hne, u, ⟨⟨q₁, ⟨hS₁, ht₁⟩⟩, hu⟩, ⟨⟨q₂, ⟨hS₂, ht₂⟩⟩, hu⟩⟩,
    use [q₁, q₂, hS₁, hS₂],
    split,
    { rintros rfl,
      rw ← ht₂ at *,
      exact hne (hnostab _ _ _ hS₁ ht₁), },
    { simp only [mem_image, set_like.mem_coe],
      use [p₂⁻¹ * p₁],
      split,
      exact mem_univ (p₂⁻¹ * p₁),
      rw [mul_smul, ht₁, ← ht₂, ← mul_smul, inv_mul_self, one_smul], },
  end,
  rw ← volume_subtype_univ F.measurable_set_domain at hlt,
  have := exists_nonempty_inter_of_measure_univ_lt_tsum_measure subtype.measure_space.volume
    (_ : (∀ p : X, measurable_set (λ a, (p • S) a : set F.domain))) _,
  { rcases this with ⟨i, j, hij, t, ht⟩,
    use [i, j, hij, t],
    simp only [and_true, mem_inter_eq, subtype.coe_prop, image_smul],
    exact ht, },
  { intro p,
    exact measurable_set_preimage (measurable_id'.subtype_coe) (measurable_set_smul p hS), },
  convert hlt,
  have := F.volume_set_eq_tsum_volume_inter hS h_smul_left,
  convert this,
  ext1 l,
  dsimp only [subtype.measure_space], -- TODO lemma
  rw measure.comap_apply _ subtype.val_injective _ _ _,
  { congr,
    ext1 v,
    simp only [mem_image, mem_inter_eq, exists_and_distrib_right, exists_eq_right, subtype.exists,
      subtype.coe_mk, subtype.val_eq_coe],
    split; { intros a, rcases a with ⟨a_left, a_right⟩, split; assumption, }, },
  { intros X hX,
    convert measurable_set.subtype_image F.measurable_set_domain hX, },
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
  (F : fundamental_domain X L) (hlt : volume F.domain < volume S)
  (h_mul_left : is_mul_left_invariant ⇑(volume : measure X)) :
  ∃ (x y : X) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y), y * x⁻¹ ∈ L :=
begin
  obtain ⟨x, y, hx, hy, hne, h⟩ := exists_mul_inv_mem_lattice_of_volume_lt_volume hS F hlt _ _,
  { refine ⟨x, y, hx, hy, hne, _⟩,
    simp only [image_univ, mem_range] at h,
    obtain ⟨l, rfl⟩ := h,
    simp [subgroup.smul_def], },
  { exact h_mul_left.to_is_smul_left_invariant.to_subgroup_is_smul_left_invariant _ , },
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
  rw [comap_apply, image_smul, smul_univ_pi ι],
  { erw pi_pi,
    { conv in (r • _)
      { rw ← inv_inv' r, },
      conv in (volume (r⁻¹⁻¹ • _))
      { rw ← preimage_smul' (inv_ne_zero (ne_of_gt hr)), },
      simp only [algebra.id.smul_eq_mul],
      rw [fintype.card, ← finset.prod_const, ← finset.prod_mul_distrib],
      congr,
      ext i : 1,
      erw ← measure.map_apply (measurable_const_mul r⁻¹) (hS i),
      conv_rhs { rw [← real.smul_map_volume_mul_left (inv_ne_zero (ne_of_gt hr))], },
      congr,
      rw [ennreal.of_real_inv_of_pos hr, abs_of_pos (inv_pos.mpr hr)], },
    { intro i,
      rw [← inv_inv' r, ← preimage_smul' (inv_ne_zero (ne_of_gt hr))],
      exact measurable_const_smul _ (hS i), }, },
  { exact smul_right_injective (ι → ℝ) (ne_of_gt hr), },
  { intros S hS,
    rw [image_smul, ← inv_inv' r, ← preimage_smul' (ne_of_gt (inv_pos.mpr hr))],
    apply measurable_set_preimage _ hS,
    rw measurable_const_smul_iff' (ne_of_gt (inv_pos.mpr hr)),
    exact measurable_id',
    apply_instance, },
  { exact measurable_set.univ_pi_fintype hS, },
end

open ennreal fintype

-- TODO version for any real vector space in terms of dimension
lemma exists_nonzero_mem_lattice_of_volume_mul_two_pow_card_lt_volume [fintype ι]
  (L : add_subgroup (ι → ℝ)) [encodable.{u} L] (F : add_fundamental_domain (ι → ℝ) L)
  (S : set (ι → ℝ)) (hS : measurable_set S) (h : volume F.domain * 2 ^ (card ι) < volume S)
  (h_symm : ∀ x ∈ S, -x ∈ S) (h_conv : convex ℝ S) : ∃ (x : L) (h : x ≠ 0), (x : ι → ℝ) ∈ S :=
begin
  have mhalf : measurable_set ((1/2 : ℝ) • S),
  { convert measurable_const_smul (2 : ℝ) hS,
    ext x,
    simp only [one_div, set.mem_preimage],
    exact mem_inv_smul_set_iff' two_ne_zero S x, },
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
      rw [image_smul, ← preimage_smul'],
      { apply measurable_set_preimage _ hS,
        rw measurable_const_smul_iff',
        exact measurable_id',
        exact two_ne_zero, },
      { exact two_ne_zero, }, }, },
  have h2 : volume F.domain < volume ((1/2 : ℝ) • S),
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
  { refine exists_add_neg_mem_lattice_of_volume_lt_volume' L mhalf F h2 _,
    rw [← pi_haar_measure_eq_lebesgue_measure _],
    exact measure.is_add_left_invariant_add_haar_measure (unit_cube _), },
end

end geometry_of_numbers
