/-
Copyright (c) 2021 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import measure_theory.measure.haar_lebesgue
import analysis.convex.basic
import algebra.ordered_pointwise
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

lemma smul_pi {K : Type*} [group_with_zero K] (ι : Type*) {r : K} (t : ι → set K) (S : set ι)
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

-- For now we do not extend left coset even though this is essentially just a measurable coset,
-- as the most general definition of fundamental domain may want to include measure zero boundary
-- overlaps for instance.
/-- A fundamental domain for a subgroup of an additive group is a measurable coset for the group -/
structure add_fundamental_domain {X : Type*} (Y : Type*) [measurable_space Y] [add_group X]
  (L : add_subgroup X) [has_vadd X Y] :=
(F : set Y)
(hF : measurable_set F)
(disjoint : ∀ (l : X) (hl : l ∈ L) (h : l ≠ 0), disjoint ((+ᵥ) l '' F) F)
(covers : ∀ (x : Y), ∃ (l : X) (hl : l ∈ L), l +ᵥ x ∈ F)
@[to_additive add_fundamental_domain]
structure fundamental_domain {X : Type*} (Y : Type*) [measurable_space Y] [group X]
  (L : subgroup X) [has_scalar X Y] :=
(F : set Y)
(hF : measurable_set F)
(disjoint : ∀ (l : X) (hl : l ∈ L) (h : l ≠ 1), disjoint ((•) l '' F) F)
(covers : ∀ (x : Y), ∃ (l : X) (hl : l ∈ L), l • x ∈ F)
--TODO all f.d.s have same measure https://arxiv.org/pdf/1405.2119.pdf

-- instance : inhabited (fundamental_domain (⊤ : add_subgroup (fin 0 → ℝ))) :=
-- { default := { F := ⊤,
--   hF := subsingleton.measurable_set,
--   disjoint := λ v hv hvnz, by simp at *; assumption,
--   covers := λ v, by simp } }

@[to_additive]
lemma fundamental_domain.exists_unique {X Y : Type*} [measurable_space Y] [group X]
  [mul_action X Y] {L : subgroup X} (F : fundamental_domain Y L) (x : Y) :
  ∃! (p : L), x ∈ ((•) (p : X)) '' F.F :=
exists_unique_of_exists_of_unique
begin
  simp only [exists_prop, set.mem_preimage, set.image_smul, exists_unique_iff_exists],
  obtain ⟨l, hl, lh⟩ := F.covers x,
  use l⁻¹,
  exact L.inv_mem hl,
  simp only [subgroup.coe_mk],
  refine mem_smul_set.mpr _,
  refine ⟨_, lh, _⟩,
  simp only [inv_smul_smul], -- TODO clean up this ugliness
end
begin
  rintro ⟨y₁_val, y₁_property⟩ ⟨y₂_val, y₂_property⟩ ⟨a, ha, rfl⟩ ⟨c, hc, h⟩,
  simp only [subtype.mk_eq_mk, subgroup.coe_mk] at *,
  -- replace h := h.symm,
  -- rw [← neg_vadd_eq_iff_eq_vadd, ← add_assoc] at h,
  have := F.disjoint (y₂_val⁻¹ * y₁_val) (L.mul_mem (L.inv_mem y₂_property) y₁_property),
  contrapose! this,
  simp only [inv_mul_eq_iff_eq_mul, mul_one, image_mul_left, ne.def, inv_mul_cancel, inv_inv],
  split,
  { exact this, },
  intro hd,
  apply hd ⟨_, hc⟩,
  erw mem_smul_set,
  rw ← eq_inv_smul_iff at h,
  rw [h],
  refine ⟨a, ha, _⟩, -- TODO also ugly
  rw mul_smul,
end

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
  { intros x hx,
    exact measurable_set.subtype_image hmp hx, },
  { exact measurable_set.univ, }
end

open measure_theory
/-- Blichfeldt's Principle --/
-- TODO this version when it makes sense
@[to_additive]
lemma exists_mul_inv_mem_lattice_of_volume_lt_volume {X Y : Type*} [measurable_space X]
  [measure_space Y] [group X] [mul_action X Y]
  [has_measurable_smul X Y] (L : subgroup X) [encodable L] {S : set Y} (hS : measurable_set S)
  (F : fundamental_domain Y L) (hlt : volume F.F < volume S)
  (h_smul_left : is_smul_left_invariant X ⇑(volume : measure Y))
  (hnostab : ∀ (p₁ p₂ : L) (q : Y) (hq : q ∈ S) (hppq : p₁ • q = p₂ • q), p₁ = p₂) :
  ∃ (x y : Y) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y), y ∈ (• x) '' (L : set X) :=
begin
  suffices : ∃ (p₁ p₂ : L) (hne : p₁ ≠ p₂),
    (((•) (p₁ : X) '' S ∩ F.F) ∩ ((•) (p₂ : X) '' S ∩ F.F)).nonempty,
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
      exact L.mul_mem (L.inv_mem (set_like.coe_mem _)) (set_like.coe_mem _),
      rw [mul_smul, ht₁, ← ht₂, ← mul_smul, inv_mul_self, one_smul], },
  end,
  rw ← volume_subtype_univ F.hF at hlt,
  have := exists_nonempty_inter_of_measure_univ_lt_tsum_measure subtype.measure_space.volume
    (_ : (∀ p : L, measurable_set (λ a, (((•) (p : X)) '' S) a : set F.F))) _,
  { rcases this with ⟨i, j, hij, t, ht⟩,
    use [i, j, hij, t],
    simp only [and_true, set.mem_inter_eq, set.mem_preimage, subtype.coe_prop],
    exact ht, },
  { intros,
    erw [image_smul, ← inv_inv p, ← preimage_smul (p⁻¹ : X) S],
    exact measurable_set_preimage
      ((measurable_const_smul (p⁻¹ : X)).comp measurable_subtype_coe) hS, },
  convert hlt,
  have : (∑' (i : L), volume ((•) (i : X) '' S ∩ F.F)) = volume S,
  { rw (_ : ∑' (i : L), volume (((•) (i : X)) '' S ∩ F.F) =
        ∑' (i : L), volume ((•) (i⁻¹ : X) '' ((•) (i : X) '' S ∩ F.F))),
    { have : ∀ (i : L) (x : Y)
        -- (hx : x ∈ F.F)
        (y : Y)
        -- (hy : y ∈ (•) (i : X) '' S)
        (hi : (i⁻¹ : X) • x = (i⁻¹ : X) • y), x = y,
      { intros,
        have := congr_arg ((•) (i : X)) hi,
        simpa, },
      conv in (_ '' (_ ∩ _)) {
        rw [← set.image_inter (this i), ← set.image_comp],
        simp [inv_smul_smul],
        -- simp only [function.comp_app, set.image_id',
        --   comp_add_right, add_zero, add_right_neg, set.image_add_right, neg_neg],
        rw set.inter_comm, },
      rw ← measure_Union _ _,
      { congr,
        rw [← set.Union_inter, set.inter_eq_self_of_subset_right],
        convert set.subset_univ _,
        rw set.eq_univ_iff_forall,
        intros,
        rw set.mem_Union,
        rcases F.covers x with ⟨w, t, h_1_h⟩,
        use ⟨w, t⟩,
        simp only [subgroup.coe_mk],
        rw ← preimage_smul (w : X),
        rwa [set.mem_preimage], },
      { apply_instance, },
      { intros x y hxy,
        suffices : (disjoint on λ (i : ↥(L)), (λ (_x : Y), (i⁻¹  : X) • _x) '' F.F) x y,
        { simp only [comp_add_right, mul_one, mul_right_inv,
            set.image_mul_right, inv_inv, set.image_id'] at this ⊢,
          rintros z ⟨⟨hzx, hzS⟩, ⟨hzy, hzS⟩⟩,
          apply this,
          simp only [set.mem_preimage, set.mem_inter_eq, set.inf_eq_inter],
          exact ⟨hzx, hzy⟩, },
        rintros t ⟨htx, hty⟩,
        simp only [set.mem_empty_eq, set.mem_preimage, set.bot_eq_empty,
          set.image_mul_right, inv_inv] at htx hty ⊢,
        apply hxy,
        suffices : x⁻¹ = y⁻¹, by simpa using this,
        apply exists_unique.unique (F.exists_unique t) _ _; simpa, },
      { intro l,
        apply measurable_set.inter _ hS,
        rw ← preimage_smul (l : X),
        refine measurable_set_preimage _ F.hF,
        exact measurable_const_smul (l : X), }, },
    { congr,
      ext1 l,
      simp only [image_smul],
      simp_rw ← preimage_smul (l : X),
      rw h_smul_left (l : X),
      apply measurable_set.inter _ F.hF, -- TODO is this a dup goal?
      rw [← inv_inv (l : X), ← preimage_smul (l⁻¹ : X)],
      refine measurable_set_preimage _ hS,
      exact measurable_const_smul _, }, },
  convert this,
  ext1 l,
  simp only [image_smul],
  dsimp only [subtype.measure_space], -- TODO lemma
  rw measure.comap_apply _ subtype.val_injective _ _ _,
  { congr,
    ext1 v,
    simp only [set.mem_preimage, set.mem_image, set.mem_inter_eq, exists_and_distrib_right,
      exists_eq_right, subtype.exists, subtype.coe_mk, subtype.val_eq_coe],
    cases l, rcases hlt with ⟨⟨hlt_w_val, hlt_w_property⟩, hlt_h_w, hlt_h_h⟩,
    simp only [set.image_mul_right, subgroup.coe_mk, option.mem_def,
      ennreal.some_eq_coe, add_subgroup.coe_mk],
    split; { intros a, rcases a with ⟨a_left, a_right⟩, split; assumption, }, },
  { intros X hX,
    convert measurable_set.subtype_image F.hF hX, },
  { erw [← inv_inv l, ← preimage_smul (l⁻¹ : X) S],
    exact measurable_set_preimage
      ((measurable_const_smul (l⁻¹ : X)).comp measurable_subtype_coe) hS, },
end
-- TODO version giving `ceiling (volume S / volume F)` points whose difference is in a subgroup
-- needs the m-fold version of exists_nonempty_inter_of_measure_univ_lt_tsum_measure when
-- measure > m * measure giving some x in m sets
@[to_additive]
lemma exists_mul_inv_mem_lattice_of_volume_lt_volume' {X : Type*} [measure_space X] [comm_group X]
  [has_measurable_mul X] (L : subgroup X) [encodable L] {S : set X} (hS : measurable_set S)
  (F : fundamental_domain X L) (hlt : volume F.F < volume S)
  (h_mul_left : is_mul_left_invariant ⇑(volume : measure X)) :
  ∃ (x y : X) (hx : x ∈ S) (hy : y ∈ S) (hne : x ≠ y), y * x⁻¹ ∈ L :=
begin
  obtain ⟨x, y, hx, hy, hne, h⟩ := exists_mul_inv_mem_lattice_of_volume_lt_volume L hS F hlt
    h_mul_left.to_is_smul_left_invariant _,
  { refine ⟨x, y, hx, hy, hne, _⟩,
    simpa only [smul_eq_mul, image_mul_right, mem_preimage, set_like.mem_coe] using h, },
  { rintros ⟨p₁, hp₁⟩ ⟨p₂, hp₂⟩ q hq hleft,
    change _ * _ = _ * _ at hleft, -- TODO this is nasty
    simp only [submonoid.coe_subtype, mul_left_inj, subgroup.coe_mk] at hleft,
    ext,
    simpa, },
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
  erw pi_pi,
  conv in (r • _)
  { rw ← inv_inv' r, },
  conv in (volume (r⁻¹⁻¹ • _))
  { rw ← preimage_smul' (inv_ne_zero (ne_of_gt hr)), },
  simp only [algebra.id.smul_eq_mul],
  rw [fintype.card, ← finset.prod_const, ← finset.prod_mul_distrib],
  congr,
  ext i : 1,
  erw ← measure.map_apply _ _,
  conv_rhs { rw [← real.smul_map_volume_mul_left (inv_ne_zero (ne_of_gt hr))], },
  congr,
  rw ennreal.of_real_inv_of_pos hr,
  rw abs_of_pos (inv_pos.mpr hr),
  exact measurable_const_mul r⁻¹,
  exact hS i,
  { intro i,
    rw [← inv_inv' r, ← preimage_smul' (inv_ne_zero (ne_of_gt hr))],
    exact measurable_const_smul _ (hS i), },
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
  (S : set (ι → ℝ)) (hS : measurable_set S) (h : volume F.F * 2 ^ (card ι) < volume S)
  (h_symm : ∀ x ∈ S, -x ∈ S) (h_conv : convex S) : ∃ (x : L) (h : x ≠ 0), (x : ι → ℝ) ∈ S :=
begin
  have mhalf : measurable_set ((1/2 : ℝ) • S),
  { convert measurable_const_smul (2 : ℝ) hS,
    ext x,
    simp only [one_div, set.mem_preimage],
    exact mem_inv_smul_set_iff two_ne_zero S x, },
  have : volume ((1/2 : ℝ) • S) * 2 ^ (card ι) = volume S,
  { suffices : volume ((1/2 : ℝ) • S) = (1 / 2) ^ (card ι) * volume S,
    { rw [this, mul_comm _ (volume S), mul_assoc, ← mul_pow, one_div,
        ennreal.inv_mul_cancel two_ne_zero two_ne_top, one_pow, mul_one], },
    have := rescale ι (half_pos zero_lt_one),
    simp only [one_div, fintype.card_fin] at this ⊢,
    rw ← ennreal.of_real_inv_of_pos (by norm_num : 0 < (2 : ℝ)) at this,
    simp only [zero_le_one, of_real_one, of_real_bit0] at this,
    rw [← measure.smul_apply, ← this, comap_apply _ _ _ _ hS],
    simp,
    { exact smul_right_injective _ (by norm_num), },
    { intros S hS,
      rw [image_smul, ← preimage_smul' _],
      apply measurable_set_preimage _ hS,
      rw measurable_const_smul_iff' _,
      exact measurable_id',
      apply_instance,
      apply_instance,
      exact two_ne_zero,
      exact two_ne_zero, }, },
  have h2 : volume F.F < volume ((1/2 : ℝ) • S),
  { rw ← ennreal.mul_lt_mul_right (pow_ne_zero (card ι) two_ne_zero') (pow_ne_top two_ne_top),
    convert h, },

  have : (1 / 2 + 1 / 2 : ℝ) • S = (1/2 : ℝ) • S + (1/2 : ℝ) • S,
  from (have honehalf : 0 ≤ (1 / 2 : ℝ) := by norm_num, h_conv.add_smul honehalf honehalf),
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
