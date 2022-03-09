/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best
-/
import algebra.order.hom.ring
import analysis.special_functions.pow

/-!
# Conditionally complete linear ordered fields

This file shows that the reals are unique, or, more formally, given a type satisfying the common
axioms of the reals (field, conditionally complete, linearly ordered) that there is an equivalence
preserving these properties to the reals. This is `cut_ordered_ring_equiv`. Moreover this
equivalence is unique.

We introduce definitions of conditionally complete linear ordered fields, and show all such are
archimedean. We also construct the natural map from a `linear_ordered_field` to such a field.

## Main definitions

* `conditionally_complete_linear_ordered_field` : A field satisfying the standard axiomatization of
  the real numbers, being a Dedekind complete and linear ordered field.
* `induced_map` : A (unique) map from any archimedean linear ordered field to a conditionally
  complete linear ordered field
* `cut_map` :

## Main results

* `ordered_ring_hom_unique` : Uniqueness of `order_ring_hom`s from
* `ordered_ring_equiv_eq_cut_ordered_ring_equiv` : Uniqueness of `order_ring_iso`s between two
  conditionally complete linearly ordered fields.

## References

* https://mathoverflow.net/questions/362991/
  who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags

reals, conditionally complete, ordered field, uniqueness
-/

variables {α β : Type*}

open function set
open_locale pointwise

lemma cSup_add [conditionally_complete_linear_order α] [add_comm_group α]
  [covariant_class α α (swap (+)) (≤)] [covariant_class α α (+) (≤)] (s t : set α)
  (hs₀ : s.nonempty) (ht₀ : t.nonempty) (hs₁ : bdd_above s) (ht₁ : bdd_above t) :
  Sup (s + t) = Sup s + Sup t :=
begin
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (hs₀.add ht₀) _ (λ a ha, _),
  { rintro f ⟨a, b, ha, hb, rfl⟩,
    exact add_le_add (le_cSup hs₁ ha) (le_cSup ht₁ hb) },
  { obtain ⟨b, hb, hab⟩ := exists_lt_of_lt_cSup hs₀ (sub_lt_iff_lt_add.2 ha),
    obtain ⟨c, hc, hbc⟩ := exists_lt_of_lt_cSup ht₀ (sub_lt.1 hab),
    exact ⟨b + c, add_mem_add hb hc, sub_lt_iff_lt_add'.1 hbc⟩ }
end

noncomputable theory
open_locale classical

open set

/-- The natural equiv between the rationals and the rationals as a set inside any characteristic 0
  division ring. -/
def rat_equiv_of_char_zero (α : Type*) [division_ring α] [char_zero α] : ℚ ≃ range (coe : ℚ → α) :=
equiv.of_injective coe rat.cast_injective

/-- The natural equiv between the rationals as a set inside any pair of characteristic 0
  division rings -/
def range_rat_equiv (α β : Type*) [division_ring α] [char_zero α] [division_ring β] [char_zero β] :
  range (coe : ℚ → α) ≃ range (coe : ℚ → β) :=
(rat_equiv_of_char_zero α).symm.trans (rat_equiv_of_char_zero β)

@[simp] lemma range_rat_equiv_apply {q : ℚ} [division_ring α] [char_zero α] [division_ring β]
  [char_zero β] :
  range_rat_equiv α β ⟨q, mem_range_self q⟩ = ⟨q, mem_range_self q⟩ :=
by simp only [range_rat_equiv, rat_equiv_of_char_zero, function.comp_app, subtype.mk_eq_mk,
  equiv.coe_trans, rat.cast_inj, equiv.symm_apply_eq, equiv.of_injective_apply]

/-- The function sending subsets of the rationals embedded inside of one characteristic zero
division ring to the corresponding subset of a second such ring. -/
def cut_map (α β : Type*) [division_ring α] [char_zero α] [division_ring β] [char_zero β] :
  set (set.range (coe : ℚ → α)) → set (set.range (coe : ℚ → β)) :=
image $ range_rat_equiv α β

set_option old_structure_cmd true

/-- A field which is both linearly ordered and conditionally complete with respect to the order,
this is an axiomatization of the reals. -/
class conditionally_complete_linear_ordered_field (α : Type*)
  extends linear_ordered_field α, conditionally_complete_linear_order α

-- TODO conditionally_complete_lattice or conditionally_complete_linear order?

/-- The reals are a conditionally complete linearly ordered field. -/
instance : conditionally_complete_linear_ordered_field ℝ :=
{ ..real.linear_ordered_field, ..real.conditionally_complete_linear_order }

open real

/- TODO does this follow from `intermediate_value_Icc`? -/
lemma exists_rat_sqr_btwn_rat_aux (x y : ℝ) (h : x < y) (hx : 0 ≤ x) :
  ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ ↑q^2 < y :=
begin
  have hy : (0 : ℝ) ≤ y,
  { linarith },
  rw ← sqrt_lt_sqrt_iff hx at h,
  obtain ⟨q, hqx, hqy⟩ := exists_rat_btwn h,
  have hq : (0 : ℝ) ≤ q,
  { transitivity x.sqrt,
    exact real.sqrt_nonneg x,
    exact le_of_lt hqx },
  refine ⟨q, _, _, _⟩,
  { assumption_mod_cast },
  { rwa [← real.sqrt_lt_sqrt_iff hx, real.sqrt_sq hq] },
  { rwa [← real.sqrt_lt_sqrt_iff (pow_nonneg hq 2), real.sqrt_sq hq] }
end

lemma exists_rat_sqr_btwn_rat {x y : ℚ} (h : x < y) (hx : 0 ≤ x) :
  ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ q^2 < y :=
by apply_mod_cast exists_rat_sqr_btwn_rat_aux x y; assumption

/-- There is a rational square between any two elements of an archimedean ordered field. -/
lemma exists_rat_sqr_btwn [linear_ordered_field α] [archimedean α] {x y : α} (h : x < y)
  (hx : 0 ≤ x) : ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ (q^2 : α) < y :=
begin
  obtain ⟨q1, hq1x, hq1y⟩ := exists_rat_btwn h,
  obtain ⟨q2, hq2x, hq1q2⟩ := exists_rat_btwn hq1x,
  norm_cast at hq1q2,
  have : (0 : α) ≤ q2 := le_trans hx (le_of_lt hq2x),
  obtain ⟨q, hqpos, hq⟩ := exists_rat_sqr_btwn_rat hq1q2 (by exact_mod_cast this),
  refine ⟨q, hqpos, _, _⟩,
  { transitivity (q2 : α),
    exact hq2x,
    exact_mod_cast hq.1 },
  { transitivity (q1 : α),
    exact_mod_cast hq.2,
    exact hq1y }
end

/-- The lower cut of rationals inside a linear ordered field that are less than a given element of
another linear ordered field. -/
def cut_image (β : Type*) [linear_ordered_field α] [linear_ordered_field β] (x : α) : set β :=
subtype.val '' cut_map α β {t | ↑t < x}

lemma cut_image_nonempty (α β : Type*) [linear_ordered_field α] [archimedean α]
  [linear_ordered_field β] (x : α) : (cut_image β x).nonempty :=
begin
  obtain ⟨q, hq⟩ := exists_rat_lt x,
  simp only [cut_image, mem_image, exists_and_distrib_right, exists_eq_right, subtype.exists,
    subtype.coe_mk, subtype.val_eq_coe],
  refine ⟨q, mem_range_self q, _⟩,
  rw [cut_map],
  exact ⟨q, q, hq, range_rat_equiv_apply⟩,
end

lemma cut_image_bdd_above (α β : Type*) [linear_ordered_field α] [archimedean α]
  [linear_ordered_field β] (x : α) : bdd_above (cut_image β x) :=
begin
  obtain ⟨q, hq⟩ := exists_rat_gt x,
  use q,
  simp only [cut_image, mem_image, exists_and_distrib_right, exists_eq_right, subtype.exists,
    subtype.coe_mk, subtype.val_eq_coe],
  rintro t ⟨⟨q2, rfl⟩, ⟨f, q3, rfl⟩, ht1, ht2⟩,
  erw range_rat_equiv_apply at ht2,
  simp only [subtype.mk_eq_mk, rat.cast_inj, rat.cast_le] at ht2 ⊢,
  rw ← ht2,
  suffices : (q3 : α) ≤ q,
  { exact_mod_cast this },
  rw [mem_def, subtype.coe_mk] at ht1,
  exact le_of_lt (lt_trans ht1 hq),
end

lemma cut_image_subset (β : Type*) [linear_ordered_field α] [linear_ordered_field β] {x y : α}
  (h : x ≤ y) : cut_image β x ⊆ cut_image β y :=
begin
  rintro t ⟨⟨y, q, rfl⟩, ⟨⟨q2, q3, rfl⟩, ht2, ht3⟩, rfl⟩,
  erw [←ht3, range_rat_equiv_apply],
  exact mem_image_of_mem _ ⟨⟨q3, mem_range_self q3⟩, lt_of_lt_of_le ht2 h, range_rat_equiv_apply⟩,
end

lemma mem_cut_image_iff [linear_ordered_field α] [linear_ordered_field β] {x : α} {t : β} :
  t ∈ cut_image β x ↔ ∃ q : ℚ, (q : β) = t ∧ (q : α) < x :=
begin
  rw cut_image,
  simp only [mem_image, exists_and_distrib_right, exists_eq_right, subtype.exists, subtype.coe_mk,
    subtype.val_eq_coe],
  split,
  { rintro ⟨⟨q, _⟩, ⟨_, q2, rfl⟩, hd, hh⟩,
    erw range_rat_equiv_apply at hh,
    simp only [subtype.mk_eq_mk, rat.cast_inj] at hh,
    exact ⟨q2, hh, hd⟩ },
  { rintro ⟨q, h, hx⟩,
    use [q, h, q, mem_range_self q],
    simp only [range_rat_equiv_apply, subtype.mk_eq_mk],
    exact ⟨hx, h⟩ }
end

lemma coe_mem_cut_image_iff [linear_ordered_field α] [linear_ordered_field β] {x : α} {q : ℚ} :
  (q : β) ∈ cut_image β x ↔ (q : α) < x :=
begin
  refine mem_cut_image_iff.trans ⟨_, λ h, ⟨q, rfl, h⟩⟩,
  rintro ⟨q2, h, he⟩,
  rwa ←rat.cast_injective h,
end

lemma cut_image_ssubset (β : Type*) [linear_ordered_field α] [archimedean α]
  [linear_ordered_field β] {a b : α} (hab : a < b) : cut_image β a ⊂ cut_image β b :=
begin
  rw ssubset_iff_subset_ne,
  refine ⟨cut_image_subset β hab.le, _⟩,
  obtain ⟨q, hx, hy⟩ := exists_rat_btwn hab,
  exact ((coe_mem_cut_image_iff.mpr hy).ne_of_not_mem' $ λ h, lt_irrefl a $ hx.trans $
    coe_mem_cut_image_iff.1 h).symm,
end

lemma cut_image_self [linear_ordered_field α] (x : α) :
  cut_image α x = Iio x ∩ range (coe : ℚ → α) :=
begin
  ext y,
  simp only [mem_cut_image_iff, mem_inter_eq, mem_Iio, mem_range],
  split,
  { rintro ⟨h, rfl, a⟩,
    exact ⟨a, h, rfl⟩ },
  { rintro ⟨h, a, rfl⟩,
    exact ⟨a, rfl, h⟩ }
end

lemma cut_image_rat [linear_ordered_field α] [linear_ordered_field β] {q : ℚ} :
  cut_image β (q : α) = subtype.val '' {t : set.range (coe : ℚ → β) | (t : β) < q} :=
begin
  ext x,
  simp only [mem_cut_image_iff, mem_range, rat.cast_lt, exists_prop, mem_image, subtype.exists,
    exists_and_distrib_right, exists_eq_right],
  split,
  { rintro ⟨q2, rfl, hq2⟩,
    exact ⟨⟨q2, rfl⟩, rat.cast_lt.mpr hq2⟩ },
  { rintro ⟨⟨q2, rfl⟩, hq⟩,
    exact ⟨q2, rfl, rat.cast_lt.mp hq⟩ }
end

open_locale pointwise

lemma cut_image_add (β : Type*) [linear_ordered_field α] [archimedean α] [linear_ordered_field β]
  (x y : α) : cut_image β (x + y) = cut_image β x + cut_image β y :=
begin
  ext t,
  refine ⟨λ h, _, _⟩,
  { rw mem_cut_image_iff at h,
    rcases h with ⟨q, rfl, h⟩,
    rw ← sub_lt_iff_lt_add at h,
    obtain ⟨q₁, hq₁q, hq₁xy⟩ := exists_rat_btwn h,
    refine ⟨q₁, q - q₁, _, _, by abel⟩; try {norm_cast};
    rw coe_mem_cut_image_iff,
    assumption,
    push_cast,
    exact sub_lt.mp hq₁q },
  { simp_rw [mem_add, mem_cut_image_iff],
    rintro ⟨_, _, ⟨qx, rfl, hx⟩, ⟨qy, rfl, hy⟩, rfl⟩,
    refine ⟨qx + qy, by norm_cast, _⟩,
    push_cast,
    exact add_lt_add hx hy }
end

lemma lt_of_mul_self_lt_mul_self [linear_ordered_comm_ring α] {a b : α} (ha : 0 ≤ a) (hb : 0 < b)
  (h : a * a < b * b) : a < b :=
begin
  rw [← sub_pos, mul_self_sub_mul_self] at h,
  rw ← sub_pos,
  exact (zero_lt_mul_left (lt_add_of_pos_of_le hb ha)).mp h,
end

lemma lt_of_pow_two_lt_pow_two [linear_ordered_comm_ring α] {a b : α} (ha : 0 ≤ a) (hb : 0 < b)
  (h : a^2 < b^2) : a < b :=
by { rw [pow_two, pow_two] at h, exact lt_of_mul_self_lt_mul_self ha hb h}

namespace conditionally_complete_linear_ordered_field

/-- Any conditionally complete linearly ordered field is archimedean. -/
@[priority 100] -- see Note [lower instance priority]
instance [conditionally_complete_linear_ordered_field α] : archimedean α :=
archimedean_iff_nat_lt.mpr
  begin
    by_contra' h,
    have : ∀ (b : α), b ∈ set.range (coe : ℕ → α) → b ≤ Sup (set.range (coe : ℕ → α)) - 1,
    { obtain ⟨x, h⟩ := h,
      have : bdd_above (set.range (coe : ℕ → α)),
      { use x,
        rintro _ ⟨n, rfl⟩,
        exact h n },
      rintro b ⟨n, rfl⟩,
      rw le_sub_iff_add_le,
      exact le_cSup _ _ this ⟨n + 1, nat.cast_succ n⟩ },
    replace := cSup_le _ _ (set.range_nonempty (coe : ℕ → α)) this,
    linarith,
  end

/-- The induced order preserving function from a linear ordered field to a conditionally complete
linear ordered field, defined by taking the Sup in the codomain of all the rationals less than the
input. -/
def induced_map (α β : Type*) [linear_ordered_field α]
  [conditionally_complete_linear_ordered_field β] : α → β :=
λ x, Sup $ cut_image β x

lemma induced_map_mono (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] :
  monotone (induced_map α β) :=
λ a b h, cSup_le_cSup (cut_image_bdd_above α β _) (cut_image_nonempty α β _) (cut_image_subset β h)

lemma induced_map_rat (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] (q : ℚ) : induced_map α β (q : α) = q :=
begin
  rw induced_map,
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_image_nonempty α β q) (λ x h, _)
    (λ w h, _),
  { simp only [cut_image_rat, mem_image, exists_and_distrib_right, exists_eq_right, subtype.exists,
      subtype.coe_mk, subtype.val_eq_coe] at h,
    rcases h with ⟨⟨q, rfl⟩, h⟩,
    exact le_of_lt h },
  { obtain ⟨q2, hq2w, hq2q⟩ := exists_rat_btwn h,
    use q2,
    simp only [cut_image_rat, mem_image, exists_eq, mem_range, exists_and_distrib_right,
      exists_eq_right, exists_prop_of_true, subtype.exists, rat.cast_inj, subtype.coe_mk,
      subtype.val_eq_coe],
    exact ⟨hq2q, hq2w⟩ }
end

lemma lt_induced_map_iff [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] {x : α} {t : β} :
  t < induced_map α β x ↔ ∃ (q : ℚ) (h : t < q), (q : α) < x :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨q, hqt, hqi⟩ := exists_rat_btwn h,
    refine ⟨q, hqt, _⟩,
    rw induced_map at hqi,
    by_contra' hx,
    have hs := cSup_le_cSup (cut_image_bdd_above α β _)
                (cut_image_nonempty α β x) (cut_image_subset α β hx),
    change _ ≤ induced_map α β q at hs,
    rw induced_map_rat at hs,
    apply lt_irrefl (q : β) (lt_of_lt_of_le hqi hs) },
  { rintro ⟨q, hqt, hqx⟩,
    transitivity (q : β),
    { exact hqt },
    { obtain ⟨q2, hq2q, hq2x⟩ := exists_rat_btwn hqx,
      rw induced_map,
      have : (q2 : β) ∈ cut_image β x := coe_mem_cut_image_iff.mpr hq2x,
      apply lt_cSup_of_lt (cut_image_bdd_above α β x) this,
      exact_mod_cast hq2q } }
end

lemma induced_map_add (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] (x y : α) :
  induced_map α β (x + y) = induced_map α β x + induced_map α β y :=
begin
  simp only [induced_map],
  rw [cut_image_add, pointwise_add_Sup _ _ (cut_image_nonempty α β x) (cut_image_nonempty α β y)
   (cut_image_bdd_above α β x) (cut_image_bdd_above α β y)],
end

/-- induced_map as an additive homomorphism -/
def induced_add_hom (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] : α →+ β :=
{ to_fun := induced_map α β,
  map_zero' := by exact_mod_cast induced_map_rat α β 0,
  map_add' := induced_map_add α β }

/-- Preparatory lemma for `induced_ring_hom` -/
lemma le_induced_mul_self_of_mem_cut_image (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] (x : α) (hx : 0 < x) (a : β)
  (ha : a ∈ cut_image β (x * x)) : a ≤ induced_add_hom α β x * induced_add_hom α β x :=
begin
  rw mem_cut_image_iff at ha,
  rcases ha with ⟨q, rfl, ha⟩,
  obtain hq | hq := le_total (q : β) 0,
  { exact hq.trans (mul_self_nonneg $ Sup $ cut_image β x) },
  have : 0 ≤ (q : α) := by exact_mod_cast hq,
  obtain ⟨q2, hqpos, hq21, hq22⟩ := exists_rat_sqr_btwn ha this,
  rw pow_two at hq22,
  have : (q2 : α) < x := lt_of_mul_self_lt_mul_self (rat.cast_nonneg.mpr hqpos) hx hq22,
  rw ← @coe_mem_cut_image_iff α β at this,
  have : (q2 : β) ≤ induced_map α β x := le_cSup _ _ (cut_image_bdd_above α β x) this,
  transitivity (q2 : β)^2,
  apply le_of_lt,
  assumption_mod_cast,
  rw pow_two,
  have q2pos : (0 : β) ≤ q2 := by exact_mod_cast hqpos,
  exact mul_le_mul this this q2pos (le_trans _ _ _ q2pos this)
end

/-- Preparatory lemma for `induced_ring_hom`. -/
lemma exists_mem_cut_image_mul_self_of_lt_induced_map_mul_self (α β : Type*)
  [linear_ordered_field α] [archimedean α] [conditionally_complete_linear_ordered_field β] (x : α)
  (hx : 0 < x) (y : β) (hyx : y < induced_add_hom α β x * induced_add_hom α β x) :
  ∃ a ∈ cut_image β (x * x), y < a :=
begin
  obtain hy | hy := lt_or_le y 0,
  { refine ⟨0, _, by rwa rat.cast_zero⟩,
    rw [coe_mem_cut_image_iff, rat.cast_zero],
      exact linear_ordered_field.mul_pos _ _ hx hx },
  obtain ⟨q2, hqpos, hq21, hq22⟩ := exists_rat_sqr_btwn hyx hy,
  rw pow_two at hq22,
  have : (q2 : β) < _ := lt_of_mul_self_lt_mul_self _ _ hq22,
  refine ⟨(q2 : β)^2, _, _⟩,
  norm_cast,
  rw coe_mem_cut_image_iff,
  erw [induced_add_hom, lt_induced_map_iff] at this,
  obtain ⟨q3, hq23, hh⟩ := this,
  rw pow_two,
  push_cast,
  have : (q2 : α) < x,
  { transitivity (q3 : α);
    assumption_mod_cast },
  apply mul_lt_mul'' this this,
  assumption_mod_cast,
  assumption_mod_cast,
  exact hq21,
  exact_mod_cast hqpos,
  simp only [induced_add_hom, add_monoid_hom.coe_mk],
  rw lt_induced_map_iff,
  obtain ⟨q3, q30, q3x⟩ := exists_rat_btwn hx,
  refine ⟨q3, _, _⟩;
    assumption_mod_cast
end

/-- `induced_map` as an `order_ring_hom`. -/
def induced_ordered_ring_hom (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] : α →+*o β :=
{ map_rel' := λ x y, induced_map_mono _ _,
  ..(induced_add_hom α β).mk_ring_hom_of_mul_self_of_two_ne_zero  -- reduce to the case of x = y
    begin
      intro x,
      -- reduce to the case of 0 < x
      suffices : ∀ (x : α), 0 < x →
        induced_add_hom α β (x * x) = induced_add_hom α β x * induced_add_hom α β x,
      { rcases lt_trichotomy x 0 with h|rfl|h,
        { rw ← neg_pos at h,
          convert this (-x) h using 1,
          { simp only [neg_mul_eq_neg_mul_symm, mul_neg_eq_neg_mul_symm, neg_neg] },
          { simp only [neg_mul_eq_neg_mul_symm, add_monoid_hom.map_neg, mul_neg_eq_neg_mul_symm,
              neg_neg] } },
        { simp only [mul_zero, add_monoid_hom.map_zero] },
        { exact this x h } },
      clear x,
      intros x hx,
    -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
    -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
    apply cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_image_nonempty α β _),
    exact le_induced_mul_self_of_mem_cut_image α β x hx,
    exact exists_mem_cut_image_mul_self_of_lt_induced_map_mul_self α β x hx,
  end two_ne_zero
  begin
    convert induced_map_rat α β 1;
    rw rat.cast_one,
    refl,
  end }

@[simp] lemma induced_map_inv_self (α β : Type*) [conditionally_complete_linear_ordered_field α]
  [conditionally_complete_linear_ordered_field β] (x : α) :
  induced_map β α (induced_map α β x) = x :=
begin
  rw induced_map,
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_image_nonempty β α (induced_map α β x))
    (λ y hy, _) (λ w hw, _),
  { rw mem_cut_image_iff at hy,
    rcases hy with ⟨q, rfl, h⟩,
    rw induced_map at h,
    obtain ⟨y, hym, hyq⟩ := exists_lt_of_lt_cSup (cut_image_nonempty α β x) h,
    rw mem_cut_image_iff at hym,
    obtain ⟨q2, rfl, h⟩ := hym,
    apply le_of_lt,
    transitivity (q2 : α),
    assumption_mod_cast,
    assumption },
  { obtain ⟨q, hqw, hqx⟩ := exists_rat_btwn hw,
    refine ⟨q, _, _⟩,
    { rw [coe_mem_cut_image_iff, lt_induced_map_iff],
      obtain ⟨q2, hq2q, hq2x⟩ := exists_rat_btwn hqx,
      refine ⟨q2, _, _⟩,
      exact_mod_cast hq2q,
      exact_mod_cast hq2x },
    { exact_mod_cast hqw } }
end

/-- The equivalence of ordered rings between two conditionally complete linearly ordered fields. -/
def cut_ordered_ring_equiv (α β : Type*)
  [conditionally_complete_linear_ordered_field α] [conditionally_complete_linear_ordered_field β] :
  α ≃+*o β :=
{ inv_fun := induced_map β α,
  left_inv := induced_map_inv_self α β,
  right_inv := induced_map_inv_self β α,
  map_rel_iff' := λ x y, begin
    refine ⟨λ h, _, induced_map_le _ _⟩,
    simpa [induced_ordered_ring_hom, add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero,
      induced_add_hom] using induced_map_le β α h,
  end,
  ..induced_ordered_ring_hom α β }

lemma cut_ordered_equiv_coe_fun (α β : Type*)
  [conditionally_complete_linear_ordered_field α] [conditionally_complete_linear_ordered_field β] :
  (cut_ordered_ring_equiv α β : α → β) = induced_map α β := rfl

lemma cut_ordered_ring_equiv_symm (α β : Type*)
  [conditionally_complete_linear_ordered_field α] [conditionally_complete_linear_ordered_field β] :
  (cut_ordered_ring_equiv α β).symm = cut_ordered_ring_equiv β α := rfl

@[simp]
lemma cut_ordered_ring_equiv_self (α : Type*) [conditionally_complete_linear_ordered_field α] :
  cut_ordered_ring_equiv α α = order_ring_iso.refl α :=
begin
  ext,
  change induced_map α α x = _,
  simp only [order_ring_iso.refl_apply, induced_map, cut_image_self],
  apply cSup_eq_of_forall_le_of_forall_lt_exists_gt,
  { obtain ⟨q, h⟩ := exists_rat_lt x,
    exact ⟨q, h, mem_range_self _⟩ },
  { rintro y ⟨hlt, _⟩,
    exact le_of_lt hlt },
  { rintro y hlt,
    obtain ⟨q, hyq, hqx⟩ := exists_rat_btwn hlt,
    exact ⟨q, ⟨hqx, mem_range_self _⟩, hyq⟩ }
end

@[simp] lemma ring_hom_rat [division_ring α] [division_ring β] [char_zero α] (f : α →+* β) (q : ℚ) :
  f q = q :=
begin
  suffices : f.comp (rat.cast_hom α) q = q,
  { simpa },
  exact ring_hom.map_rat_cast _ q,
end

@[simp] lemma ordered_ring_hom_rat [linear_ordered_field α] [linear_ordered_field β] (f : α →+*o β)
  (q : ℚ) : f q = q :=
begin
  suffices : (f : α →+* β).comp (rat.cast_hom α) q = q,
  { simpa },
  exact ring_hom.map_rat_cast _ q,
end

@[simp] lemma ordered_ring_equiv_rat [division_ring α] [char_zero α] [has_le α] [has_le β]
  [division_ring β] (f : α ≃+*o β) (q : ℚ) : f q = q :=ring_hom_rat (f : α →+* β) q

open order_ring_iso

/-- There is a unique ordered ring homomorphism from an archimedean linear ordered field to a
conditionally complete linear ordered field. -/
instance [linear_ordered_field α] [archimedean α] [conditionally_complete_linear_ordered_field β] :
  unique (α →+*o β) :=
{ default := induced_ordered_ring_hom α β,
  uniq := λ f, begin
  ext,
  wlog h : f x ≤ g x using [f g, g f],
  exact le_total (f x) (g x),
  rw le_iff_lt_or_eq at h,
  rcases h with h | h,
  { rcases exists_rat_btwn h with ⟨q, hqf, hqg⟩,
    rw ← ring_hom_rat (f : α →+* β) at hqf,
    rw ← ring_hom_rat (g : α →+* β) at hqg,
    rcases lt_trichotomy x q with h' | rfl | h',
    swap, { simp },
    all_goals { replace h' := le_of_lt h' },
    { replace h' := g.map_le h', simp only [ring_hom_rat, ordered_ring_hom_rat] at *, linarith },
    { replace h' := f.map_le h', simp only [ring_hom_rat, ordered_ring_hom_rat] at *, linarith } },
  { exact h }
end }

lemma ordered_ring_equiv_unique [linear_ordered_field α]
  [conditionally_complete_linear_ordered_field β] (f g : α ≃+*o β) : f = g :=


instance [conditionally_complete_linear_ordered_field α]
  [conditionally_complete_linear_ordered_field β] : unique (α ≃+*o β) :=
{ default := cut_ordered_ring_equiv α β,
  uniq := λ f, begin
    ext,
    exact order_ring_hom.congr_fun (ordered_ring_hom_unique (f : α →+*o β) (g : α →+*o β)) x,
  end }

end conditionally_complete_linear_ordered_field
