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
preserving these properties to the reals. This is `cut_order_ring_iso`. Moreover this
equivalence is unique.

We introduce definitions of conditionally complete linear ordered fields, and show all such are
archimedean. We also construct the natural map from a `linear_ordered_field` to such a field.

## Main definitions

* `conditionally_complete_linear_ordered_field` : A field satisfying the standard axiomatization of
  the real numbers, being a Dedekind complete and linear ordered field.
* `induced_map` : A (unique) map from any archimedean linear ordered field to a conditionally
  complete linear ordered field

## Main results

* `order_ring_hom_unique` : Uniqueness of `order_ring_hom`s from
* `order_ring_iso_eq_cut_order_ring_iso` : Uniqueness of `order_ring_iso`s between two
  conditionally complete linearly ordered fields.

## References

* https://mathoverflow.net/questions/362991/
  who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags

reals, conditionally complete, ordered field, uniqueness
-/

variables {F α β : Type*}

open function set
open_locale pointwise

@[to_additive] lemma cSup_mul [conditionally_complete_linear_order α] [comm_group α]
  [covariant_class α α (swap (*)) (≤)] [covariant_class α α (*) (≤)] (s t : set α)
  (hs₀ : s.nonempty) (ht₀ : t.nonempty) (hs₁ : bdd_above s) (ht₁ : bdd_above t) :
  Sup (s * t) = Sup s * Sup t :=
begin
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (hs₀.mul ht₀) _ (λ a ha, _),
  { rintro f ⟨a, b, ha, hb, rfl⟩,
    exact mul_le_mul' (le_cSup hs₁ ha) (le_cSup ht₁ hb) },
  { obtain ⟨b, hb, hab⟩ := exists_lt_of_lt_cSup hs₀ (div_lt_iff_lt_mul.2 ha),
    obtain ⟨c, hc, hbc⟩ := exists_lt_of_lt_cSup ht₀ (div_lt''.1 hab),
    exact ⟨b * c, mul_mem_mul hb hc, div_lt_iff_lt_mul'.1 hbc⟩ }
end

@[to_additive] lemma cInf_mul [conditionally_complete_linear_order α] [comm_group α]
  [covariant_class α α (swap (*)) (≤)] [covariant_class α α (*) (≤)] (s t : set α)
  (hs₀ : s.nonempty) (ht₀ : t.nonempty) (hs₁ : bdd_below s) (ht₁ : bdd_below t) :
  Inf (s * t) = Inf s * Inf t :=
begin
  refine cInf_eq_of_forall_ge_of_forall_gt_exists_lt (hs₀.mul ht₀) _ (λ a ha, _),
  { rintro f ⟨a, b, ha, hb, rfl⟩,
    exact mul_le_mul' (cInf_le hs₁ ha) (cInf_le ht₁ hb) },
  { obtain ⟨b, hb, hab⟩ := exists_lt_of_cInf_lt hs₀ (lt_div_iff_mul_lt.2 ha),
    obtain ⟨c, hc, hbc⟩ := exists_lt_of_cInf_lt ht₀ (lt_div''.1 hab),
    exact ⟨b * c, mul_mem_mul hb hc, lt_div_iff_mul_lt'.1 hbc⟩ }
end

@[simp] lemma map_rat_cast [division_ring α] [division_ring β] [char_zero α] [ring_hom_class F α β]
  (f : F) (q : ℚ) :
  f q = q :=
ring_hom.map_rat_cast (f : α →+* β) _

lemma order_ring_iso.to_order_ring_hom_injective [non_assoc_semiring α] [preorder α]
  [non_assoc_semiring β] [preorder β] :
  injective (order_ring_iso.to_order_ring_hom : (α ≃+*o β) → α →+*o β) :=
λ f g h, fun_like.coe_injective $ by convert fun_like.ext'_iff.1 h

lemma lt_of_mul_self_lt_mul_self [linear_ordered_semiring α] {a b : α} (hb : 0 ≤ b)
  (h : a * a < b * b) : a < b :=
by { simp_rw ←sq at h, exact lt_of_pow_lt_pow _ hb h }

lemma le_of_forall_rat_lt_imp_le [linear_ordered_field α] [archimedean α] {x y : α}
  (h : ∀ q : ℚ, (q : α) < x → (q : α) ≤ y) : x ≤ y :=
le_of_not_lt $ λ hyx, let ⟨q, hy, hx⟩ := exists_rat_btwn hyx in hy.not_le $ h _ hx

lemma le_of_forall_lt_rat_imp_le [linear_ordered_field α] [archimedean α] {x y : α}
  (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y :=
(le_of_not_lt $ λ hyx, let ⟨q, hy, hx⟩ := exists_rat_btwn hyx in hx.not_le $ h _ hy)

lemma eq_of_forall_rat_lt_iff_lt [linear_ordered_field α] [archimedean α] {x y : α}
  (h : ∀ q : ℚ, (q : α) < x ↔ (q : α) < y) : x = y :=
(le_of_forall_rat_lt_imp_le $ λ q hq, ((h q).1 hq).le).antisymm $ le_of_forall_rat_lt_imp_le $
  λ q hq, ((h q).2 hq).le

lemma eq_of_forall_lt_rat_iff_lt [linear_ordered_field α] [archimedean α] {x y : α}
  (h : ∀ q : ℚ, x < q ↔ y < q) : x = y :=
(le_of_forall_lt_rat_imp_le $ λ q hq, ((h q).2 hq).le).antisymm $ le_of_forall_lt_rat_imp_le $
  λ q hq, ((h q).1 hq).le

noncomputable theory
open_locale classical

open set

/-- The natural equiv between the rationals and the rationals as a set inside any characteristic 0
  division ring. -/
def range_coe_equiv_rat (α : Type*) [division_ring α] [char_zero α] :
  range (coe : ℚ → α) ≃ ℚ :=
(equiv.of_injective coe rat.cast_injective).symm

@[simp] lemma range_coe_equiv_rat_symm_apply [division_ring α] [char_zero α] (q : ℚ) :
  (range_coe_equiv_rat α).symm q = ⟨q, mem_range_self _⟩ := rfl

@[simp] lemma range_coe_equiv_rat_coe [division_ring α] [char_zero α] (q : ℚ) :
  range_coe_equiv_rat α ⟨q, mem_range_self _⟩ = q :=
(equiv.apply_eq_iff_eq_symm_apply _).2 rfl

/-- The natural equiv between the rationals as a set inside any pair of characteristic 0
  division rings -/
def range_rat_equiv (α β : Type*) [division_ring α] [char_zero α] [division_ring β]
  [char_zero β] :
  range (coe : ℚ → α) ≃ range (coe : ℚ → β) :=
(range_coe_equiv_rat α).trans (range_coe_equiv_rat β).symm

@[simp] lemma range_rat_equiv_apply_coe [division_ring α] [char_zero α] [division_ring β]
  [char_zero β] (q : ℚ):
  range_rat_equiv α β ⟨q, mem_range_self q⟩ = ⟨q, mem_range_self q⟩ :=
by simp only [range_rat_equiv, equiv.coe_trans, comp_app, range_coe_equiv_rat_coe,
  range_coe_equiv_rat_symm_apply]

set_option old_structure_cmd true

/-- A field which is both linearly ordered and conditionally complete with respect to the order,
this is an axiomatization of the reals. -/
class conditionally_complete_linear_ordered_field (α : Type*)
  extends linear_ordered_field α renaming max → sup min → inf, conditionally_complete_linear_order α

-- TODO conditionally_complete_lattice or conditionally_complete_linear order?

/-- The reals are a conditionally complete linearly ordered field. -/
instance : conditionally_complete_linear_ordered_field ℝ :=
{ ..real.linear_ordered_field, ..real.conditionally_complete_linear_order }

open real

lemma lt_sq_of_sqrt_lt {x y : ℝ} (h : sqrt x < y) : x < y ^ 2 :=
by { have hy := x.sqrt_nonneg.trans_lt h,
  rwa [←sqrt_lt_sqrt_iff_of_pos (sq_pos_of_pos hy), sqrt_sq hy.le] }

/- TODO does this follow from `intermediate_value_Icc`? -/
lemma exists_rat_sq_btwn_rat_aux (x y : ℝ) (h : x < y) (hy : 0 < y) :
  ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ ↑q^2 < y :=
begin
  rw ←sqrt_lt_sqrt_iff_of_pos hy at h,
  obtain ⟨q, hxq, hqy⟩ := exists_rat_btwn h,
  have hq : (0 : ℝ) ≤ q := x.sqrt_nonneg.trans hxq.le,
  refine ⟨q, _, lt_sq_of_sqrt_lt hxq, _⟩,
  { assumption_mod_cast },
  { rwa [←real.sqrt_lt_sqrt_iff (pow_nonneg hq 2), real.sqrt_sq hq] }
end

lemma exists_rat_sq_btwn_rat {x y : ℚ} (h : x < y) (hy : 0 < y) :
  ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ q^2 < y :=
by apply_mod_cast exists_rat_sq_btwn_rat_aux x y; assumption

/-- There is a rational square between any two positive elements of an archimedean ordered field. -/
lemma exists_rat_sq_btwn [linear_ordered_field α] [archimedean α] {x y : α} (h : x < y)
  (hy : 0 < y) : ∃ q : ℚ, 0 ≤ q ∧ x < q^2 ∧ (q^2 : α) < y :=
begin
  obtain ⟨q₂, hx₂, hy₂⟩ := exists_rat_btwn (max_lt h hy),
  obtain ⟨q₁, hx₁, hq₁₂⟩ := exists_rat_btwn hx₂,
  have : (0 : α) < q₂ := (le_max_right _ _).trans_lt hx₂,
  norm_cast at hq₁₂ this,
  obtain ⟨q, hq, hq₁, hq₂⟩ := exists_rat_sq_btwn_rat hq₁₂ this,
  refine ⟨q, hq, (le_max_left _ _).trans_lt $ hx₁.trans _, _⟩,
  { exact_mod_cast hq₁ },
  { transitivity (q₂ : α),
    exact_mod_cast hq₂,
    exact hy₂ }
end

/-- The lower cut of rationals inside a linear ordered field that are less than a given element of
another linear ordered field. -/
def cut_image (β : Type*) [linear_ordered_field α] [linear_ordered_field β] (x : α) : set β :=
subtype.val ∘ range_rat_equiv α β '' {t | ↑t < x}

@[simp] lemma mem_cut_image_iff [linear_ordered_field α] [linear_ordered_field β] {x : α} {t : β} :
  t ∈ cut_image β x ↔ ∃ q : ℚ, (q : β) = t ∧ (q : α) < x :=
begin
  rw cut_image,
  split,
  { rintro ⟨⟨_, q, rfl⟩, hq, rfl⟩,
    exact ⟨q, congr_arg coe (range_coe_equiv_rat_coe _).symm, hq⟩ },
  { rintro ⟨q, rfl, hq⟩,
    exact ⟨⟨q, mem_range_self _⟩, hq, congr_arg coe $ range_coe_equiv_rat_coe _⟩ }
end

lemma cut_image_nonempty (β : Type*) [linear_ordered_field α] [archimedean α]
  [linear_ordered_field β] (x : α) : (cut_image β x).nonempty :=
let ⟨q, hq⟩ := exists_rat_lt x in nonempty.image _ ⟨⟨q, mem_range_self _⟩, hq⟩

lemma cut_image_bdd_above (β : Type*) [linear_ordered_field α] [archimedean α]
  [linear_ordered_field β] (x : α) : bdd_above (cut_image β x) :=
begin
  obtain ⟨q, hq⟩ := exists_rat_gt x,
  use q,
  simp_rw [mem_upper_bounds, mem_cut_image_iff],
  rintro _ ⟨r, rfl, hr⟩,
  exact_mod_cast hr.le.trans hq.le,
end

lemma cut_image_mono (β : Type*) [linear_ordered_field α] [linear_ordered_field β] {x y : α}
  (h : x ≤ y) : cut_image β x ⊆ cut_image β y :=
image_subset _ $ λ t ht, lt_of_lt_of_le ht h

@[simp] lemma coe_mem_cut_image_iff [linear_ordered_field α] [linear_ordered_field β] {x : α}
  {q : ℚ} :
  (q : β) ∈ cut_image β x ↔ (q : α) < x :=
begin
  refine mem_cut_image_iff.trans ⟨_, λ h, ⟨q, rfl, h⟩⟩,
  rintro ⟨r, h, hr⟩,
  rwa ←rat.cast_injective h,
end

lemma cut_image_ssubset (β : Type*) [linear_ordered_field α] [archimedean α]
  [linear_ordered_field β] {a b : α} (hab : a < b) : cut_image β a ⊂ cut_image β b :=
begin
  rw ssubset_iff_subset_ne,
  refine ⟨cut_image_mono β hab.le, _⟩,
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

lemma cut_image_coe [linear_ordered_field α] [linear_ordered_field β] {q : ℚ} :
  cut_image β (q : α) = subtype.val '' {t : set.range (coe : ℚ → β) | (t : β) < q} :=
begin
  ext x,
  simp only [mem_cut_image_iff, mem_range, rat.cast_lt, exists_prop, mem_image, subtype.exists,
    exists_and_distrib_right, exists_eq_right],
  split,
  { rintro ⟨r, rfl, hr⟩,
    exact ⟨⟨r, rfl⟩, rat.cast_lt.mpr hr⟩ },
  { rintro ⟨⟨r, rfl⟩, hq⟩,
    exact ⟨r, rfl, rat.cast_lt.mp hq⟩ }
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
    refine ⟨q₁, q - q₁, _, _, add_sub_cancel'_right _ _⟩; try {norm_cast};
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

namespace conditionally_complete_linear_ordered_field

/-- Any conditionally complete linearly ordered field is archimedean. -/
@[priority 100] -- see Note [lower instance priority]
instance to_archimedean [conditionally_complete_linear_ordered_field α] : archimedean α :=
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
  [conditionally_complete_linear_ordered_field β] (x : α) : β :=
Sup $ cut_image β x

lemma induced_map_mono (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] :
  monotone (induced_map α β) :=
λ a b h, cSup_le_cSup (cut_image_bdd_above β _) (cut_image_nonempty β _) (cut_image_mono β h)

lemma induced_map_rat (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] (q : ℚ) : induced_map α β (q : α) = q :=
begin
  rw induced_map,
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_image_nonempty β q) (λ x h, _)
    (λ w h, _),
  { rw [cut_image_coe] at h,
    obtain ⟨r, h, rfl⟩ := h,
    exact le_of_lt h },
  { obtain ⟨q2, hq2w, hq2q⟩ := exists_rat_btwn h,
    use q2,
    simp only [cut_image_coe, mem_image, exists_eq, mem_range, exists_and_distrib_right,
      exists_eq_right, exists_prop_of_true, subtype.exists, rat.cast_inj, subtype.coe_mk,
      subtype.val_eq_coe],
    exact ⟨hq2q, hq2w⟩ }
end

@[simp] lemma induced_map_zero (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] : induced_map α β 0 = 0 :=
by exact_mod_cast induced_map_rat α β 0

lemma rat_cast_lt_induced_map_iff [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] {x : α} {q : ℚ} :
  (q : β) < induced_map α β x ↔ (q : α) < x :=
begin
  refine ⟨λ h, _, _⟩,
  { rw ←induced_map_rat α at h,
    exact (induced_map_mono α β).reflect_lt h },
  { rintro hq,
    obtain ⟨q2, hq2q, hq2x⟩ := exists_rat_btwn hq,
    rw induced_map,
    have : (q2 : β) ∈ cut_image β x := coe_mem_cut_image_iff.mpr hq2x,
    apply lt_cSup_of_lt (cut_image_bdd_above β x) this,
    exact_mod_cast hq2q }
end

lemma lt_induced_map_iff [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] {x : α} {t : β} :
  t < induced_map α β x ↔ ∃ (q : ℚ) (h : t < q), (q : α) < x :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨q, hqt, hqi⟩ := exists_rat_btwn h,
    rw rat_cast_lt_induced_map_iff at hqi,
    refine ⟨q, hqt, hqi⟩ },
  { rintro ⟨q, hqt, hqx⟩,
    refine hqt.trans _,
    rwa rat_cast_lt_induced_map_iff }
end

@[simp] lemma induced_map_self [conditionally_complete_linear_ordered_field α] (x : α) :
  induced_map α α x = x :=
eq_of_forall_rat_lt_iff_lt $ λ q, rat_cast_lt_induced_map_iff

@[simp] lemma induced_map_induced_map (α β γ : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β]
  [conditionally_complete_linear_ordered_field γ] (x : α) :
  induced_map β γ (induced_map α β x) = induced_map α γ x :=
eq_of_forall_rat_lt_iff_lt $ λ q, by rw [rat_cast_lt_induced_map_iff,
  rat_cast_lt_induced_map_iff, iff.comm, rat_cast_lt_induced_map_iff]

@[simp] lemma induced_map_inv_self (α β : Type*) [conditionally_complete_linear_ordered_field α]
  [conditionally_complete_linear_ordered_field β] (x : α) :
  induced_map β α (induced_map α β x) = x :=
by rw [induced_map_induced_map, induced_map_self]

lemma induced_map_add (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] (x y : α) :
  induced_map α β (x + y) = induced_map α β x + induced_map α β y :=
begin
  rw [induced_map, cut_image_add],
  exact cSup_add _ _ (cut_image_nonempty β x) (cut_image_nonempty β y)
   (cut_image_bdd_above β x) (cut_image_bdd_above β y),
end

/-- `induced_map` as an additive homomorphism. -/
def induced_add_hom (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] : α →+ β :=
{ to_fun := induced_map α β,
  map_zero' := induced_map_zero α β,
  map_add' := induced_map_add α β }

/-- Preparatory lemma for `induced_ring_hom` -/
lemma le_induced_mul_self_of_mem_cut_image (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] (x : α) (hx : 0 < x) (a : β)
  (ha : a ∈ cut_image β (x * x)) : a ≤ induced_add_hom α β x * induced_add_hom α β x :=
begin
  rw mem_cut_image_iff at ha,
  rcases ha with ⟨q, rfl, ha⟩,
  obtain ⟨q2, hqpos, hq21, hq22⟩ := exists_rat_sq_btwn ha (mul_self_pos.2 hx.ne'),
  rw pow_two at hq22,
  have : (q2 : α) < x := lt_of_mul_self_lt_mul_self hx.le hq22,
  rw ← @coe_mem_cut_image_iff α β at this,
  have : (q2 : β) ≤ induced_map α β x := le_cSup _ _ (cut_image_bdd_above β x) this,
  transitivity (q2 : β)^2,
  apply le_of_lt,
  assumption_mod_cast,
  rw pow_two,
  have q2pos : (0 : β) ≤ q2 := by exact_mod_cast hqpos,
  exact mul_le_mul this this q2pos (le_trans _ _ _ q2pos this),
end

/-- Preparatory lemma for `induced_ring_hom`. -/
lemma exists_mem_cut_image_mul_self_of_lt_induced_map_mul_self (α β : Type*)
  [linear_ordered_field α] [archimedean α] [conditionally_complete_linear_ordered_field β] (x : α)
  (hx : 0 < x) (y : β) (hyx : y < induced_add_hom α β x * induced_add_hom α β x) :
  ∃ a ∈ cut_image β (x * x), y < a :=
begin
  obtain hy | hy := lt_or_le y 0,
  { refine ⟨0, _, hy⟩,
    rw [←rat.cast_zero, coe_mem_cut_image_iff, rat.cast_zero],
    exact mul_self_pos.2 hx.ne' },
  obtain ⟨q2, hqpos, hq21, hq22⟩ := exists_rat_sq_btwn hyx (hy.trans_lt hyx),
  rw pow_two at hq22,
  have : (q2 : β) < _ := lt_of_mul_self_lt_mul_self _ hq22,
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
  rw ←induced_map_zero α,
  exact induced_map_mono _ _ hx.le,
end

/-- `induced_map` as an `order_ring_hom`. -/
@[simps] def induced_order_ring_hom (α β : Type*) [linear_ordered_field α] [archimedean α]
  [conditionally_complete_linear_ordered_field β] : α →+*o β :=
{ monotone' := induced_map_mono _ _,
  ..(induced_add_hom α β).mk_ring_hom_of_mul_self_of_two_ne_zero  -- reduce to the case of x = y
    begin
      intro x,
      -- reduce to the case of 0 < x
      suffices : ∀ (x : α), 0 < x →
        induced_add_hom α β (x * x) = induced_add_hom α β x * induced_add_hom α β x,
      { rcases lt_trichotomy x 0 with h|rfl|h,
        { convert this (-x) (neg_pos.2 h) using 1,
          { rw [neg_mul, mul_neg, neg_neg] },
          { simp_rw [add_monoid_hom.map_neg, neg_mul, mul_neg, neg_neg] } },
        { simp only [mul_zero, add_monoid_hom.map_zero] },
        { exact this x h } },
      clear x,
      intros x hx,
      -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
      -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
      refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_image_nonempty β _) _ _,
      exact le_induced_mul_self_of_mem_cut_image α β x hx,
      exact exists_mem_cut_image_mul_self_of_lt_induced_map_mul_self α β x hx,
    end two_ne_zero (by exact_mod_cast induced_map_rat α β 1) }

/-- The equivalence of ordered rings between two conditionally complete linearly ordered fields. -/
def cut_order_ring_iso (α β : Type*)
  [conditionally_complete_linear_ordered_field α] [conditionally_complete_linear_ordered_field β] :
  α ≃+*o β :=
{ inv_fun := induced_map β α,
  left_inv := induced_map_inv_self α β,
  right_inv := induced_map_inv_self β α,
  map_le_map_iff' := λ x y, begin
    refine ⟨λ h, _, λ h, induced_map_mono _ _ h⟩,
    simpa [induced_order_ring_hom, add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero,
      induced_add_hom] using induced_map_mono β α h,
  end,
  ..induced_order_ring_hom α β }

lemma cut_ordered_equiv_coe_fun (α β : Type*)
  [conditionally_complete_linear_ordered_field α] [conditionally_complete_linear_ordered_field β] :
  (cut_order_ring_iso α β : α → β) = induced_map α β := rfl

lemma cut_order_ring_iso_symm (α β : Type*)
  [conditionally_complete_linear_ordered_field α] [conditionally_complete_linear_ordered_field β] :
  (cut_order_ring_iso α β).symm = cut_order_ring_iso β α := rfl

@[simp] lemma cut_order_ring_iso_self (α : Type*) [conditionally_complete_linear_ordered_field α] :
  cut_order_ring_iso α α = order_ring_iso.refl α :=
order_ring_iso.ext induced_map_self

open order_ring_iso

/-- There is at most ring homomorphism from a linear ordered field to an archimedean linear ordered
field. -/
instance [linear_ordered_field α] [linear_ordered_field β] [archimedean β] :
  subsingleton (α →+*o β) :=
⟨λ f g, begin
  ext x,
  by_contra' h,
  wlog h : f x < g x using [f g, g f],
  { exact ne.lt_or_lt h },
  obtain ⟨q, hf, hg⟩ := exists_rat_btwn h,
  rw ←map_rat_cast f at hf,
  rw ←map_rat_cast g at hg,
  exact (lt_asymm ((order_hom_class.mono g).reflect_lt hg) $
    (order_hom_class.mono f).reflect_lt hf).elim,
end⟩

instance [linear_ordered_field α] [linear_ordered_field β] [archimedean β] :
  subsingleton (α ≃+*o β) :=
order_ring_iso.to_order_ring_hom_injective.subsingleton

/-- There is a unique ordered ring homomorphism from an archimedean linear ordered field to a
conditionally complete linear ordered field. -/
instance [linear_ordered_field α] [archimedean α] [conditionally_complete_linear_ordered_field β] :
  unique (α →+*o β) :=
unique_of_subsingleton $ induced_order_ring_hom α β

instance [conditionally_complete_linear_ordered_field α]
  [conditionally_complete_linear_ordered_field β] : unique (α ≃+*o β) :=
unique_of_subsingleton $ cut_order_ring_iso α β

end conditionally_complete_linear_ordered_field
