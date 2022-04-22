/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import algebra.order.hom.ring
import analysis.special_functions.pow

/-!
# Conditionally complete linear ordered fields

This file shows that the reals are unique, or, more formally, given a type satisfying the common
axioms of the reals (field, conditionally complete, linearly ordered) that there is an equivalence
preserving these properties to the reals. This is `induced_order_ring_iso`. Moreover this
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
* `order_ring_iso_eq_induced_order_ring_iso` : Uniqueness of `order_ring_iso`s between two
  conditionally complete linearly ordered fields.

## References

* https://mathoverflow.net/questions/362991/
  who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags

reals, conditionally complete, ordered field, uniqueness
-/

section move
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

section
variables [linear_ordered_field α] [archimedean α] {x y : α}

lemma le_of_forall_rat_lt_imp_le (h : ∀ q : ℚ, (q : α) < x → (q : α) ≤ y) : x ≤ y :=
le_of_not_lt $ λ hyx, let ⟨q, hy, hx⟩ := exists_rat_btwn hyx in hy.not_le $ h _ hx

lemma le_of_forall_lt_rat_imp_le (h : ∀ q : ℚ, y < q → x ≤ q) : x ≤ y :=
le_of_not_lt $ λ hyx, let ⟨q, hy, hx⟩ := exists_rat_btwn hyx in hx.not_le $ h _ hy

lemma eq_of_forall_rat_lt_iff_lt (h : ∀ q : ℚ, (q : α) < x ↔ (q : α) < y) : x = y :=
(le_of_forall_rat_lt_imp_le $ λ q hq, ((h q).1 hq).le).antisymm $ le_of_forall_rat_lt_imp_le $
  λ q hq, ((h q).2 hq).le

lemma eq_of_forall_lt_rat_iff_lt (h : ∀ q : ℚ, x < q ↔ y < q) : x = y :=
(le_of_forall_lt_rat_imp_le $ λ q hq, ((h q).2 hq).le).antisymm $ le_of_forall_lt_rat_imp_le $
  λ q hq, ((h q).1 hq).le

end

noncomputable theory
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

variables (α β) [division_ring α] [char_zero α] [division_ring β] [char_zero β]

/-- The natural equiv between the rationals and the rationals as a set inside any characteristic 0
  division ring. -/
def range_coe_equiv_rat : range (coe : ℚ → α) ≃ ℚ :=
(equiv.of_injective coe rat.cast_injective).symm

@[simp] lemma range_coe_equiv_rat_symm_apply (q : ℚ) :
  (range_coe_equiv_rat α).symm q = ⟨q, mem_range_self _⟩ := rfl

@[simp] lemma range_coe_equiv_rat_coe (q : ℚ) : range_coe_equiv_rat α ⟨q, mem_range_self _⟩ = q :=
(equiv.apply_eq_iff_eq_symm_apply _).2 rfl

/-- The natural equiv between the rationals as a set inside any pair of characteristic 0
  division rings -/
def range_rat_equiv : range (coe : ℚ → α) ≃ range (coe : ℚ → β) :=
(range_coe_equiv_rat α).trans (range_coe_equiv_rat β).symm

@[simp] lemma range_rat_equiv_apply_coe (q : ℚ):
  range_rat_equiv α β ⟨q, mem_range_self q⟩ = ⟨q, mem_range_self q⟩ :=
by simp only [range_rat_equiv, equiv.coe_trans, comp_app, range_coe_equiv_rat_coe,
  range_coe_equiv_rat_symm_apply]

end move

variables {F α β γ : Type*}

noncomputable theory

open function real set
open_locale classical pointwise

set_option old_structure_cmd true

/-- A field which is both linearly ordered and conditionally complete with respect to the order,
this is an axiomatization of the reals. -/
@[protect_proj, ancestor linear_ordered_field conditionally_complete_linear_order]
class conditionally_complete_linear_ordered_field (α : Type*)
  extends linear_ordered_field α renaming max → sup min → inf, conditionally_complete_linear_order α

/-- Any conditionally complete linearly ordered field is archimedean. -/
@[priority 100] -- see Note [lower instance priority]
instance conditionally_complete_linear_ordered_field.to_archimedean
  [conditionally_complete_linear_ordered_field α] : archimedean α :=
archimedean_iff_nat_lt.mpr
  begin
    by_contra' h,
    have : ∀ b, b ∈ set.range (coe : ℕ → α) → b ≤ Sup (set.range (coe : ℕ → α)) - 1,
    { obtain ⟨x, h⟩ := h,
      have : bdd_above (set.range (coe : ℕ → α)),
      { use x,
        rintro _ ⟨n, rfl⟩,
        exact h n },
      rintro b ⟨n, rfl⟩,
      rw le_sub_iff_add_le,
      exact le_cSup this ⟨n + 1, nat.cast_succ n⟩ },
    replace := cSup_le (set.range_nonempty (coe : ℕ → α)) this,
    linarith,
  end

/-- The reals are a conditionally complete linearly ordered field. -/
instance : conditionally_complete_linear_ordered_field ℝ :=
{ ..real.linear_ordered_field, ..real.conditionally_complete_linear_order }

namespace rat

/-!
### Rational cut map

The idea is that a conditionally complete linear ordered field is fully characterized by its copy of
the rationals. Hence we define `rat.cut_map β : α → set β` which sends `a : α` to the "rationals in
`β`" that are less than `a`.
-/

section cut_map
variables (β) [linear_ordered_field α] [linear_ordered_field β] {a : α} {b : β} {q : ℚ}

/-- The lower cut of rationals inside a linear ordered field that are less than a given element of
another linear ordered field. -/
def cut_map (a : α) : set β := subtype.val ∘ range_rat_equiv α β '' {t | ↑t < a}

lemma cut_map_mono {x y : α} (h : x ≤ y) : cut_map β x ⊆ cut_map β y :=
image_subset _ $ λ t,  h.trans_lt'

variables {β}

@[simp] lemma mem_cut_map_iff : b ∈ cut_map β a ↔ ∃ q : ℚ, (q : β) = b ∧ (q : α) < a :=
begin
  rw cut_map,
  split,
  { rintro ⟨⟨_, q, rfl⟩, hq, rfl⟩,
    exact ⟨q, congr_arg coe (range_coe_equiv_rat_coe _ _).symm, hq⟩ },
  { rintro ⟨q, rfl, hq⟩,
    exact ⟨⟨q, mem_range_self _⟩, hq, congr_arg coe $ range_coe_equiv_rat_coe _ _⟩ }
end

@[simp] lemma coe_mem_cut_map_iff : (q : β) ∈ cut_map β a ↔ (q : α) < a :=
mem_cut_map_iff.trans ⟨λ ⟨r, h, hr⟩, by rwa ←rat.cast_injective h, λ h, ⟨q, rfl, h⟩⟩

lemma cut_map_coe (q : ℚ) :
  cut_map β (q : α) = subtype.val '' {t : set.range (coe : ℚ → β) | (t : β) < q} :=
begin
  ext x,
  simp only [mem_cut_map_iff, mem_range, rat.cast_lt, exists_prop, mem_image, subtype.exists,
    exists_and_distrib_right, exists_eq_right],
  split,
  { rintro ⟨r, rfl, hr⟩,
    exact ⟨⟨r, rfl⟩, rat.cast_lt.mpr hr⟩ },
  { rintro ⟨⟨r, rfl⟩, hq⟩,
    exact ⟨r, rfl, rat.cast_lt.mp hq⟩ }
end

lemma cut_map_self (a : α) : cut_map α a = Iio a ∩ range (coe : ℚ → α) :=
begin
  ext y,
  simp only [mem_cut_map_iff, mem_inter_eq, mem_Iio, mem_range],
  split,
  { rintro ⟨q, rfl, h⟩,
    exact ⟨h, q, rfl⟩ },
  { rintro ⟨h, q, rfl⟩,
    exact ⟨q, rfl, h⟩ }
end

variables (β) [archimedean α]

lemma cut_map_nonempty (a : α) : (cut_map β a).nonempty :=
let ⟨q, hq⟩ := exists_rat_lt a in nonempty.image _ ⟨⟨q, mem_range_self _⟩, hq⟩

lemma cut_map_bdd_above (a : α) : bdd_above (cut_map β a) :=
begin
  obtain ⟨q, hq⟩ := exists_rat_gt a,
  use q,
  simp_rw [mem_upper_bounds, mem_cut_map_iff],
  rintro _ ⟨r, rfl, hr⟩,
  exact_mod_cast hr.le.trans hq.le,
end

lemma cut_map_strict_mono {a b : α} (hab : a < b) : cut_map β a ⊂ cut_map β b :=
begin
  refine (cut_map_mono β hab.le).ssubset_of_ne _,
  obtain ⟨q, ha, hb⟩ := exists_rat_btwn hab,
  exact ((coe_mem_cut_map_iff.mpr hb).ne_of_not_mem' $ λ h, lt_irrefl a $ ha.trans $
    coe_mem_cut_map_iff.1 h).symm,
end

lemma cut_map_add (a b : α) : cut_map β (a + b) = cut_map β a + cut_map β b :=
begin
  ext,
  refine ⟨λ h, _, _⟩,
  { obtain ⟨q, rfl, hq⟩ := mem_cut_map_iff.1 h,
    rw ← sub_lt_iff_lt_add at hq,
    obtain ⟨q₁, hq₁q, hq₁ab⟩ := exists_rat_btwn hq,
    refine ⟨q₁, q - q₁, _, _, add_sub_cancel'_right _ _⟩; try {norm_cast};
    rwa coe_mem_cut_map_iff,
    push_cast,
    exact sub_lt.mp hq₁q },
  { simp_rw [mem_add, mem_cut_map_iff],
    rintro ⟨_, _, ⟨qa, rfl, ha⟩, ⟨qb, rfl, hb⟩, rfl⟩,
    refine ⟨qa + qb, by norm_cast, _⟩,
    push_cast,
    exact add_lt_add ha hb }
end

end cut_map

/-!
### Induced map

`rat.cut_map` spits out a `set β`. To get something in `β`, we now take the supremum.
-/

section induced_map
variables (α β γ) [linear_ordered_field α] [conditionally_complete_linear_ordered_field β]
  [conditionally_complete_linear_ordered_field γ]

/-- The induced order preserving function from a linear ordered field to a conditionally complete
linear ordered field, defined by taking the Sup in the codomain of all the rationals less than the
input. -/
def induced_map (x : α) : β := Sup $ cut_map β x

variables [archimedean α]

lemma induced_map_mono : monotone (induced_map α β) :=
λ a b h, cSup_le_cSup (cut_map_bdd_above β _) (cut_map_nonempty β _) (cut_map_mono β h)

lemma induced_map_rat (q : ℚ) : induced_map α β (q : α) = q :=
begin
  refine cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_map_nonempty β q) (λ x h, _) (λ w h, _),
  { rw cut_map_coe at h,
    obtain ⟨r, h, rfl⟩ := h,
    exact le_of_lt h },
  { obtain ⟨q', hwq, hq⟩ := exists_rat_btwn h,
    rw cut_map_coe,
    exact ⟨q', ⟨⟨_, mem_range_self _⟩, hq, rfl⟩, hwq⟩ }
end

@[simp] lemma induced_map_zero : induced_map α β 0 = 0 := by exact_mod_cast induced_map_rat α β 0
@[simp] lemma induced_map_one : induced_map α β 1 = 1 := by exact_mod_cast induced_map_rat α β 1

variables {α β} {a : α} {b : β} {q : ℚ}

lemma induced_map_nonneg (ha : 0 ≤ a) : 0 ≤ induced_map α β a :=
(induced_map_zero α _).ge.trans $ induced_map_mono _ _ ha

lemma coe_lt_induced_map_iff : (q : β) < induced_map α β a ↔ (q : α) < a :=
begin
  refine ⟨λ h, _, _⟩,
  { rw ←induced_map_rat α at h,
    exact (induced_map_mono α β).reflect_lt h },
  { rintro hq,
    obtain ⟨q', hq, hqa⟩ := exists_rat_btwn hq,
    apply lt_cSup_of_lt (cut_map_bdd_above β a) (coe_mem_cut_map_iff.mpr hqa),
    exact_mod_cast hq }
end

lemma lt_induced_map_iff : b < induced_map α β a ↔ ∃ (q : ℚ) (h : b < q), (q : α) < a :=
begin
  refine ⟨λ h, _, _⟩,
  { obtain ⟨q, hqt, hqi⟩ := exists_rat_btwn h,
    rw coe_lt_induced_map_iff at hqi,
    refine ⟨q, hqt, hqi⟩ },
  { rintro ⟨q, hqt, hqx⟩,
    refine hqt.trans _,
    rwa coe_lt_induced_map_iff }
end

@[simp] lemma induced_map_self (b : β) : induced_map β β b = b :=
eq_of_forall_rat_lt_iff_lt $ λ q, coe_lt_induced_map_iff

variables (α β)

@[simp] lemma induced_map_induced_map (a : α) :
  induced_map β γ (induced_map α β a) = induced_map α γ a :=
eq_of_forall_rat_lt_iff_lt $ λ q,
  by rw [coe_lt_induced_map_iff, coe_lt_induced_map_iff, iff.comm, coe_lt_induced_map_iff]

@[simp] lemma induced_map_inv_self (b : β) : induced_map γ β (induced_map β γ b) = b :=
by rw [induced_map_induced_map, induced_map_self]

lemma induced_map_add (x y : α) : induced_map α β (x + y) = induced_map α β x + induced_map α β y :=
begin
  rw [induced_map, cut_map_add],
  exact cSup_add _ _ (cut_map_nonempty β x) (cut_map_nonempty β y)
   (cut_map_bdd_above β x) (cut_map_bdd_above β y),
end

variables {α β}

/-- Preparatory lemma for `induced_ring_hom`. -/
lemma le_induced_map_mul_self_of_mem_cut_map (ha : 0 < a) (b : β) (hb : b ∈ cut_map β (a * a)) :
  b ≤ induced_map α β a * induced_map α β a :=
begin
  rw mem_cut_map_iff at hb,
  obtain ⟨q, rfl, hb⟩ := hb,
  obtain ⟨q', hq', hqq', hqa⟩ := exists_rat_sq_btwn hb (mul_self_pos.2 ha.ne'),
  transitivity (q' : β)^2,
  exact_mod_cast hqq'.le,
  rw pow_two at ⊢ hqa,
  exact mul_self_le_mul_self (by exact_mod_cast hq') (le_cSup (cut_map_bdd_above β a) $
    coe_mem_cut_map_iff.2 $ lt_of_mul_self_lt_mul_self ha.le hqa),
end

/-- Preparatory lemma for `induced_ring_hom`. -/
lemma exists_mem_cut_map_mul_self_of_lt_induced_map_mul_self (ha : 0 < a) (b : β)
  (hba : b < induced_map α β a * induced_map α β a) :
  ∃ c ∈ cut_map β (a * a), b < c :=
begin
  obtain hb | hb := lt_or_le b 0,
  { refine ⟨0, _, hb⟩,
    rw [←rat.cast_zero, coe_mem_cut_map_iff, rat.cast_zero],
    exact mul_self_pos.2 ha.ne' },
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_sq_btwn hba (hb.trans_lt hba),
  rw ←cast_pow at hbq,
  refine ⟨(q^2 : ℚ), coe_mem_cut_map_iff.2 _, hbq⟩,
  rw pow_two at ⊢ hqa,
  push_cast,
  obtain ⟨q', hq', hqa'⟩ := lt_induced_map_iff.1 (lt_of_mul_self_lt_mul_self _ hqa),
  exact mul_self_lt_mul_self (by assumption_mod_cast) (hqa'.trans' $ by assumption_mod_cast),
  exact induced_map_nonneg ha.le,
end

variables (α β)

/-- `induced_map` as an additive homomorphism. -/
def induced_add_hom : α →+ β := ⟨induced_map α β, induced_map_zero α β, induced_map_add α β⟩

/-- `induced_map` as an `order_ring_hom`. -/
@[simps] def induced_order_ring_hom : α →+*o β :=
{ monotone' := induced_map_mono _ _,
  ..(induced_add_hom α β).mk_ring_hom_of_mul_self_of_two_ne_zero  -- reduce to the case of x = y
    begin
      -- reduce to the case of 0 < x
      suffices : ∀ x, 0 < x →
        induced_add_hom α β (x * x) = induced_add_hom α β x * induced_add_hom α β x,
      { rintro x,
        obtain h | rfl | h := lt_trichotomy x 0,
        { convert this (-x) (neg_pos.2 h) using 1,
          { rw [neg_mul, mul_neg, neg_neg] },
          { simp_rw [add_monoid_hom.map_neg, neg_mul, mul_neg, neg_neg] } },
        { simp only [mul_zero, add_monoid_hom.map_zero] },
        { exact this x h } },
      -- prove that the (Sup of rationals less than x) ^ 2 is the Sup of the set of rationals less
      -- than (x ^ 2) by showing it is an upper bound and any smaller number is not an upper bound
      refine λ x hx, cSup_eq_of_forall_le_of_forall_lt_exists_gt (cut_map_nonempty β _) _ _,
      exact le_induced_map_mul_self_of_mem_cut_map hx,
      exact exists_mem_cut_map_mul_self_of_lt_induced_map_mul_self hx,
    end two_ne_zero (induced_map_one _ _) }

/-- The isomorphism of ordered rings between two conditionally complete linearly ordered fields. -/
def induced_order_ring_iso : β ≃+*o γ :=
{ inv_fun := induced_map γ β,
  left_inv := induced_map_inv_self _ _,
  right_inv := induced_map_inv_self _ _,
  map_le_map_iff' := λ x y, begin
    refine ⟨λ h, _, λ h, induced_map_mono _ _ h⟩,
    simpa [induced_order_ring_hom, add_monoid_hom.mk_ring_hom_of_mul_self_of_two_ne_zero,
      induced_add_hom] using induced_map_mono γ β h,
  end,
  ..induced_order_ring_hom β γ }

@[simp] lemma coe_induced_order_ring_iso : ⇑(induced_order_ring_iso β γ) = induced_map β γ := rfl

@[simp] lemma induced_order_ring_iso_symm :
  (induced_order_ring_iso β γ).symm = induced_order_ring_iso γ β := rfl

@[simp] lemma induced_order_ring_iso_self : induced_order_ring_iso β β = order_ring_iso.refl β :=
order_ring_iso.ext induced_map_self

open order_ring_iso

/-- There is a unique ordered ring homomorphism from an archimedean linear ordered field to a
conditionally complete linear ordered field. -/
instance : unique (α →+*o β) := unique_of_subsingleton $ induced_order_ring_hom α β

/-- There is a unique ordered ring isomorphism between two conditionally complete linear ordered
field. -/
instance : unique (β ≃+*o γ) := unique_of_subsingleton $ induced_order_ring_iso β γ

end induced_map
end rat
