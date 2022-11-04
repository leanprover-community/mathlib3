/-
Copyright (c) 2022 Alex J. Best. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alex J. Best, Yaël Dillies
-/
import algebra.order.hom.ring
import algebra.order.pointwise
import analysis.special_functions.pow

/-!
# Conditionally complete linear ordered fields

This file shows that the reals are unique, or, more formally, given a type satisfying the common
axioms of the reals (field, conditionally complete, linearly ordered) that there is an isomorphism
preserving these properties to the reals. This is `rat.induced_order_ring_iso`. Moreover this
isomorphism is unique.

We introduce definitions of conditionally complete linear ordered fields, and show all such are
archimedean. We also construct the natural map from a `linear_ordered_field` to such a field.

## Main definitions

* `conditionally_complete_linear_ordered_field`: A field satisfying the standard axiomatization of
  the real numbers, being a Dedekind complete and linear ordered field.
* `linear_ordered_field.induced_map`: A (unique) map from any archimedean linear ordered field to a
  conditionally complete linear ordered field. Various bundlings are available.

## Main results

* `unique.order_ring_hom` : Uniqueness of `order_ring_hom`s from an archimedean linear ordered field
  to a conditionally complete linear ordered field.
* `unique.order_ring_iso` : Uniqueness of `order_ring_iso`s between two
  conditionally complete linearly ordered fields.

## References

* https://mathoverflow.net/questions/362991/
  who-first-characterized-the-real-numbers-as-the-unique-complete-ordered-field

## Tags

reals, conditionally complete, ordered field, uniqueness
-/

variables {F α β γ : Type*}

noncomputable theory

open function rat real set
open_locale classical pointwise

set_option old_structure_cmd true

/-- A field which is both linearly ordered and conditionally complete with respect to the order.
This axiomatizes the reals. -/
@[protect_proj, ancestor linear_ordered_field conditionally_complete_linear_order]
class conditionally_complete_linear_ordered_field (α : Type*)
  extends linear_ordered_field α renaming max → sup min → inf, conditionally_complete_linear_order α

/-- Any conditionally complete linearly ordered field is archimedean. -/
@[priority 100] -- see Note [lower instance priority]
instance conditionally_complete_linear_ordered_field.to_archimedean
  [conditionally_complete_linear_ordered_field α] : archimedean α :=
archimedean_iff_nat_lt.2 begin
  by_contra' h,
  obtain ⟨x, h⟩ := h,
  have := cSup_le (range_nonempty (coe : ℕ → α)) (forall_range_iff.2 $ λ n, le_sub_iff_add_le.2 $
    le_cSup ⟨x, forall_range_iff.2 h⟩ ⟨n + 1, nat.cast_succ n⟩),
  linarith,
end

/-- The reals are a conditionally complete linearly ordered field. -/
instance : conditionally_complete_linear_ordered_field ℝ :=
{ ..real.linear_ordered_field, ..real.conditionally_complete_linear_order }

namespace linear_ordered_field

/-!
### Rational cut map

The idea is that a conditionally complete linear ordered field is fully characterized by its copy of
the rationals. Hence we define `rat.cut_map β : α → set β` which sends `a : α` to the "rationals in
`β`" that are less than `a`.
-/

section cut_map
variables [linear_ordered_field α]

section division_ring
variables (β) [division_ring β] {a a₁ a₂ : α} {b : β} {q : ℚ}

/-- The lower cut of rationals inside a linear ordered field that are less than a given element of
another linear ordered field. -/
def cut_map (a : α) : set β := (coe : ℚ → β) '' {t | ↑t < a}

lemma cut_map_mono (h : a₁ ≤ a₂) : cut_map β a₁ ⊆ cut_map β a₂ := image_subset _ $ λ _, h.trans_lt'

variables {β}

@[simp] lemma mem_cut_map_iff : b ∈ cut_map β a ↔ ∃ q : ℚ, (q : α) < a ∧ (q : β) = b := iff.rfl

@[simp] lemma coe_mem_cut_map_iff [char_zero β] : (q : β) ∈ cut_map β a ↔ (q : α) < a :=
rat.cast_injective.mem_set_image

lemma cut_map_self (a : α) : cut_map α a = Iio a ∩ range (coe : ℚ → α) :=
begin
  ext,
  split,
  { rintro ⟨q, h, rfl⟩,
    exact ⟨h, q, rfl⟩ },
  { rintro ⟨h, q, rfl⟩,
    exact ⟨q, h, rfl⟩ }
end

end division_ring

variables (β) [linear_ordered_field β] {a a₁ a₂ : α} {b : β} {q : ℚ}

lemma cut_map_coe (q : ℚ) : cut_map β (q : α) = coe '' {r : ℚ | (r : β) < q} :=
by simp_rw [cut_map, rat.cast_lt]

variables [archimedean α]

lemma cut_map_nonempty (a : α) : (cut_map β a).nonempty :=  nonempty.image _ $ exists_rat_lt a

lemma cut_map_bdd_above (a : α) : bdd_above (cut_map β a) :=
begin
  obtain ⟨q, hq⟩ := exists_rat_gt a,
  exact ⟨q, ball_image_iff.2 $ λ r hr, by exact_mod_cast (hq.trans' hr).le⟩,
end

lemma cut_map_add (a b : α) : cut_map β (a + b) = cut_map β a + cut_map β b :=
begin
  refine (image_subset_iff.2 $ λ q hq, _).antisymm _,
  { rw [mem_set_of_eq, ←sub_lt_iff_lt_add] at hq,
    obtain ⟨q₁, hq₁q, hq₁ab⟩ := exists_rat_btwn hq,
    refine ⟨q₁, q - q₁, _, _, add_sub_cancel'_right _ _⟩; try {norm_cast}; rwa coe_mem_cut_map_iff,
    exact_mod_cast sub_lt_comm.mp hq₁q },
  { rintro _ ⟨_, _, ⟨qa, ha, rfl⟩, ⟨qb, hb, rfl⟩, rfl⟩,
    refine ⟨qa + qb, _, by norm_cast⟩,
    rw [mem_set_of_eq, cast_add],
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
    exact ⟨q', ⟨_, hq, rfl⟩, hwq⟩ }
end

@[simp] lemma induced_map_zero : induced_map α β 0 = 0 := by exact_mod_cast induced_map_rat α β 0
@[simp] lemma induced_map_one : induced_map α β 1 = 1 := by exact_mod_cast induced_map_rat α β 1

variables {α β} {a : α} {b : β} {q : ℚ}

lemma induced_map_nonneg (ha : 0 ≤ a) : 0 ≤ induced_map α β a :=
(induced_map_zero α _).ge.trans $ induced_map_mono _ _ ha

lemma coe_lt_induced_map_iff : (q : β) < induced_map α β a ↔ (q : α) < a :=
begin
  refine ⟨λ h, _, λ hq, _⟩,
  { rw ←induced_map_rat α at h,
    exact (induced_map_mono α β).reflect_lt h },
  { obtain ⟨q', hq, hqa⟩ := exists_rat_btwn hq,
    apply lt_cSup_of_lt (cut_map_bdd_above β a) (coe_mem_cut_map_iff.mpr hqa),
    exact_mod_cast hq }
end

lemma lt_induced_map_iff : b < induced_map α β a ↔ ∃ q : ℚ, b < q ∧ (q : α) < a :=
⟨λ h, (exists_rat_btwn h).imp $ λ q, and.imp_right coe_lt_induced_map_iff.1,
  λ ⟨q, hbq, hqa⟩, hbq.trans $ by rwa coe_lt_induced_map_iff⟩

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
  exact cSup_add (cut_map_nonempty β x) (cut_map_bdd_above β x) (cut_map_nonempty β y)
    (cut_map_bdd_above β y),
end

variables {α β}

/-- Preparatory lemma for `induced_ring_hom`. -/
lemma le_induced_map_mul_self_of_mem_cut_map (ha : 0 < a) (b : β) (hb : b ∈ cut_map β (a * a)) :
  b ≤ induced_map α β a * induced_map α β a :=
begin
  obtain ⟨q, hb, rfl⟩ := hb,
  obtain ⟨q', hq', hqq', hqa⟩ := exists_rat_pow_btwn two_ne_zero hb (mul_self_pos.2 ha.ne'),
  transitivity (q' : β)^2,
  exact_mod_cast hqq'.le,
  rw pow_two at ⊢ hqa,
  exact mul_self_le_mul_self (by exact_mod_cast hq'.le) (le_cSup (cut_map_bdd_above β a) $
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
  obtain ⟨q, hq, hbq, hqa⟩ := exists_rat_pow_btwn two_ne_zero hba (hb.trans_lt hba),
  rw ←cast_pow at hbq,
  refine ⟨(q^2 : ℚ), coe_mem_cut_map_iff.2 _, hbq⟩,
  rw pow_two at ⊢ hqa,
  push_cast,
  obtain ⟨q', hq', hqa'⟩ := lt_induced_map_iff.1 (lt_of_mul_self_lt_mul_self _ hqa),
  exact mul_self_lt_mul_self (by exact_mod_cast hq.le) (hqa'.trans' $ by assumption_mod_cast),
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
fields. -/
instance : unique (β ≃+*o γ) := unique_of_subsingleton $ induced_order_ring_iso β γ

end induced_map
end linear_ordered_field

section real

variables {R S : Type*} [ordered_ring R] [linear_ordered_ring S]

lemma ring_hom_monotone (hR : ∀ r : R, 0 ≤ r → ∃ s : R, s^2 = r) (f : R →+* S) : monotone f :=
(monotone_iff_map_nonneg f).2 $ λ r h, by { obtain ⟨s, rfl⟩ := hR r h, rw map_pow, apply sq_nonneg }

/-- There exists no nontrivial ring homomorphism `ℝ →+* ℝ`. -/
instance real.ring_hom.unique : unique (ℝ →+* ℝ) :=
{ default := ring_hom.id ℝ,
  uniq := λ f, congr_arg order_ring_hom.to_ring_hom
    (subsingleton.elim ⟨f, ring_hom_monotone (λ r hr, ⟨real.sqrt r, sq_sqrt hr⟩) f⟩ default), }

end real
