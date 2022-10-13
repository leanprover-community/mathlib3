/-
Copyright (c) 2020 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Yaël Dillies
-/
import data.finset.pointwise.basic
import data.set.pointwise.smul

/-!
# Scalar multiplication of finsets

The main declaration is
* `a • s` (`finset.has_smul_finset`): Scaling, finset of all `a • x` where `x ∈ s`.

For `α` a semigroup/monoid, `finset α` is a semigroup/monoid.
As an unfortunate side effect, this means that `n • s`, where `n : ℕ`, is ambiguous between
pointwise scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while
the latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].
-/


/-! ### Scalar addition/multiplication of finsets -/

namespace finset

variables {α β γ : Type*}
open_locale pointwise

section has_smul
variables [decidable_eq β] [has_smul α β] {s s₁ s₂ : finset α} {t t₁ t₂ u : finset β} {a : α}
  {b : β}

/-- The pointwise product of two finsets `s` and `t`: `s • t = {x • y | x ∈ s, y ∈ t}`. -/
@[to_additive "The pointwise sum of two finsets `s` and
`t`: `s +ᵥ t = {x +ᵥ y | x ∈ s, y ∈ t}`."]
protected def has_smul : has_smul (finset α) (finset β) := ⟨image₂ (•)⟩

localized "attribute [instance] finset.has_smul finset.has_vadd" in pointwise

@[to_additive] lemma smul_def : s • t = (s ×ˢ t).image (λ p : α × β, p.1 • p.2) := rfl

@[to_additive]
lemma image_smul_product : (s ×ˢ t).image (λ x : α × β, x.fst • x.snd)  = s • t := rfl

@[to_additive] lemma mem_smul {x : β} : x ∈ s • t ↔ ∃ y z, y ∈ s ∧ z ∈ t ∧ y • z = x := mem_image₂

@[simp, norm_cast, to_additive]
lemma coe_smul (s : finset α) (t : finset β) : (↑(s • t) : set β) = (s : set α) • t :=
coe_image₂ _ _ _

@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image₂_of_mem
@[to_additive] lemma smul_card_le : (s • t).card ≤ s.card • t.card := card_image₂_le _ _ _

@[simp, to_additive] lemma empty_smul (t : finset β) : (∅ : finset α) • t = ∅ := image₂_empty_left
@[simp, to_additive] lemma smul_empty (s : finset α) : s • (∅ : finset β) = ∅ := image₂_empty_right
@[simp, to_additive] lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image₂_eq_empty_iff
@[simp, to_additive] lemma smul_nonempty_iff : (s • t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image₂_nonempty_iff
@[to_additive] lemma nonempty.smul : s.nonempty → t.nonempty → (s • t).nonempty := nonempty.image₂
@[to_additive] lemma nonempty.of_smul_left : (s • t).nonempty → s.nonempty :=
nonempty.of_image₂_left
@[to_additive] lemma nonempty.of_smul_right : (s • t).nonempty → t.nonempty :=
nonempty.of_image₂_right
@[to_additive] lemma smul_singleton (b : β) : s • ({b} : finset β) = s.image (• b) :=
image₂_singleton_right
@[to_additive] lemma singleton_smul (a : α) : ({a} : finset α) • t = t.image ((•) a) :=
image₂_singleton_left
@[simp, to_additive] lemma singleton_smul_singleton (a : α) (b : β) :
  ({a} : finset α) • ({b} : finset β) = {a • b} :=
image₂_singleton

@[to_additive, mono] lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image₂_subset
@[to_additive] lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image₂_subset_left
@[to_additive] lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image₂_subset_right
@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a • b ∈ u := image₂_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive] lemma union_smul [decidable_eq α] : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t :=
image₂_union_left
@[to_additive] lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image₂_union_right
@[to_additive] lemma inter_smul_subset [decidable_eq α] : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t :=
image₂_inter_subset_left
@[to_additive] lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
image₂_inter_subset_right

/-- If a finset `u` is contained in the scalar product of two sets `s • t`, we can find two finsets
`s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' • t'`. -/
@[to_additive "If a finset `u` is contained in the scalar sum of two sets `s +ᵥ t`, we can find two
finsets `s'`, `t'` such that `s' ⊆ s`, `t' ⊆ t` and `u ⊆ s' +ᵥ t'`."]
lemma subset_smul {s : set α} {t : set β} :
  ↑u ⊆ s • t → ∃ (s' : finset α) (t' : finset β), ↑s' ⊆ s ∧ ↑t' ⊆ t ∧ u ⊆ s' • t' :=
subset_image₂

end has_smul


open_locale pointwise

/-! ### Translation/scaling of finsets -/

section has_smul
variables [decidable_eq β] [has_smul α β] {s s₁ s₂ t u : finset β} {a : α} {b : β}

/-- The scaling of a finset `s` by a scalar `a`: `a • s = {a • x | x ∈ s}`. -/
@[to_additive "The translation of a finset `s` by a vector `a`:
`a +ᵥ s = {a +ᵥ x | x ∈ s}`."]
protected def has_smul_finset : has_smul α (finset β) := ⟨λ a, image $ (•) a⟩

localized "attribute [instance] finset.has_smul_finset finset.has_vadd_finset" in pointwise

@[to_additive] lemma smul_finset_def : a • s = s.image ((•) a) := rfl
@[to_additive] lemma image_smul : s.image (λ x, a • x)  = a • s := rfl

@[to_additive]
lemma mem_smul_finset {x : β} : x ∈ a • s ↔ ∃ y, y ∈ s ∧ a • y = x :=
by simp only [finset.smul_finset_def, and.assoc, mem_image, exists_prop, prod.exists, mem_product]

@[simp, norm_cast, to_additive]
lemma coe_smul_finset (a : α) (s : finset β) : (↑(a • s) : set β) = a • s := coe_image

@[to_additive] lemma smul_finset_mem_smul_finset : b ∈ s → a • b ∈ a • s := mem_image_of_mem _
@[to_additive] lemma smul_finset_card_le : (a • s).card ≤ s.card := card_image_le

@[simp, to_additive] lemma smul_finset_empty (a : α) : a • (∅ : finset β) = ∅ := image_empty _
@[simp, to_additive] lemma smul_finset_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty
@[simp, to_additive] lemma smul_finset_nonempty : (a • s).nonempty ↔ s.nonempty :=
nonempty.image_iff _
@[to_additive] lemma nonempty.smul_finset (hs : s.nonempty) : (a • s).nonempty := hs.image _

@[to_additive, mono]
lemma smul_finset_subset_smul_finset : s ⊆ t → a • s ⊆ a • t := image_subset_image

attribute [mono] vadd_finset_subset_vadd_finset

@[simp, to_additive]
lemma smul_finset_singleton (b : β) : a • ({b} : finset β) = {a • b} := image_singleton _ _

@[to_additive] lemma smul_finset_union : a • (s₁ ∪ s₂) = a • s₁ ∪ a • s₂ := image_union _ _
@[to_additive] lemma smul_finset_inter_subset : a • (s₁ ∩ s₂) ⊆ a • s₁ ∩ (a • s₂) :=
image_inter_subset _ _ _

@[simp] lemma bUnion_smul_finset (s : finset α) (t : finset β) : s.bUnion (• t) = s • t :=
bUnion_image_left

end has_smul

open_locale pointwise

section instances
variables [decidable_eq γ]

open function

@[to_additive]
instance smul_comm_class_finset [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α β (finset γ) :=
⟨λ _ _, commute.finset_image $ smul_comm _ _⟩

@[to_additive]
instance smul_comm_class_finset' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α (finset β) (finset γ) :=
⟨λ a s t, coe_injective $ by simp only [coe_smul_finset, coe_smul, smul_comm]⟩

@[to_additive]
instance smul_comm_class_finset'' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (finset α) β (finset γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (finset α) (finset β) (finset γ) :=
⟨λ s t u, coe_injective $ by simp_rw [coe_smul, smul_comm]⟩

@[to_additive]
instance is_scalar_tower [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α β (finset γ) :=
⟨λ a b s, by simp only [←image_smul, image_image, smul_assoc]⟩

variables [decidable_eq β]

@[to_additive]
instance is_scalar_tower' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α (finset β) (finset γ) :=
⟨λ a s t, coe_injective $ by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

@[to_additive]
instance is_scalar_tower'' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower (finset α) (finset β) (finset γ) :=
⟨λ a s t, coe_injective $ by simp only [coe_smul_finset, coe_smul, smul_assoc]⟩

instance is_central_scalar [has_smul α β] [has_smul αᵐᵒᵖ β] [is_central_scalar α β] :
  is_central_scalar α (finset β) :=
⟨λ a s, coe_injective $ by simp only [coe_smul_finset, coe_smul, op_smul_eq_smul]⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of
`finset α` on `finset β`. -/
@[to_additive "An additive action of an additive monoid `α` on a type `β` gives an additive action
of `finset α` on `finset β`"]
protected def mul_action [decidable_eq α] [monoid α] [mul_action α β] :
  mul_action (finset α) (finset β) :=
{ mul_smul := λ _ _ _, image₂_assoc mul_smul,
  one_smul := λ s, image₂_singleton_left.trans $ by simp_rw [one_smul, image_id'] }

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `finset β`.
-/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action
on `finset β`."]
protected def mul_action_finset [monoid α] [mul_action α β] : mul_action α (finset β) :=
coe_injective.mul_action _ coe_smul_finset

localized "attribute [instance] finset.mul_action_finset finset.add_action_finset
  finset.mul_action finset.add_action" in pointwise

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `finset β`. -/
protected def distrib_mul_action_finset [monoid α] [add_monoid β] [distrib_mul_action α β] :
  distrib_mul_action α (finset β) :=
function.injective.distrib_mul_action ⟨coe, coe_zero, coe_add⟩ coe_injective coe_smul_finset

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mul_distrib_mul_action_finset [monoid α] [monoid β] [mul_distrib_mul_action α β] :
  mul_distrib_mul_action α (finset β) :=
function.injective.mul_distrib_mul_action ⟨coe, coe_one, coe_mul⟩ coe_injective coe_smul_finset

localized "attribute [instance] finset.distrib_mul_action_finset
  finset.mul_distrib_mul_action_finset" in pointwise

instance [decidable_eq α] [has_zero α] [has_mul α] [no_zero_divisors α] :
  no_zero_divisors (finset α) :=
coe_injective.no_zero_divisors _ coe_zero coe_mul

instance [has_zero α] [has_zero β] [has_smul α β] [no_zero_smul_divisors α β] :
  no_zero_smul_divisors (finset α) (finset β) :=
⟨λ s t h, begin
  by_contra' H,
  have hst : (s • t).nonempty := h.symm.subst zero_nonempty,
  simp_rw [←hst.of_smul_left.subset_zero_iff, ←hst.of_smul_right.subset_zero_iff, not_subset,
    mem_zero] at H,
  obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H,
  have := subset_of_eq h,
  exact (eq_zero_or_eq_zero_of_smul_eq_zero $ mem_zero.1 $ this $ smul_mem_smul hs ht).elim ha hb,
end⟩

instance no_zero_smul_divisors_finset [has_zero α] [has_zero β] [has_smul α β]
  [no_zero_smul_divisors α β] : no_zero_smul_divisors α (finset β) :=
coe_injective.no_zero_smul_divisors _ coe_zero coe_smul_finset

end instances

section left_cancel_semigroup
variables [left_cancel_semigroup α] [decidable_eq α] (s t : finset α) (a : α)

@[to_additive] lemma pairwise_disjoint_smul_iff {s : set α} {t : finset α} :
  s.pairwise_disjoint (• t) ↔ (s ×ˢ t : set (α × α)).inj_on (λ p, p.1 * p.2) :=
by simp_rw [←pairwise_disjoint_coe, coe_smul_finset, set.pairwise_disjoint_smul_iff]

@[simp, to_additive] lemma card_singleton_mul : ({a} * t).card = t.card :=
card_image₂_singleton_left _ $ mul_right_injective _

@[to_additive] lemma singleton_mul_inter : {a} * (s ∩ t) = ({a} * s) ∩ ({a} * t) :=
image₂_singleton_inter _ _ $ mul_right_injective _

@[to_additive] lemma card_le_card_mul_left {s : finset α} (hs : s.nonempty) :
  t.card ≤ (s * t).card :=
card_le_card_image₂_left _ hs mul_right_injective

end left_cancel_semigroup

section
variables [right_cancel_semigroup α] [decidable_eq α] (s t : finset α) (a : α)

@[simp, to_additive] lemma card_mul_singleton : (s * {a}).card = s.card :=
card_image₂_singleton_right _ $ mul_left_injective _

@[to_additive] lemma inter_mul_singleton : (s ∩ t) * {a} = (s * {a}) ∩ (t * {a}) :=
image₂_inter_singleton _ _ $ mul_left_injective _

@[to_additive] lemma card_le_card_mul_right {t : finset α} (ht : t.nonempty) :
  s.card ≤ (s * t).card :=
card_le_card_image₂_right _ ht mul_left_injective

end

open_locale pointwise

section group
variables [decidable_eq β] [group α] [mul_action α β] {s t : finset β} {a : α} {b : β}

@[simp, to_additive] lemma smul_mem_smul_finset_iff (a : α) : a • b ∈ a • s ↔ b ∈ s :=
(mul_action.injective _).mem_finset_image

@[to_additive] lemma inv_smul_mem_iff : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
by rw [←smul_mem_smul_finset_iff a, smul_inv_smul]

@[to_additive] lemma mem_inv_smul_finset_iff : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
by rw [←smul_mem_smul_finset_iff a, smul_inv_smul]

@[simp, to_additive] lemma smul_finset_subset_smul_finset_iff : a • s ⊆ a • t ↔ s ⊆ t :=
image_subset_image_iff $ mul_action.injective _

@[to_additive] lemma smul_finset_subset_iff : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
by { simp_rw ←coe_subset, push_cast, exact set.set_smul_subset_iff }

@[to_additive] lemma subset_smul_finset_iff : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
by { simp_rw ←coe_subset, push_cast, exact set.subset_set_smul_iff }

end group

section group_with_zero
variables [decidable_eq β] [group_with_zero α] [mul_action α β] {s t : finset β} {a : α} {b : β}

@[simp] lemma smul_mem_smul_finset_iff₀ (ha : a ≠ 0) : a • b ∈ a • s ↔ b ∈ s :=
smul_mem_smul_finset_iff (units.mk0 a ha)

lemma inv_smul_mem_iff₀ (ha : a ≠ 0) : a⁻¹ • b ∈ s ↔ b ∈ a • s :=
show _ ↔ _ ∈ units.mk0 a ha • _, from inv_smul_mem_iff

lemma mem_inv_smul_finset_iff₀ (ha : a ≠ 0) : b ∈ a⁻¹ • s ↔ a • b ∈ s :=
show _ ∈ (units.mk0 a ha)⁻¹ • _ ↔ _, from mem_inv_smul_finset_iff

@[simp] lemma smul_finset_subset_smul_finset_iff₀ (ha : a ≠ 0) : a • s ⊆ a • t ↔ s ⊆ t :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from smul_finset_subset_smul_finset_iff

lemma smul_finset_subset_iff₀ (ha : a ≠ 0) : a • s ⊆ t ↔ s ⊆ a⁻¹ • t :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from smul_finset_subset_iff

lemma subset_smul_finset_iff₀ (ha : a ≠ 0) : s ⊆ a • t ↔ a⁻¹ • s ⊆ t :=
show _ ⊆ units.mk0 a ha • _ ↔ _, from subset_smul_finset_iff

lemma smul_univ₀ [fintype β] {s : finset α} (hs : ¬ s ⊆ 0) : s • (univ : finset β) = univ :=
coe_injective $ by { rw ←coe_subset at hs, push_cast at ⊢ hs, exact set.smul_univ₀ hs }

lemma smul_finset_univ₀ [fintype β] (ha : a ≠ 0) : a • (univ : finset β) = univ :=
coe_injective $ by {  push_cast, exact set.smul_set_univ₀ ha }

end group_with_zero

section smul_with_zero
variables [has_zero α] [has_zero β] [smul_with_zero α β] [decidable_eq β] {s : finset α}
  {t : finset β}

/-!
Note that we have neither `smul_with_zero α (finset β)` nor `smul_with_zero (finset α) (finset β)`
because `0 * ∅ ≠ 0`.
-/

lemma smul_zero_subset (s : finset α) : s • (0 : finset β) ⊆ 0 := by simp [subset_iff, mem_smul]
lemma zero_smul_subset (t : finset β) : (0 : finset α) • t ⊆ 0 := by simp [subset_iff, mem_smul]

lemma nonempty.smul_zero (hs : s.nonempty) : s • (0 : finset β) = 0 :=
s.smul_zero_subset.antisymm $ by simpa [mem_smul] using hs

lemma nonempty.zero_smul (ht : t.nonempty) : (0 : finset α) • t = 0 :=
t.zero_smul_subset.antisymm $ by simpa [mem_smul] using ht

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
lemma zero_smul_finset {s : finset β} (h : s.nonempty) : (0 : α) • s = (0 : finset β) :=
coe_injective $ by simpa using set.zero_smul_set h

lemma zero_smul_finset_subset (s : finset β) : (0 : α) • s ⊆ 0 :=
image_subset_iff.2 $ λ x _, mem_zero.2 $ zero_smul α x

lemma zero_mem_smul_finset {t : finset β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
mem_smul_finset.2 ⟨0, h, smul_zero _⟩

variables [no_zero_smul_divisors α β] {a : α}

lemma zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.nonempty ∨ (0 : β) ∈ t ∧ s.nonempty :=
by { rw [←mem_coe, coe_smul, set.zero_mem_smul_iff], refl }

lemma zero_mem_smul_finset_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
by { rw [←mem_coe, coe_smul_finset, set.zero_mem_smul_set_iff ha, mem_coe], apply_instance }

end smul_with_zero

section monoid
variables [monoid α] [add_group β] [distrib_mul_action α β] [decidable_eq β] (a : α) (s : finset α)
  (t : finset β)

@[simp] lemma smul_finset_neg : a • -t = -(a • t) :=
by simp only [←image_smul, ←image_neg, function.comp, image_image, smul_neg]

@[simp] protected lemma smul_neg : s • -t = -(s • t) :=
by { simp_rw ←image_neg, exact image_image₂_right_comm smul_neg }

end monoid

section ring
variables [ring α] [add_comm_group β] [module α β] [decidable_eq β] {s : finset α} {t : finset β}
  {a : α}

@[simp] lemma neg_smul_finset : -a • t = -(a • t) :=
by simp only [←image_smul, ←image_neg, image_image, neg_smul]

@[simp] protected lemma neg_smul [decidable_eq α] : -s • t = -(s • t) :=
by { simp_rw ←image_neg, exact image₂_image_left_comm neg_smul }

end ring
end finset
