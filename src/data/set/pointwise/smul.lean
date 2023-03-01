/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import algebra.module.basic
import data.set.pairwise
import data.set.pointwise.basic
import tactic.by_contra

/-!
# Pointwise operations of sets

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines pointwise algebraic operations on sets.

## Main declarations

For sets `s` and `t` and scalar `a`:
* `s • t`: Scalar multiplication, set of all `x • y` where `x ∈ s` and `y ∈ t`.
* `s +ᵥ t`: Scalar addition, set of all `x +ᵥ y` where `x ∈ s` and `y ∈ t`.
* `s -ᵥ t`: Scalar subtraction, set of all `x -ᵥ y` where `x ∈ s` and `y ∈ t`.
* `a • s`: Scaling, set of all `a • x` where `x ∈ s`.
* `a +ᵥ s`: Translation, set of all `a +ᵥ x` where `x ∈ s`.

For `α` a semigroup/monoid, `set α` is a semigroup/monoid.

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

* We put all instances in the locale `pointwise`, so that these instances are not available by
  default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
  since we expect the locale to be open whenever the instances are actually used (and making the
  instances reducible changes the behavior of `simp`.

-/

open function

variables {F α β γ : Type*}

namespace set

open_locale pointwise

/-! ### Translation/scaling of sets -/

section smul

/-- The dilation of set `x • s` is defined as `{x • y | y ∈ s}` in locale `pointwise`. -/
@[to_additive "The translation of set `x +ᵥ s` is defined as `{x +ᵥ y | y ∈ s}` in
locale `pointwise`."]
protected def has_smul_set [has_smul α β] : has_smul α (set β) :=
⟨λ a, image (has_smul.smul a)⟩

/-- The pointwise scalar multiplication of sets `s • t` is defined as `{x • y | x ∈ s, y ∈ t}` in
locale `pointwise`. -/
@[to_additive "The pointwise scalar addition of sets `s +ᵥ t` is defined as
`{x +ᵥ y | x ∈ s, y ∈ t}` in locale `pointwise`."]
protected def has_smul [has_smul α β] : has_smul (set α) (set β) :=
⟨image2 has_smul.smul⟩

localized "attribute [instance] set.has_smul_set set.has_smul" in pointwise
localized "attribute [instance] set.has_vadd_set set.has_vadd" in pointwise

section has_smul
variables {ι : Sort*} {κ : ι → Sort*} [has_smul α β] {s s₁ s₂ : set α} {t t₁ t₂ u : set β} {a : α}
  {b : β}

@[simp, to_additive]
lemma image2_smul : image2 has_smul.smul s t = s • t := rfl

@[to_additive add_image_prod]
lemma image_smul_prod : (λ x : α × β, x.fst • x.snd) '' s ×ˢ t = s • t := image_prod _

@[to_additive]
lemma mem_smul : b ∈ s • t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x • y = b := iff.rfl

@[to_additive] lemma smul_mem_smul : a ∈ s → b ∈ t → a • b ∈ s • t := mem_image2_of_mem

@[simp, to_additive] lemma empty_smul : (∅ : set α) • t = ∅ := image2_empty_left
@[simp, to_additive] lemma smul_empty : s • (∅ : set β) = ∅ := image2_empty_right
@[simp, to_additive] lemma smul_eq_empty : s • t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp, to_additive] lemma smul_nonempty : (s • t).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
@[to_additive] lemma nonempty.smul : s.nonempty → t.nonempty → (s • t).nonempty := nonempty.image2
@[to_additive] lemma nonempty.of_smul_left : (s • t).nonempty → s.nonempty :=
nonempty.of_image2_left
@[to_additive] lemma nonempty.of_smul_right : (s • t).nonempty → t.nonempty :=
nonempty.of_image2_right
@[simp, to_additive] lemma smul_singleton : s • {b} = (• b) '' s := image2_singleton_right
@[simp, to_additive] lemma singleton_smul : ({a} : set α) • t = a • t := image2_singleton_left
@[simp, to_additive] lemma singleton_smul_singleton : ({a} : set α) • ({b} : set β) = {a • b} :=
image2_singleton

@[to_additive, mono] lemma smul_subset_smul : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ • t₁ ⊆ s₂ • t₂ := image2_subset
@[to_additive] lemma smul_subset_smul_left : t₁ ⊆ t₂ → s • t₁ ⊆ s • t₂ := image2_subset_left
@[to_additive] lemma smul_subset_smul_right : s₁ ⊆ s₂ → s₁ • t ⊆ s₂ • t := image2_subset_right
@[to_additive] lemma smul_subset_iff : s • t ⊆ u ↔ ∀ (a ∈ s) (b ∈ t), a • b ∈ u := image2_subset_iff

attribute [mono] vadd_subset_vadd

@[to_additive] lemma union_smul : (s₁ ∪ s₂) • t = s₁ • t ∪ s₂ • t := image2_union_left
@[to_additive] lemma smul_union : s • (t₁ ∪ t₂) = s • t₁ ∪ s • t₂ := image2_union_right
@[to_additive] lemma inter_smul_subset : (s₁ ∩ s₂) • t ⊆ s₁ • t ∩ s₂ • t := image2_inter_subset_left
@[to_additive] lemma smul_inter_subset : s • (t₁ ∩ t₂) ⊆ s • t₁ ∩ s • t₂ :=
image2_inter_subset_right

@[to_additive] lemma Union_smul_left_image : (⋃ a ∈ s, a • t) = s • t := Union_image_left _
@[to_additive] lemma Union_smul_right_image : (⋃ a ∈ t, (• a) '' s) = s • t := Union_image_right _

@[to_additive] lemma Union_smul (s : ι → set α) (t : set β) : (⋃ i, s i) • t = ⋃ i, s i • t :=
image2_Union_left _ _ _
@[to_additive] lemma smul_Union (s : set α) (t : ι → set β) : s • (⋃ i, t i) = ⋃ i, s • t i :=
image2_Union_right _ _ _

@[to_additive]
lemma Union₂_smul (s : Π i, κ i → set α) (t : set β) : (⋃ i j, s i j) • t = ⋃ i j, s i j • t :=
image2_Union₂_left _ _ _

@[to_additive]
lemma smul_Union₂ (s : set α) (t : Π i, κ i → set β) : s • (⋃ i j, t i j) = ⋃ i j, s • t i j :=
image2_Union₂_right _ _ _

@[to_additive]
lemma Inter_smul_subset (s : ι → set α) (t : set β) : (⋂ i, s i) • t ⊆ ⋂ i, s i • t :=
image2_Inter_subset_left _ _ _

@[to_additive]
lemma smul_Inter_subset (s : set α) (t : ι → set β) : s • (⋂ i, t i) ⊆ ⋂ i, s • t i :=
image2_Inter_subset_right _ _ _

@[to_additive]
lemma Inter₂_smul_subset (s : Π i, κ i → set α) (t : set β) :
  (⋂ i j, s i j) • t ⊆ ⋂ i j, s i j • t :=
image2_Inter₂_subset_left _ _ _

@[to_additive]
lemma smul_Inter₂_subset (s : set α) (t : Π i, κ i → set β) :
  s • (⋂ i j, t i j) ⊆ ⋂ i j, s • t i j :=
image2_Inter₂_subset_right _ _ _

@[simp, to_additive] lemma bUnion_smul_set (s : set α) (t : set β) :
  (⋃ a ∈ s, a • t) = s • t :=
Union_image_left _

end has_smul

section has_smul_set
variables {ι : Sort*} {κ : ι → Sort*} [has_smul α β] {s t t₁ t₂ : set β} {a : α} {b : β} {x y : β}

@[simp, to_additive] lemma image_smul : (λ x, a • x) '' t = a • t := rfl

@[to_additive] lemma mem_smul_set : x ∈ a • t ↔ ∃ y, y ∈ t ∧ a • y = x := iff.rfl

@[to_additive] lemma smul_mem_smul_set : b ∈ s → a • b ∈ a • s := mem_image_of_mem _

@[simp, to_additive] lemma smul_set_empty : a • (∅ : set β) = ∅ := image_empty _
@[simp, to_additive] lemma smul_set_eq_empty : a • s = ∅ ↔ s = ∅ := image_eq_empty
@[simp, to_additive] lemma smul_set_nonempty : (a • s).nonempty ↔ s.nonempty := nonempty_image_iff

@[simp, to_additive] lemma smul_set_singleton : a • ({b} : set β) = {a • b} := image_singleton

@[to_additive] lemma smul_set_mono : s ⊆ t → a • s ⊆ a • t := image_subset _
@[to_additive] lemma smul_set_subset_iff : a • s ⊆ t ↔ ∀ ⦃b⦄, b ∈ s → a • b ∈ t := image_subset_iff

@[to_additive] lemma smul_set_union : a • (t₁ ∪ t₂) = a • t₁ ∪ a • t₂ := image_union _ _ _

@[to_additive]
lemma smul_set_inter_subset : a • (t₁ ∩ t₂) ⊆ a • t₁ ∩ (a • t₂) := image_inter_subset _ _ _

@[to_additive]
lemma smul_set_Union (a : α) (s : ι → set β) : a • (⋃ i, s i) = ⋃ i, a • s i := image_Union

@[to_additive]
lemma smul_set_Union₂ (a : α) (s : Π i, κ i → set β) : a • (⋃ i j, s i j) = ⋃ i j, a • s i j :=
image_Union₂ _ _

@[to_additive]
lemma smul_set_Inter_subset (a : α) (t : ι → set β) : a • (⋂ i, t i) ⊆ ⋂ i, a • t i :=
image_Inter_subset _ _

@[to_additive]
lemma smul_set_Inter₂_subset (a : α) (t : Π i, κ i → set β) :
  a • (⋂ i j, t i j) ⊆ ⋂ i j, a • t i j :=
image_Inter₂_subset _ _

@[to_additive] lemma nonempty.smul_set : s.nonempty → (a • s).nonempty := nonempty.image _

end has_smul_set

variables {s s₁ s₂ : set α} {t t₁ t₂ : set β} {a : α} {b : β}

@[simp, to_additive] lemma bUnion_op_smul_set [has_mul α] (s t : set α) :
  (⋃ a ∈ t, mul_opposite.op a • s) = s * t :=
Union_image_right _

@[to_additive]
theorem range_smul_range {ι κ : Type*} [has_smul α β] (b : ι → α) (c : κ → β) :
  range b • range c = range (λ p : ι × κ, b p.1 • c p.2) :=
ext $ λ x, ⟨λ hx, let ⟨p, q, ⟨i, hi⟩, ⟨j, hj⟩, hpq⟩ := set.mem_smul.1 hx in
  ⟨(i, j), hpq ▸ hi ▸ hj ▸ rfl⟩,
λ ⟨⟨i, j⟩, h⟩, set.mem_smul.2 ⟨b i, c j, ⟨i, rfl⟩, ⟨j, rfl⟩, h⟩⟩

@[to_additive] lemma smul_set_range [has_smul α β] {ι : Sort*} {f : ι → β} :
  a • range f = range (λ i, a • f i) := (range_comp _ _).symm

@[to_additive]
instance smul_comm_class_set [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α β (set γ) :=
⟨λ _ _, commute.set_image $ smul_comm _ _⟩

@[to_additive]
instance smul_comm_class_set' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class α (set β) (set γ) :=
⟨λ _ _ _, image_image2_distrib_right $ smul_comm _⟩

@[to_additive]
instance smul_comm_class_set'' [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) β (set γ) :=
by haveI := smul_comm_class.symm α β γ; exact smul_comm_class.symm _ _ _

@[to_additive]
instance smul_comm_class [has_smul α γ] [has_smul β γ] [smul_comm_class α β γ] :
  smul_comm_class (set α) (set β) (set γ) :=
⟨λ _ _ _, image2_left_comm smul_comm⟩

@[to_additive]
instance is_scalar_tower [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α β (set γ) :=
{ smul_assoc := λ a b T, by simp only [←image_smul, image_image, smul_assoc] }

@[to_additive]
instance is_scalar_tower' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower α (set β) (set γ) :=
⟨λ _ _ _, image2_image_left_comm $ smul_assoc _⟩

@[to_additive]
instance is_scalar_tower'' [has_smul α β] [has_smul α γ] [has_smul β γ] [is_scalar_tower α β γ] :
  is_scalar_tower (set α) (set β) (set γ) :=
{ smul_assoc := λ T T' T'', image2_assoc smul_assoc }

instance is_central_scalar [has_smul α β] [has_smul αᵐᵒᵖ β] [is_central_scalar α β] :
  is_central_scalar α (set β) :=
⟨λ a S, congr_arg (λ f, f '' S) $ by exact funext (λ _, op_smul_eq_smul _ _)⟩

/-- A multiplicative action of a monoid `α` on a type `β` gives a multiplicative action of `set α`
on `set β`. -/
@[to_additive "An additive action of an additive monoid `α` on a type `β` gives an additive action
of `set α` on `set β`"]
protected def mul_action [monoid α] [mul_action α β] : mul_action (set α) (set β) :=
{ mul_smul := λ _ _ _, image2_assoc mul_smul,
  one_smul := λ s, image2_singleton_left.trans $ by simp_rw [one_smul, image_id'] }

/-- A multiplicative action of a monoid on a type `β` gives a multiplicative action on `set β`. -/
@[to_additive "An additive action of an additive monoid on a type `β` gives an additive action
on `set β`."]
protected def mul_action_set [monoid α] [mul_action α β] : mul_action α (set β) :=
{ mul_smul := by { intros, simp only [← image_smul, image_image, ← mul_smul] },
  one_smul := by { intros, simp only [← image_smul, one_smul, image_id'] } }

localized "attribute [instance] set.mul_action_set set.add_action_set
  set.mul_action set.add_action" in pointwise

/-- A distributive multiplicative action of a monoid on an additive monoid `β` gives a distributive
multiplicative action on `set β`. -/
protected def distrib_mul_action_set [monoid α] [add_monoid β] [distrib_mul_action α β] :
  distrib_mul_action α (set β) :=
{ smul_add := λ _ _ _, image_image2_distrib $ smul_add _,
  smul_zero := λ _, image_singleton.trans $ by rw [smul_zero, singleton_zero] }

/-- A multiplicative action of a monoid on a monoid `β` gives a multiplicative action on `set β`. -/
protected def mul_distrib_mul_action_set [monoid α] [monoid β] [mul_distrib_mul_action α β] :
  mul_distrib_mul_action α (set β) :=
{ smul_mul := λ _ _ _, image_image2_distrib $ smul_mul' _,
  smul_one := λ _, image_singleton.trans $ by rw [smul_one, singleton_one] }

localized "attribute [instance] set.distrib_mul_action_set set.mul_distrib_mul_action_set"
  in pointwise

instance [has_zero α] [has_zero β] [has_smul α β] [no_zero_smul_divisors α β] :
  no_zero_smul_divisors (set α) (set β) :=
⟨λ s t h, begin
  by_contra' H,
  have hst : (s • t).nonempty := h.symm.subst zero_nonempty,
  simp_rw [←hst.of_smul_left.subset_zero_iff, ←hst.of_smul_right.subset_zero_iff, not_subset,
    mem_zero] at H,
  obtain ⟨⟨a, hs, ha⟩, b, ht, hb⟩ := H,
  exact (eq_zero_or_eq_zero_of_smul_eq_zero $ h.subset $ smul_mem_smul hs ht).elim ha hb,
end⟩

instance no_zero_smul_divisors_set [has_zero α] [has_zero β] [has_smul α β]
  [no_zero_smul_divisors α β] : no_zero_smul_divisors α (set β) :=
⟨λ a s h, begin
  by_contra' H,
  have hst : (a • s).nonempty := h.symm.subst zero_nonempty,
  simp_rw [←hst.of_image.subset_zero_iff, not_subset, mem_zero] at H,
  obtain ⟨ha, b, ht, hb⟩ := H,
  exact (eq_zero_or_eq_zero_of_smul_eq_zero $ h.subset $ smul_mem_smul_set ht).elim ha hb,
end⟩

instance [has_zero α] [has_mul α] [no_zero_divisors α] : no_zero_divisors (set α) :=
⟨λ s t h, eq_zero_or_eq_zero_of_smul_eq_zero h⟩

end smul

section vsub
variables {ι : Sort*} {κ : ι → Sort*} [has_vsub α β] {s s₁ s₂ t t₁ t₂ : set β} {u : set α} {a : α}
  {b c : β}
include α

instance has_vsub : has_vsub (set α) (set β) := ⟨image2 (-ᵥ)⟩

@[simp] lemma image2_vsub : (image2 has_vsub.vsub s t : set α) = s -ᵥ t := rfl

lemma image_vsub_prod : (λ x : β × β, x.fst -ᵥ x.snd) '' s ×ˢ t = s -ᵥ t := image_prod _

lemma mem_vsub : a ∈ s -ᵥ t ↔ ∃ x y, x ∈ s ∧ y ∈ t ∧ x -ᵥ y = a := iff.rfl

lemma vsub_mem_vsub (hb : b ∈ s) (hc : c ∈ t) : b -ᵥ c ∈ s -ᵥ t := mem_image2_of_mem hb hc

@[simp] lemma empty_vsub (t : set β) : ∅ -ᵥ t = ∅ := image2_empty_left
@[simp] lemma vsub_empty (s : set β) : s -ᵥ ∅ = ∅ := image2_empty_right
@[simp] lemma vsub_eq_empty : s -ᵥ t = ∅ ↔ s = ∅ ∨ t = ∅ := image2_eq_empty_iff
@[simp] lemma vsub_nonempty : (s -ᵥ t : set α).nonempty ↔ s.nonempty ∧ t.nonempty :=
image2_nonempty_iff
lemma nonempty.vsub : s.nonempty → t.nonempty → (s -ᵥ t : set α).nonempty := nonempty.image2
lemma nonempty.of_vsub_left : (s -ᵥ t :set α).nonempty → s.nonempty := nonempty.of_image2_left
lemma nonempty.of_vsub_right : (s -ᵥ t : set α).nonempty → t.nonempty := nonempty.of_image2_right
@[simp] lemma vsub_singleton (s : set β) (b : β) : s -ᵥ {b} = (-ᵥ b) '' s := image2_singleton_right
@[simp] lemma singleton_vsub (t : set β) (b : β) : {b} -ᵥ t = ((-ᵥ) b) '' t := image2_singleton_left
@[simp] lemma singleton_vsub_singleton : ({b} : set β) -ᵥ {c} = {b -ᵥ c} := image2_singleton

@[mono] lemma vsub_subset_vsub : s₁ ⊆ s₂ → t₁ ⊆ t₂ → s₁ -ᵥ t₁ ⊆ s₂ -ᵥ t₂ := image2_subset
lemma vsub_subset_vsub_left : t₁ ⊆ t₂ → s -ᵥ t₁ ⊆ s -ᵥ t₂ := image2_subset_left
lemma vsub_subset_vsub_right : s₁ ⊆ s₂ → s₁ -ᵥ t ⊆ s₂ -ᵥ t := image2_subset_right
lemma vsub_subset_iff : s -ᵥ t ⊆ u ↔ ∀ (x ∈ s) (y ∈ t), x -ᵥ y ∈ u := image2_subset_iff
lemma vsub_self_mono (h : s ⊆ t) : s -ᵥ s ⊆ t -ᵥ t := vsub_subset_vsub h h

lemma union_vsub : (s₁ ∪ s₂) -ᵥ t = s₁ -ᵥ t ∪ (s₂ -ᵥ t) := image2_union_left
lemma vsub_union : s -ᵥ (t₁ ∪ t₂) = s -ᵥ t₁ ∪ (s -ᵥ t₂) := image2_union_right
lemma inter_vsub_subset : s₁ ∩ s₂ -ᵥ t ⊆ (s₁ -ᵥ t) ∩ (s₂ -ᵥ t) := image2_inter_subset_left
lemma vsub_inter_subset : s -ᵥ t₁ ∩ t₂ ⊆ (s -ᵥ t₁) ∩ (s -ᵥ t₂) := image2_inter_subset_right

lemma Union_vsub_left_image : (⋃ a ∈ s, ((-ᵥ) a) '' t) = s -ᵥ t := Union_image_left _
lemma Union_vsub_right_image : (⋃ a ∈ t, (-ᵥ a) '' s) = s -ᵥ t := Union_image_right _

lemma Union_vsub (s : ι → set β) (t : set β) : (⋃ i, s i) -ᵥ t = ⋃ i, s i -ᵥ t :=
image2_Union_left _ _ _
lemma vsub_Union (s : set β) (t : ι → set β) : s -ᵥ (⋃ i, t i) = ⋃ i, s -ᵥ t i :=
image2_Union_right _ _ _

lemma Union₂_vsub (s : Π i, κ i → set β) (t : set β) : (⋃ i j, s i j) -ᵥ t = ⋃ i j, s i j -ᵥ t :=
image2_Union₂_left _ _ _

lemma vsub_Union₂ (s : set β) (t : Π i, κ i → set β) : s -ᵥ (⋃ i j, t i j) = ⋃ i j, s -ᵥ t i j :=
image2_Union₂_right _ _ _

lemma Inter_vsub_subset (s : ι → set β) (t : set β) : (⋂ i, s i) -ᵥ t ⊆ ⋂ i, s i -ᵥ t :=
image2_Inter_subset_left _ _ _

lemma vsub_Inter_subset (s : set β) (t : ι → set β) : s -ᵥ (⋂ i, t i) ⊆ ⋂ i, s -ᵥ t i :=
image2_Inter_subset_right _ _ _

lemma Inter₂_vsub_subset (s : Π i, κ i → set β) (t : set β) :
  (⋂ i j, s i j) -ᵥ t ⊆ ⋂ i j, s i j -ᵥ t :=
image2_Inter₂_subset_left _ _ _

lemma vsub_Inter₂_subset (s : set β) (t : Π i, κ i → set β) :
  s -ᵥ (⋂ i j, t i j) ⊆ ⋂ i j, s -ᵥ t i j :=
image2_Inter₂_subset_right _ _ _


end vsub

open_locale pointwise

section smul_with_zero
variables [has_zero α] [has_zero β] [smul_with_zero α β] {s : set α} {t : set β}

/-!
Note that we have neither `smul_with_zero α (set β)` nor `smul_with_zero (set α) (set β)`
because `0 * ∅ ≠ 0`.
-/

lemma smul_zero_subset (s : set α) : s • (0 : set β) ⊆ 0 := by simp [subset_def, mem_smul]
lemma zero_smul_subset (t : set β) : (0 : set α) • t ⊆ 0 := by simp [subset_def, mem_smul]

lemma nonempty.smul_zero (hs : s.nonempty) : s • (0 : set β) = 0 :=
s.smul_zero_subset.antisymm $ by simpa [mem_smul] using hs

lemma nonempty.zero_smul (ht : t.nonempty) : (0 : set α) • t = 0 :=
t.zero_smul_subset.antisymm $ by simpa [mem_smul] using ht

/-- A nonempty set is scaled by zero to the singleton set containing 0. -/
lemma zero_smul_set {s : set β} (h : s.nonempty) : (0 : α) • s = (0 : set β) :=
by simp only [← image_smul, image_eta, zero_smul, h.image_const, singleton_zero]

lemma zero_smul_set_subset (s : set β) : (0 : α) • s ⊆ 0 :=
image_subset_iff.2 $ λ x _, zero_smul α x

lemma subsingleton_zero_smul_set (s : set β) : ((0 : α) • s).subsingleton :=
subsingleton_singleton.anti $ zero_smul_set_subset s

lemma zero_mem_smul_set {t : set β} {a : α} (h : (0 : β) ∈ t) : (0 : β) ∈ a • t :=
⟨0, h, smul_zero _⟩

variables [no_zero_smul_divisors α β] {a : α}

lemma zero_mem_smul_iff : (0 : β) ∈ s • t ↔ (0 : α) ∈ s ∧ t.nonempty ∨ (0 : β) ∈ t ∧ s.nonempty :=
begin
  split,
  { rintro ⟨a, b, ha, hb, h⟩,
    obtain rfl | rfl := eq_zero_or_eq_zero_of_smul_eq_zero h,
    { exact or.inl ⟨ha, b, hb⟩ },
    { exact or.inr ⟨hb, a, ha⟩ } },
  { rintro (⟨hs, b, hb⟩ | ⟨ht, a, ha⟩),
    { exact ⟨0, b, hs, hb, zero_smul _ _⟩ },
    { exact ⟨a, 0, ha, ht, smul_zero _⟩ } }
end

lemma zero_mem_smul_set_iff (ha : a ≠ 0) : (0 : β) ∈ a • t ↔ (0 : β) ∈ t :=
begin
  refine ⟨_, zero_mem_smul_set⟩,
  rintro ⟨b, hb, h⟩,
  rwa (eq_zero_or_eq_zero_of_smul_eq_zero h).resolve_left ha at hb,
end

end smul_with_zero

section left_cancel_semigroup
variables [left_cancel_semigroup α] {s t : set α}

@[to_additive] lemma pairwise_disjoint_smul_iff :
  s.pairwise_disjoint (• t) ↔ (s ×ˢ t).inj_on (λ p, p.1 * p.2) :=
pairwise_disjoint_image_right_iff $ λ _ _, mul_right_injective _

end left_cancel_semigroup

section group
variables [group α] [mul_action α β] {s t A B : set β} {a : α} {x : β}

@[simp, to_additive]
lemma smul_mem_smul_set_iff : a • x ∈ a • s ↔ x ∈ s := (mul_action.injective _).mem_set_image

@[to_additive]
lemma mem_smul_set_iff_inv_smul_mem : x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show x ∈ mul_action.to_perm a '' A ↔ _, from mem_image_equiv

@[to_additive]
lemma mem_inv_smul_set_iff : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
by simp only [← image_smul, mem_image, inv_smul_eq_iff, exists_eq_right]

@[to_additive]
lemma preimage_smul (a : α) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
((mul_action.to_perm a).symm.image_eq_preimage _).symm

@[to_additive]
lemma preimage_smul_inv (a : α) (t : set β) : (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul (to_units a)⁻¹ t

@[simp, to_additive]
lemma set_smul_subset_set_smul_iff : a • A ⊆ a • B ↔ A ⊆ B :=
image_subset_image_iff $ mul_action.injective _

@[to_additive]
lemma set_smul_subset_iff : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
(image_subset_iff).trans $ iff_of_eq $ congr_arg _ $
  preimage_equiv_eq_image_symm _ $ mul_action.to_perm _

@[to_additive]
lemma subset_set_smul_iff : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
iff.symm $ (image_subset_iff).trans $ iff.symm $ iff_of_eq $ congr_arg _ $
  image_equiv_eq_preimage_symm _ $ mul_action.to_perm _

@[to_additive] lemma smul_set_inter : a • (s ∩ t) = a • s ∩ a • t :=
image_inter $ mul_action.injective a

@[to_additive] lemma smul_set_sdiff : a • (s \ t) = a • s \ a • t :=
image_diff (mul_action.injective a) _ _

@[to_additive] lemma smul_set_symm_diff : a • (s ∆ t) = (a • s) ∆ (a • t) :=
image_symm_diff (mul_action.injective a) _ _

@[simp, to_additive] lemma smul_set_univ : a • (univ : set β) = univ :=
image_univ_of_surjective $ mul_action.surjective a

@[simp, to_additive] lemma smul_univ {s : set α} (hs : s.nonempty) : s • (univ : set β) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩

@[to_additive]
lemma smul_inter_ne_empty_iff {s t : set α} {x : α} :
  x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a * b⁻¹ = x :=
begin
  rw ←nonempty_iff_ne_empty,
  split,
  { rintros ⟨a, h, ha⟩,
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h,
    exact ⟨x • b, b, ⟨ha, hb⟩, by simp⟩, },
  { rintros ⟨a, b, ⟨ha, hb⟩, rfl⟩,
    exact ⟨a, mem_inter (mem_smul_set.mpr ⟨b, hb, by simp⟩) ha⟩, },
end

@[to_additive]
lemma smul_inter_ne_empty_iff' {s t : set α} {x : α} :
  x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ t ∧ b ∈ s) ∧ a / b = x :=
by simp_rw [smul_inter_ne_empty_iff, div_eq_mul_inv]

@[to_additive]
lemma op_smul_inter_ne_empty_iff {s t : set α} {x : αᵐᵒᵖ} :
  x • s ∩ t ≠ ∅ ↔ ∃ a b, (a ∈ s ∧ b ∈ t) ∧ a⁻¹ * b = mul_opposite.unop x :=
begin
  rw ←nonempty_iff_ne_empty,
  split,
  { rintros ⟨a, h, ha⟩,
    obtain ⟨b, hb, rfl⟩ := mem_smul_set.mp h,
    exact ⟨b, x • b, ⟨hb, ha⟩, by simp⟩, },
  { rintros ⟨a, b, ⟨ha, hb⟩, H⟩,
    have : mul_opposite.op (a⁻¹ * b) = x := congr_arg mul_opposite.op H,
    exact ⟨b, mem_inter (mem_smul_set.mpr ⟨a, ha, by simp [← this]⟩) hb⟩, },
end

@[simp, to_additive] lemma Union_inv_smul :
  (⋃ (g : α), g⁻¹ • s) = (⋃ (g : α), g • s) :=
function.surjective.supr_congr _ inv_surjective $ λ g, rfl

@[to_additive]
lemma Union_smul_eq_set_of_exists {s : set β} :
  (⋃ (g : α), g • s) = {a | ∃ (g : α), g • a ∈ s} :=
by simp_rw [← Union_set_of, ← Union_inv_smul, ← preimage_smul, preimage]

end group

section group_with_zero
variables [group_with_zero α] [mul_action α β] {s t : set β} {a : α}

@[simp] lemma smul_mem_smul_set_iff₀ (ha : a ≠ 0) (A : set β)
  (x : β) : a • x ∈ a • A ↔ x ∈ A :=
show units.mk0 a ha • _ ∈ _ ↔ _, from smul_mem_smul_set_iff

lemma mem_smul_set_iff_inv_smul_mem₀ (ha : a ≠ 0) (A : set β) (x : β) :
  x ∈ a • A ↔ a⁻¹ • x ∈ A :=
show _ ∈ units.mk0 a ha • _ ↔ _, from mem_smul_set_iff_inv_smul_mem

lemma mem_inv_smul_set_iff₀ (ha : a ≠ 0) (A : set β) (x : β) : x ∈ a⁻¹ • A ↔ a • x ∈ A :=
show _ ∈ (units.mk0 a ha)⁻¹ • _ ↔ _, from mem_inv_smul_set_iff

lemma preimage_smul₀ (ha : a ≠ 0) (t : set β) : (λ x, a • x) ⁻¹' t = a⁻¹ • t :=
preimage_smul (units.mk0 a ha) t

lemma preimage_smul_inv₀ (ha : a ≠ 0) (t : set β) :
  (λ x, a⁻¹ • x) ⁻¹' t = a • t :=
preimage_smul ((units.mk0 a ha)⁻¹) t

@[simp] lemma set_smul_subset_set_smul_iff₀ (ha : a ≠ 0) {A B : set β} :
  a • A ⊆ a • B ↔ A ⊆ B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_set_smul_iff

lemma set_smul_subset_iff₀ (ha : a ≠ 0) {A B : set β} : a • A ⊆ B ↔ A ⊆ a⁻¹ • B :=
show units.mk0 a ha • _ ⊆ _ ↔ _, from set_smul_subset_iff

lemma subset_set_smul_iff₀ (ha : a ≠ 0) {A B : set β} : A ⊆ a • B ↔ a⁻¹ • A ⊆ B :=
show _ ⊆ units.mk0 a ha • _ ↔ _, from subset_set_smul_iff

lemma smul_set_inter₀ (ha : a ≠ 0) : a • (s ∩ t) = a • s ∩ a • t :=
show units.mk0 a ha • _ = _, from smul_set_inter

lemma smul_set_sdiff₀ (ha : a ≠ 0) : a • (s \ t) = a • s \ a • t :=
image_diff (mul_action.injective₀ ha) _ _

lemma smul_set_symm_diff₀ (ha : a ≠ 0) : a • (s ∆ t) = (a • s) ∆ (a • t) :=
image_symm_diff (mul_action.injective₀ ha) _ _

lemma smul_set_univ₀ (ha : a ≠ 0) : a • (univ : set β) = univ :=
image_univ_of_surjective $ mul_action.surjective₀ ha

lemma smul_univ₀ {s : set α} (hs : ¬ s ⊆ 0) : s • (univ : set β) = univ :=
let ⟨a, ha, ha₀⟩ := not_subset.1 hs in eq_univ_of_forall $ λ b,
  ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩

lemma smul_univ₀' {s : set α} (hs : s.nontrivial) : s • (univ : set β) = univ :=
smul_univ₀ hs.not_subset_singleton

end group_with_zero

section monoid
variables [monoid α] [add_group β] [distrib_mul_action α β] (a : α) (s : set α) (t : set β)

@[simp] lemma smul_set_neg : a • -t = -(a • t) :=
by simp_rw [←image_smul, ←image_neg, image_image, smul_neg]

@[simp] protected lemma smul_neg : s • -t = -(s • t) :=
by { simp_rw ←image_neg, exact image_image2_right_comm smul_neg }

end monoid

section ring
variables [ring α] [add_comm_group β] [module α β] (a : α) (s : set α) (t : set β)

@[simp] lemma neg_smul_set : -a • t = -(a • t) :=
by simp_rw [←image_smul, ←image_neg, image_image, neg_smul]

@[simp] protected lemma neg_smul : -s • t = -(s • t) :=
by { simp_rw ←image_neg, exact image2_image_left_comm neg_smul }

end ring

end set
