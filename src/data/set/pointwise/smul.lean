/-
Copyright (c) 2019 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Floris van Doorn
-/
import algebra.module.basic
import data.list.of_fn
import data.set.pairwise
import data.set.pointwise.basic

/-!
# Algebraic structure of pointwise operations

This file provides lemmas for pointwise operations on `set` in monoids, groups, modules, and shows
that `set α` is a semigroup/monoid/... if `α` is.

## Main declarations

Appropriate definitions and results are also transported to the additive theory via `to_additive`.

## Implementation notes

We put all instances in the locale `pointwise`, so that these instances are not available by
default. Note that we do not mark them as reducible (as argued by note [reducible non-instances])
since we expect the locale to be open whenever the instances are actually used (and making the
instances reducible changes the behavior of `simp`.

Given that `set α` is a monoid when `α` is, `n • s`, where `n : ℕ`, is ambiguous between pointwise
scaling and repeated pointwise addition; the former has `(2 : ℕ) • {1, 2} = {2, 4}`, while the
latter has `(2 : ℕ) • {1, 2} = {2, 3, 4}`. See note [pointwise nat action].

## TODO

Rename this file to something more sensible. See #17812.
-/

open function
open_locale pointwise

variables {F α β γ : Type*}

namespace set
section monoid
variables [monoid α] {s t : set α} {a : α} {m n : ℕ}

@[to_additive] lemma pow_subset_pow_of_one_mem (hs : (1 : α) ∈ s) : m ≤ n → s ^ m ⊆ s ^ n :=
begin
  refine nat.le_induction _ (λ n h ih, _) _,
  { exact subset.rfl },
  { rw pow_succ,
    exact ih.trans (subset_mul_right _ hs) }
end

@[to_additive] lemma mem_prod_list_of_fn {a : α} {s : fin n → set α} :
  a ∈ (list.of_fn s).prod ↔ ∃ f : Π i, s i, (list.of_fn $ λ i, (f i : α)).prod = a :=
begin
  induction n with n ih generalizing a,
  { simp_rw [list.of_fn_zero, list.prod_nil, fin.exists_fin_zero_pi, eq_comm, set.mem_one] },
  { simp_rw [list.of_fn_succ, list.prod_cons, fin.exists_fin_succ_pi, fin.cons_zero, fin.cons_succ,
      mem_mul, @ih, exists_and_distrib_left, exists_exists_eq_and, set_coe.exists, subtype.coe_mk,
      exists_prop] }
end

@[to_additive] lemma mem_list_prod {l : list (set α)} {a : α} :
  a ∈ l.prod ↔ ∃ l' : list (Σ s : set α, ↥s),
    list.prod (l'.map (λ x, (sigma.snd x : α))) = a ∧ l'.map sigma.fst = l :=
begin
  induction l using list.of_fn_rec with n f,
  simp_rw [list.exists_iff_exists_tuple, list.map_of_fn, list.of_fn_inj', and.left_comm,
    exists_and_distrib_left, exists_eq_left, heq_iff_eq, function.comp, mem_prod_list_of_fn],
  split,
  { rintros ⟨fi, rfl⟩,  exact ⟨λ i, ⟨_, fi i⟩, rfl, rfl⟩, },
  { rintros ⟨fi, rfl, rfl⟩, exact ⟨λ i, _, rfl⟩, },
end

@[to_additive] lemma mem_pow {a : α} {n : ℕ} :
  a ∈ s ^ n ↔ ∃ f : fin n → s, (list.of_fn (λ i, (f i : α))).prod = a :=
by rw [←mem_prod_list_of_fn, list.of_fn_const, list.prod_repeat]

@[simp, to_additive] lemma empty_pow {n : ℕ} (hn : n ≠ 0) : (∅ : set α) ^ n = ∅ :=
by rw [← tsub_add_cancel_of_le (nat.succ_le_of_lt $ nat.pos_of_ne_zero hn), pow_succ, empty_mul]

--TODO: `to_additive` trips up on the `1 : ℕ` used in the pattern-matching.
@[simp] lemma nsmul_univ {α : Type*} [add_monoid α] : ∀ {n : ℕ}, n ≠ 0 → n • (univ : set α) = univ
| 0 := λ h, (h rfl).elim
| 1 := λ _, one_nsmul _
| (n + 2) := λ _, by { rw [succ_nsmul, nsmul_univ n.succ_ne_zero, univ_add_univ] }

@[simp, to_additive nsmul_univ] lemma univ_pow : ∀ {n : ℕ}, n ≠ 0 → (univ : set α) ^ n = univ
| 0 := λ h, (h rfl).elim
| 1 := λ _, pow_one _
| (n + 2) := λ _, by { rw [pow_succ, univ_pow n.succ_ne_zero, univ_mul_univ] }

@[to_additive] protected lemma _root_.is_unit.set : is_unit a → is_unit ({a} : set α) :=
is_unit.map (singleton_monoid_hom : α →* set α)

end monoid

section division_monoid
variables [division_monoid α] {s t : set α}

@[simp, to_additive] lemma is_unit_iff : is_unit s ↔ ∃ a, s = {a} ∧ is_unit a :=
begin
  split,
  { rintro ⟨u, rfl⟩,
    obtain ⟨a, b, ha, hb, h⟩ := set.mul_eq_one_iff.1 u.mul_inv,
    refine ⟨a, ha, ⟨a, b, h, singleton_injective _⟩, rfl⟩,
    rw [←singleton_mul_singleton, ←ha, ←hb],
    exact u.inv_mul },
  { rintro ⟨a, rfl, ha⟩,
    exact ha.set }
end

end division_monoid

/-- `set α` has distributive negation if `α` has. -/
protected def has_distrib_neg [has_mul α] [has_distrib_neg α] : has_distrib_neg (set α) :=
{ neg_mul := λ _ _, by { simp_rw ←image_neg, exact image2_image_left_comm neg_mul },
  mul_neg := λ _ _, by { simp_rw ←image_neg, exact image_image2_right_comm mul_neg },
  ..set.has_involutive_neg }

localized "attribute [instance] set.division_monoid set.subtraction_monoid set.division_comm_monoid
  set.subtraction_comm_monoid set.has_distrib_neg" in pointwise

section distrib
variables [distrib α] (s t u : set α)

/-!
Note that `set α` is not a `distrib` because `s * t + s * u` has cross terms that `s * (t + u)`
lacks.
-/

lemma mul_add_subset : s * (t + u) ⊆ s * t + s * u := image2_distrib_subset_left mul_add
lemma add_mul_subset : (s + t) * u ⊆ s * u + t * u := image2_distrib_subset_right add_mul

end distrib

section mul_zero_class
variables [mul_zero_class α] {s t : set α}

/-! Note that `set` is not a `mul_zero_class` because `0 * ∅ ≠ 0`. -/

lemma mul_zero_subset (s : set α) : s * 0 ⊆ 0 := by simp [subset_def, mem_mul]
lemma zero_mul_subset (s : set α) : 0 * s ⊆ 0 := by simp [subset_def, mem_mul]

lemma nonempty.mul_zero (hs : s.nonempty) : s * 0 = 0 :=
s.mul_zero_subset.antisymm $ by simpa [mem_mul] using hs

lemma nonempty.zero_mul (hs : s.nonempty) : 0 * s = 0 :=
s.zero_mul_subset.antisymm $ by simpa [mem_mul] using hs

end mul_zero_class

section group
variables [group α] {s t : set α} {a b : α}

/-! Note that `set` is not a `group` because `s / s ≠ 1` in general. -/

@[to_additive] lemma is_unit_singleton (a : α) : is_unit ({a} : set α) := (group.is_unit a).set

@[simp, to_additive] lemma is_unit_iff_singleton : is_unit s ↔ ∃ a, s = {a} :=
by simp only [is_unit_iff, group.is_unit, and_true]

end group

section group_with_zero
variables [group_with_zero α] {s t : set α}

lemma div_zero_subset (s : set α) : s / 0 ⊆ 0 := by simp [subset_def, mem_div]
lemma zero_div_subset (s : set α) : 0 / s ⊆ 0 := by simp [subset_def, mem_div]

lemma nonempty.div_zero (hs : s.nonempty) : s / 0 = 0 :=
s.div_zero_subset.antisymm $ by simpa [mem_div] using hs

lemma nonempty.zero_div (hs : s.nonempty) : 0 / s = 0 :=
s.zero_div_subset.antisymm $ by simpa [mem_div] using hs

end group_with_zero

section has_mul
variables [has_mul α] [has_mul β] [mul_hom_class F α β] (m : F) {s t : set α}
include α β

@[to_additive] lemma image_mul : m '' (s * t) = m '' s * m '' t := image_image2_distrib $ map_mul m

@[to_additive]
lemma preimage_mul_preimage_subset {s t : set β} : m ⁻¹' s * m ⁻¹' t ⊆ m ⁻¹' (s * t) :=
by { rintro _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (map_mul m _ _).symm ⟩ }

end has_mul

section group
variables [group α] [division_monoid β] [monoid_hom_class F α β] (m : F) {s t : set α}
include α β

@[to_additive] lemma image_div : m '' (s / t) = m '' s / m '' t := image_image2_distrib $ map_div m

@[to_additive]
lemma preimage_div_preimage_subset {s t : set β} : m ⁻¹' s / m ⁻¹' t ⊆ m ⁻¹' (s / t) :=
by { rintro _ ⟨_, _, _, _, rfl⟩, exact ⟨_, _, ‹_›, ‹_›, (map_div m _ _).symm ⟩ }

end group

open_locale pointwise

/-! ### Translation/scaling of sets -/

section smul
variables {s s₁ s₂ : set α} {t t₁ t₂ : set β} {a : α} {b : β}

@[to_additive]
lemma smul_set_inter [group α] [mul_action α β] {s t : set β} :
  a • (s ∩ t) = a • s ∩ a • t :=
(image_inter $ mul_action.injective a).symm

lemma smul_set_inter₀ [group_with_zero α] [mul_action α β] {s t : set β} (ha : a ≠ 0) :
  a • (s ∩ t) = a • s ∩ a • t :=
show units.mk0 a ha • _ = _, from smul_set_inter

@[simp, to_additive]
lemma smul_set_univ [group α] [mul_action α β] {a : α} : a • (univ : set β) = univ :=
eq_univ_of_forall $ λ b, ⟨a⁻¹ • b, trivial, smul_inv_smul _ _⟩

@[simp, to_additive]
lemma smul_univ [group α] [mul_action α β] {s : set α} (hs : s.nonempty) :
  s • (univ : set β) = univ :=
let ⟨a, ha⟩ := hs in eq_univ_of_forall $ λ b, ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul _ _⟩

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
variables [group_with_zero α] [mul_action α β] {s : set α} {a : α}

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

lemma smul_univ₀ (hs : ¬ s ⊆ 0) : s • (univ : set β) = univ :=
let ⟨a, ha, ha₀⟩ := not_subset.1 hs in eq_univ_of_forall $ λ b,
  ⟨a, a⁻¹ • b, ha, trivial, smul_inv_smul₀ ha₀ _⟩

lemma smul_set_univ₀ (ha : a ≠ 0) : a • (univ : set β) = univ :=
eq_univ_of_forall $ λ b, ⟨a⁻¹ • b, trivial, smul_inv_smul₀ ha _⟩

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
