/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import algebra.big_operators.order
import algebra.group.prod
import data.option.n_ary
import data.set.pointwise.basic
import order.interval
import tactic.positivity

/-!
# Interval arithmetic

This file defines arithmetic operations on intervals and prove their correctness. Note that this is
full precision operations. The essentials of float operations can be found
in `data.fp.basic`. We hsve not yet integrated these with the rest of the library.
-/

open function set
open_locale big_operators pointwise

universe u
variables {ι α : Type*}

/-! ### One/zero -/

section one
section preorder
variables [preorder α] [has_one α]

@[to_additive] instance : has_one (nonempty_interval α) := ⟨nonempty_interval.pure 1⟩
@[to_additive] instance : has_one (interval α) := ⟨interval.pure 1⟩

namespace nonempty_interval

@[simp, to_additive to_prod_zero] lemma to_prod_one : (1 : nonempty_interval α).to_prod = 1 := rfl
@[to_additive] lemma fst_one : (1 : nonempty_interval α).fst = 1 := rfl
@[to_additive] lemma snd_one : (1 : nonempty_interval α).snd = 1 := rfl
@[simp, norm_cast, to_additive]
lemma coe_one_interval : ((1 : nonempty_interval α) : interval α) = 1 := rfl
@[simp, to_additive] lemma pure_one : pure (1 : α) = 1 := rfl

end nonempty_interval

namespace interval

@[simp, to_additive] lemma pure_one : pure (1 : α) = 1 := rfl
@[simp, to_additive] lemma one_ne_bot : (1 : interval α) ≠ ⊥ := pure_ne_bot
@[simp, to_additive] lemma bot_ne_one : (⊥ : interval α) ≠ 1 := bot_ne_pure

end interval
end preorder

section partial_order
variables [partial_order α] [has_one α]

namespace nonempty_interval

@[simp, to_additive] lemma coe_one : ((1 : nonempty_interval α) : set α) = 1 := coe_pure _
@[to_additive] lemma one_mem_one : (1 : α) ∈ (1 : nonempty_interval α) := ⟨le_rfl, le_rfl⟩

end nonempty_interval

namespace interval

@[simp, to_additive] lemma coe_one : ((1 : interval α) : set α) = 1 := Icc_self _
@[to_additive] lemma one_mem_one : (1 : α) ∈ (1 : interval α) := ⟨le_rfl, le_rfl⟩

end interval
end partial_order
end one

/-!
### Addition/multiplication

Note that this multiplication does not apply to `ℚ` or `ℝ`.
-/

section mul
variables [preorder α] [has_mul α] [covariant_class α α (*) (≤)]
  [covariant_class α α (swap (*)) (≤)]

@[to_additive] instance : has_mul (nonempty_interval α) :=
⟨λ s t, ⟨s.to_prod * t.to_prod, mul_le_mul' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive] instance : has_mul (interval α) := ⟨option.map₂ (*)⟩

namespace nonempty_interval
variables (s t : nonempty_interval α) (a b : α)

@[simp, to_additive to_prod_add] lemma to_prod_mul : (s * t).to_prod = s.to_prod * t.to_prod := rfl
@[to_additive] lemma fst_mul : (s * t).fst = s.fst * t.fst := rfl
@[to_additive] lemma snd_mul : (s * t).snd = s.snd * t.snd := rfl
@[simp, to_additive] lemma coe_mul_interval : (↑(s * t) : interval α) = s * t := rfl
@[simp, to_additive] lemma pure_mul_pure : pure a * pure b = pure (a * b) := rfl

end nonempty_interval

namespace interval
variables (s t : interval α)

@[simp, to_additive] lemma bot_mul : ⊥ * t = ⊥ := rfl
@[simp, to_additive] lemma mul_bot : s * ⊥ = ⊥ := option.map₂_none_right _ _

end interval
end mul

/-! ### Powers -/

-- TODO: if `to_additive` gets improved sufficiently, derive this from `has_pow`
instance nonempty_interval.has_nsmul [add_monoid α] [preorder α] [covariant_class α α (+) (≤)]
  [covariant_class α α (swap (+)) (≤)] : has_smul ℕ (nonempty_interval α) :=
⟨λ n s, ⟨(n • s.fst, n • s.snd), nsmul_le_nsmul_of_le_right s.fst_le_snd _⟩⟩

section pow
variables [monoid α] [preorder α] [covariant_class α α (*) (≤)] [covariant_class α α (swap (*)) (≤)]

@[to_additive nonempty_interval.has_nsmul]
instance nonempty_interval.has_pow : has_pow (nonempty_interval α) ℕ :=
⟨λ s n, ⟨s.to_prod ^ n, pow_le_pow_of_le_left' s.fst_le_snd _⟩⟩

namespace nonempty_interval
variables (s : nonempty_interval α) (a : α) (n : ℕ)

@[simp, to_additive to_prod_nsmul] lemma to_prod_pow : (s ^ n).to_prod = s.to_prod ^ n := rfl
@[to_additive] lemma fst_pow : (s ^ n).fst = s.fst ^ n := rfl
@[to_additive] lemma snd_pow : (s ^ n).snd = s.snd ^ n := rfl
@[simp, to_additive] lemma pure_pow : pure a ^ n = pure (a ^ n) := rfl

end nonempty_interval
end pow

namespace nonempty_interval

@[to_additive]
instance [ordered_comm_monoid α] : comm_monoid (nonempty_interval α) :=
nonempty_interval.to_prod_injective.comm_monoid _ to_prod_one to_prod_mul to_prod_pow

end nonempty_interval

@[to_additive]
instance [ordered_comm_monoid α] : mul_one_class (interval α) :=
{ mul := (*),
  one := 1,
  one_mul := λ s, (option.map₂_coe_left _ _ _).trans $
    by simp only [nonempty_interval.pure_one, one_mul, ←id_def, option.map_id, id],
  mul_one := λ s, (option.map₂_coe_right _ _ _).trans $
    by simp only [nonempty_interval.pure_one, mul_one, ←id_def, option.map_id, id] }

@[to_additive]
instance [ordered_comm_monoid α] : comm_monoid (interval α) :=
{ mul_comm := λ _ _, option.map₂_comm mul_comm,
  mul_assoc := λ _ _ _, option.map₂_assoc mul_assoc,
  ..interval.mul_one_class }

namespace nonempty_interval

@[simp, to_additive] lemma coe_pow_interval [ordered_comm_monoid α] (s : nonempty_interval α)
  (n : ℕ) :
  (↑(s ^ n) : interval α) = s ^ n :=
map_pow (⟨coe, coe_one_interval, coe_mul_interval⟩ : nonempty_interval α →* interval α) _ _

end nonempty_interval

namespace interval
variables [ordered_comm_monoid α] (s : interval α) {n : ℕ}

@[to_additive] lemma bot_pow : ∀ {n : ℕ} (hn : n ≠ 0), (⊥ : interval α) ^ n = ⊥
| 0 h := (h rfl).elim
| (nat.succ n) _ := bot_mul (⊥ ^ n)

end interval

/-!
### Subtraction

Subtraction is defined more generally than division so that it applies to `ℕ` (and `has_ordered_div`
is not a thing and probably should not become one).
-/

section sub
variables [preorder α] [add_comm_semigroup α] [has_sub α] [has_ordered_sub α]
  [covariant_class α α (+) (≤)]

instance : has_sub (nonempty_interval α) :=
⟨λ s t, ⟨(s.fst - t.snd, s.snd - t.fst), tsub_le_tsub s.fst_le_snd t.fst_le_snd⟩⟩

instance : has_sub (interval α) := ⟨option.map₂ has_sub.sub⟩

namespace nonempty_interval
variables (s t : nonempty_interval α) {a b : α}

@[simp] lemma fst_sub : (s - t).fst = s.fst - t.snd := rfl
@[simp] lemma snd_sub : (s - t).snd = s.snd - t.fst := rfl
@[simp] lemma coe_sub_interval : (↑(s - t) : interval α) = s - t := rfl
lemma sub_mem_sub (ha : a ∈ s) (hb : b ∈ t) : a - b ∈ s - t :=
⟨tsub_le_tsub ha.1 hb.2, tsub_le_tsub ha.2 hb.1⟩
@[simp] lemma pure_sub_pure (a b : α) : pure a - pure b = pure (a - b) := rfl

end nonempty_interval

namespace interval
variables (s t : interval α)

@[simp] lemma bot_sub : ⊥ - t = ⊥ := rfl
@[simp] lemma sub_bot : s - ⊥ = ⊥ := option.map₂_none_right _ _

end interval
end sub

/-!
### Division in ordered groups

Note that this division does not apply to `ℚ` or `ℝ`.
-/

section div
variables [preorder α] [comm_group α] [covariant_class α α (*) (≤)]

@[to_additive] instance : has_div (nonempty_interval α) :=
⟨λ s t, ⟨(s.fst / t.snd, s.snd / t.fst), div_le_div'' s.fst_le_snd t.fst_le_snd⟩⟩

@[to_additive] instance : has_div (interval α) := ⟨option.map₂ (/)⟩

namespace nonempty_interval
variables (s t : nonempty_interval α) (a b : α)

@[simp, to_additive] lemma fst_div : (s / t).fst = s.fst / t.snd := rfl
@[simp, to_additive] lemma snd_div : (s / t).snd = s.snd / t.fst := rfl
@[simp, to_additive] lemma coe_div_interval : (↑(s / t) : interval α) = s / t := rfl
@[to_additive] lemma div_mem_div (ha : a ∈ s) (hb : b ∈ t) : a / b ∈ s / t :=
⟨div_le_div'' ha.1 hb.2, div_le_div'' ha.2 hb.1⟩
@[simp, to_additive] lemma pure_div_pure : pure a / pure b = pure (a / b) := rfl

end nonempty_interval

namespace interval
variables (s t : interval α)

@[simp, to_additive] lemma bot_div : ⊥ / t = ⊥ := rfl
@[simp, to_additive] lemma div_bot : s / ⊥ = ⊥ := option.map₂_none_right _ _

end interval
end div

/-! ### Negation/inversion -/

section inv
variables [ordered_comm_group α]

@[to_additive] instance : has_inv (nonempty_interval α) :=
⟨λ s, ⟨(s.snd⁻¹, s.fst⁻¹), inv_le_inv' s.fst_le_snd⟩⟩

@[to_additive] instance : has_inv (interval α) := ⟨option.map has_inv.inv⟩

namespace nonempty_interval
variables (s t : nonempty_interval α) (a : α)

@[simp, to_additive] lemma fst_inv : s⁻¹.fst = s.snd⁻¹ := rfl
@[simp, to_additive] lemma snd_inv : s⁻¹.snd = s.fst⁻¹ := rfl
@[simp, to_additive] lemma coe_inv_interval : (↑(s⁻¹) : interval α) = s⁻¹ := rfl
@[to_additive] lemma inv_mem_inv (ha : a ∈ s) : a⁻¹ ∈ s⁻¹ := ⟨inv_le_inv' ha.2, inv_le_inv' ha.1⟩
@[simp, to_additive] lemma inv_pure : (pure a)⁻¹ = pure a⁻¹ := rfl

end nonempty_interval

@[simp, to_additive] lemma interval.inv_bot : (⊥ : interval α)⁻¹ = ⊥ := rfl

end inv

namespace nonempty_interval
variables [ordered_comm_group α] {s t : nonempty_interval α}

@[to_additive] protected lemma mul_eq_one_iff :
  s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 :=
begin
  refine ⟨λ h, _, _⟩,
  { rw [ext_iff, prod.ext_iff] at h,
    have := (mul_le_mul_iff_of_ge s.fst_le_snd t.fst_le_snd).1 (h.2.trans h.1.symm).le,
    refine ⟨s.fst, t.fst, _, _, h.1⟩; ext; try { refl },
    exacts [this.1.symm, this.2.symm] },
  { rintro ⟨b, c, rfl, rfl, h⟩,
    rw [pure_mul_pure, h, pure_one] }
end

instance {α : Type u} [ordered_add_comm_group α] : subtraction_comm_monoid (nonempty_interval α) :=
{ neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := λ s t, by ext; exact sub_eq_add_neg _ _,
  neg_neg := λ s, by ext; exact neg_neg _,
  neg_add_rev := λ s t, by ext; exact neg_add_rev _ _,
  neg_eq_of_add := λ s t h, begin
    obtain ⟨a, b, rfl, rfl, hab⟩ := nonempty_interval.add_eq_zero_iff.1 h,
    rw [neg_pure, neg_eq_of_add_eq_zero_right hab],
  end,
  ..nonempty_interval.add_comm_monoid }

@[to_additive nonempty_interval.subtraction_comm_monoid]
instance : division_comm_monoid (nonempty_interval α) :=
{ inv := has_inv.inv,
  div := (/),
  div_eq_mul_inv := λ s t, by ext; exact div_eq_mul_inv _ _,
  inv_inv := λ s, by ext; exact inv_inv _,
  mul_inv_rev := λ s t, by ext; exact mul_inv_rev _ _,
  inv_eq_of_mul := λ s t h, begin
    obtain ⟨a, b, rfl, rfl, hab⟩ := nonempty_interval.mul_eq_one_iff.1 h,
    rw [inv_pure, inv_eq_of_mul_eq_one_right hab],
  end,
  ..nonempty_interval.comm_monoid }

end nonempty_interval

namespace interval
variables [ordered_comm_group α] {s t : interval α}

@[to_additive] protected lemma mul_eq_one_iff :
  s * t = 1 ↔ ∃ a b, s = pure a ∧ t = pure b ∧ a * b = 1 :=
begin
  cases s,
  { simp [with_bot.none_eq_bot] },
  cases t,
  { simp [with_bot.none_eq_bot] },
  { simp [with_bot.some_eq_coe, ←nonempty_interval.coe_mul_interval,
    nonempty_interval.mul_eq_one_iff] }
end

instance {α : Type u} [ordered_add_comm_group α] : subtraction_comm_monoid (interval α) :=
{ neg := has_neg.neg,
  sub := has_sub.sub,
  sub_eq_add_neg := by rintro (_ | s) (_ | t); refl <|> exact congr_arg some (sub_eq_add_neg _ _),
  neg_neg := by rintro (_ | s); refl <|> exact congr_arg some (neg_neg _),
  neg_add_rev := by rintro (_ | s) (_ | t); refl <|> exact congr_arg some (neg_add_rev _ _),
  neg_eq_of_add := by rintro (_ | s) (_ | t) h;
    cases h <|> exact congr_arg some (neg_eq_of_add_eq_zero_right $ option.some_injective _ h),
  ..interval.add_comm_monoid }

@[to_additive interval.subtraction_comm_monoid]
instance : division_comm_monoid (interval α) :=
{ inv := has_inv.inv,
  div := (/),
  div_eq_mul_inv := by rintro (_ | s) (_ | t); refl <|> exact congr_arg some (div_eq_mul_inv _ _),
  inv_inv := by rintro (_ | s); refl <|> exact congr_arg some (inv_inv _),
  mul_inv_rev := by rintro (_ | s) (_ | t); refl <|> exact congr_arg some (mul_inv_rev _ _),
  inv_eq_of_mul := by rintro (_ | s) (_ | t) h;
    cases h <|> exact congr_arg some (inv_eq_of_mul_eq_one_right $ option.some_injective _ h),
  ..interval.comm_monoid }

end interval

section length
variables [ordered_add_comm_group α]

namespace nonempty_interval
variables (s t : nonempty_interval α) (a : α)

/-- The length of an interval is its first component minus its second component. This measures the
accuracy of the approximation by an interval. -/
def length : α := s.snd - s.fst

@[simp] lemma length_nonneg : 0 ≤ s.length := sub_nonneg_of_le s.fst_le_snd
@[simp] lemma length_pure : (pure a).length = 0 := sub_self _
@[simp] lemma length_zero : (0 : nonempty_interval α).length = 0 := length_pure _
@[simp] lemma length_neg : (-s).length = s.length := neg_sub_neg _ _
@[simp] lemma length_add : (s + t).length = s.length + t.length := add_sub_add_comm _ _ _ _
@[simp] lemma length_sub : (s - t).length = s.length + t.length := by simp [sub_eq_add_neg]

@[simp] lemma length_sum (f : ι → nonempty_interval α) (s : finset ι) :
  (∑ i in s, f i).length = ∑ i in s, (f i).length :=
map_sum (⟨length, length_zero, length_add⟩ : nonempty_interval α →+ α) _ _

end nonempty_interval

namespace interval
variables (s t : interval α) (a : α)

/-- The length of an interval is its first component minus its second component. This measures the
accuracy of the approximation by an interval. -/
def length : interval α → α
| ⊥ := 0
| (s : nonempty_interval α) := s.length

@[simp] lemma length_nonneg : ∀ s : interval α, 0 ≤ s.length
| ⊥ := le_rfl
| (s : nonempty_interval α) := s.length_nonneg
@[simp] lemma length_pure : (pure a).length = 0 := nonempty_interval.length_pure _
@[simp] lemma length_zero : (0 : interval α).length = 0 := length_pure _
@[simp] lemma length_neg :  ∀ s : interval α, (-s).length = s.length
| ⊥ := rfl
| (s : nonempty_interval α) := s.length_neg
lemma length_add_le : ∀ s t : interval α, (s + t).length ≤ s.length + t.length
| ⊥ _ := by simp
| _ ⊥ := by simp
| (s : nonempty_interval α) (t : nonempty_interval α) := (s.length_add t).le
lemma length_sub_le : (s - t).length ≤ s.length + t.length :=
by simpa [sub_eq_add_neg] using length_add_le s (-t)

lemma length_sum_le (f : ι → interval α) (s : finset ι) :
  (∑ i in s, f i).length ≤ ∑ i in s, (f i).length :=
finset.le_sum_of_subadditive _ length_zero length_add_le _ _

end interval
end length

namespace tactic
open positivity

/-- Extension for the `positivity` tactic: The length of an interval is always nonnegative. -/
@[positivity]
meta def positivity_interval_length : expr → tactic strictness
| `(nonempty_interval.length %%s) := nonnegative <$> mk_app `nonempty_interval.length_nonneg [s]
| `(interval.length %%s) := nonnegative <$> mk_app `interval.length_nonneg [s]
| e := pp e >>= fail ∘ format.bracket "The expression `"
         "` isn't of the form `nonempty_interval.length s` or `interval.length s`"

end tactic
