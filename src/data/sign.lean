/-
Copyright (c) 2022 Eric Rodriguez. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Rodriguez
-/
import algebra.big_operators.order
import data.fintype.big_operators
import data.int.lemmas
import tactic.derive_fintype

/-!
# Sign function

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the sign function for types with zero and a decidable less-than relation, and
proves some basic theorems about it.
-/

/-- The type of signs. -/
@[derive [decidable_eq, inhabited, fintype]]
inductive sign_type
| zero | neg | pos

namespace sign_type

instance : has_zero sign_type := ⟨zero⟩
instance : has_one  sign_type := ⟨pos⟩

instance : has_neg sign_type :=
⟨λ s, match s with
| neg  := pos
| zero := zero
| pos  := neg
end⟩

@[simp] lemma zero_eq_zero   : zero = 0 := rfl
@[simp] lemma neg_eq_neg_one : neg = -1 := rfl
@[simp] lemma pos_eq_one     : pos = 1  := rfl

instance : has_mul sign_type :=
⟨λ x y, match x with
| neg  := -y
| zero := zero
| pos  := y
end⟩

/-- The less-than relation on signs. -/
inductive le : sign_type → sign_type → Prop
| of_neg (a) : le neg a
| zero       : le zero zero
| of_pos (a) : le a pos

instance : has_le sign_type := ⟨le⟩

instance : decidable_rel le :=
λ a b, by cases a; cases b; exact is_false (by rintro ⟨⟩) <|> exact is_true (by constructor)

/- We can define a `field` instance on `sign_type`, but it's not mathematically sensible,
so we only define the `comm_group_with_zero`. -/
instance : comm_group_with_zero sign_type :=
{ zero            := 0,
  one             := 1,
  mul             := (*),
  inv             := id,
  mul_zero        := λ a, by cases a; refl,
  zero_mul        := λ a, by cases a; refl,
  mul_one         := λ a, by cases a; refl,
  one_mul         := λ a, by cases a; refl,
  mul_inv_cancel  := λ a ha,  by cases a; trivial,
  mul_comm        := λ a b,   by casesm* _; refl,
  mul_assoc       := λ a b c, by casesm* _; refl,
  exists_pair_ne  := ⟨0, 1,   by rintro ⟨⟩⟩,
  inv_zero        := rfl }

instance : linear_order sign_type :=
{ le           := (≤),
  le_refl      := λ a, by cases a; constructor,
  le_total     := λ a b, by casesm* _; dec_trivial,
  le_antisymm  := λ a b ha hb, by casesm* _; refl,
  le_trans     := λ a b c hab hbc, by casesm* _; constructor,
  decidable_le := le.decidable_rel }

instance : bounded_order sign_type :=
{ top := 1,
  le_top := le.of_pos,
  bot := -1,
  bot_le := le.of_neg }

instance : has_distrib_neg sign_type :=
{ neg_neg := λ x, by cases x; refl,
  neg_mul := λ x y, by casesm* _; refl,
  mul_neg := λ x y, by casesm* _; refl,
..sign_type.has_neg }

/-- `sign_type` is equivalent to `fin 3`. -/
def fin3_equiv : sign_type ≃* fin 3 :=
{ to_fun :=  λ a, a.rec_on 0 (-1) 1,
  inv_fun := λ a, match a with
    | ⟨0, h⟩   := 0
    | ⟨1, h⟩   := 1
    | ⟨2, h⟩   := -1
    | ⟨n+3, h⟩ := (h.not_le le_add_self).elim
  end,
  left_inv :=  λ a, by cases a; refl,
  right_inv := λ a, match a with
    | ⟨0, h⟩   := rfl
    | ⟨1, h⟩   := rfl
    | ⟨2, h⟩   := rfl
    | ⟨n+3, h⟩ := (h.not_le le_add_self).elim
  end,
  map_mul' := λ x y, by casesm* _; refl }

section case_bashing

lemma nonneg_iff {a : sign_type} : 0 ≤ a ↔ a = 0 ∨ a = 1 := by dec_trivial!

lemma nonneg_iff_ne_neg_one {a : sign_type} : 0 ≤ a ↔ a ≠ -1 := by dec_trivial!

lemma neg_one_lt_iff {a : sign_type} : -1 < a ↔ 0 ≤ a := by dec_trivial!

lemma nonpos_iff {a : sign_type} : a ≤ 0 ↔ a = -1 ∨ a = 0 := by dec_trivial!

lemma nonpos_iff_ne_one {a : sign_type} : a ≤ 0 ↔ a ≠ 1 := by dec_trivial!

lemma lt_one_iff {a : sign_type} : a < 1 ↔ a ≤ 0 := by dec_trivial!

@[simp] lemma neg_iff {a : sign_type} : a < 0 ↔ a = -1 := by dec_trivial!

@[simp] lemma le_neg_one_iff {a : sign_type} : a ≤ -1 ↔ a = -1 := le_bot_iff

@[simp] lemma pos_iff {a : sign_type} : 0 < a ↔ a = 1 := by dec_trivial!

@[simp] lemma one_le_iff {a : sign_type} : 1 ≤ a ↔ a = 1 := top_le_iff

@[simp] lemma neg_one_le (a : sign_type) : -1 ≤ a := bot_le

@[simp] lemma le_one (a : sign_type) : a ≤ 1 := le_top

@[simp] lemma not_lt_neg_one (a : sign_type) : ¬ a < -1 := not_lt_bot

@[simp] lemma not_one_lt (a : sign_type) : ¬ 1 < a := not_top_lt

@[simp] lemma self_eq_neg_iff (a : sign_type) : a = -a ↔ a = 0 := by dec_trivial!

@[simp] lemma neg_eq_self_iff (a : sign_type) : -a = a ↔ a = 0 := by dec_trivial!

@[simp] lemma neg_one_lt_one : (-1 : sign_type) < 1 := bot_lt_top

end case_bashing

section cast

variables {α : Type*} [has_zero α] [has_one α] [has_neg α]

/-- Turn a `sign_type` into zero, one, or minus one. This is a coercion instance, but note it is
only a `has_coe_t` instance: see note [use has_coe_t]. -/
def cast : sign_type → α
| zero :=  0
| pos  :=  1
| neg  := -1

instance : has_coe_t sign_type α := ⟨cast⟩

@[simp] lemma cast_eq_coe (a : sign_type) : (cast a : α) = a := rfl

@[simp] lemma coe_zero : ↑(0 : sign_type) = (0 : α) := rfl
@[simp] lemma coe_one  : ↑(1 : sign_type) = (1 : α) := rfl
@[simp] lemma coe_neg_one : ↑(-1 : sign_type) = (-1 : α) := rfl

end cast

/-- `sign_type.cast` as a `mul_with_zero_hom`. -/
@[simps] def cast_hom {α} [mul_zero_one_class α] [has_distrib_neg α] : sign_type →*₀ α :=
{ to_fun    := cast,
  map_zero' := rfl,
  map_one'  := rfl,
  map_mul'  := λ x y, by cases x; cases y; simp }

lemma range_eq {α} (f : sign_type → α) : set.range f = {f zero, f neg, f pos} :=
begin
  classical,
  simpa only [← finset.coe_singleton, ← finset.image_singleton,
    ← fintype.coe_image_univ, finset.coe_image, ← set.image_insert_eq],
end

end sign_type

variables {α : Type*}

open sign_type

section preorder

variables [has_zero α] [preorder α] [decidable_rel ((<) : α → α → Prop)] {a : α}

/-- The sign of an element is 1 if it's positive, -1 if negative, 0 otherwise. -/
def sign : α →o sign_type :=
⟨λ a, if 0 < a then 1 else if a < 0 then -1 else 0,
 λ a b h, begin
  dsimp,
  split_ifs with h₁ h₂ h₃ h₄ _ _ h₂ h₃; try {constructor},
  { cases lt_irrefl 0 (h₁.trans $ h.trans_lt h₃) },
  { cases h₂ (h₁.trans_le h) },
  { cases h₄ (h.trans_lt h₃) }
  end⟩

lemma sign_apply : sign a = ite (0 < a) 1 (ite (a < 0) (-1) 0) := rfl

@[simp] lemma sign_zero : sign (0 : α) = 0 := by simp [sign_apply]
@[simp] lemma sign_pos (ha : 0 < a) : sign a = 1 := by rwa [sign_apply, if_pos]
@[simp] lemma sign_neg (ha : a < 0) : sign a = -1 := by rwa [sign_apply, if_neg $ asymm ha, if_pos]

lemma sign_eq_one_iff : sign a = 1 ↔ 0 < a :=
begin
  refine ⟨λ h, _, λ h, sign_pos h⟩,
  by_contra hn,
  rw [sign_apply, if_neg hn] at h,
  split_ifs at h;
    simpa using h
end

lemma sign_eq_neg_one_iff : sign a = -1 ↔ a < 0 :=
begin
  refine ⟨λ h, _, λ h, sign_neg h⟩,
  rw sign_apply at h,
  split_ifs at h,
  { simpa using h },
  { exact h_2 },
  { simpa using h }
end

end preorder

section linear_order

variables [has_zero α] [linear_order α] {a : α}

@[simp] lemma sign_eq_zero_iff : sign a = 0 ↔ a = 0 :=
begin
  refine ⟨λ h, _, λ h, h.symm ▸ sign_zero⟩,
  rw [sign_apply] at h,
  split_ifs at h; cases h,
  exact (le_of_not_lt h_1).eq_of_not_lt h_2
end

lemma sign_ne_zero : sign a ≠ 0 ↔ a ≠ 0 :=
sign_eq_zero_iff.not

@[simp] lemma sign_nonneg_iff : 0 ≤ sign a ↔ 0 ≤ a :=
begin
  rcases lt_trichotomy 0 a with (h|rfl|h),
  { simp [h, h.le] },
  { simp },
  { simpa [h, h.not_le] }
end

@[simp] lemma sign_nonpos_iff : sign a ≤ 0 ↔ a ≤ 0 :=
begin
  rcases lt_trichotomy 0 a with (h|rfl|h),
  { simp [h, h.not_le] },
  { simp },
  { simp [h, h.le] }
end

end linear_order

section ordered_semiring

variables [ordered_semiring α] [decidable_rel ((<) : α → α → Prop)] [nontrivial α]

@[simp] lemma sign_one : sign (1 : α) = 1 :=
sign_pos zero_lt_one

end ordered_semiring

section linear_ordered_ring

variables [linear_ordered_ring α] {a b : α}

/- I'm not sure why this is necessary, see https://leanprover.zulipchat.com/#narrow/stream/
113488-general/topic/type.20class.20inference.20issues/near/276937942 -/
local attribute [instance] linear_ordered_ring.decidable_lt

lemma sign_mul (x y : α) : sign (x * y) = sign x * sign y :=
begin
  rcases lt_trichotomy x 0 with hx | hx | hx; rcases lt_trichotomy y 0 with hy | hy | hy;
    simp only [sign_zero, mul_zero, zero_mul, sign_pos, sign_neg, hx, hy, mul_one, neg_one_mul,
               neg_neg, one_mul, mul_pos_of_neg_of_neg, mul_neg_of_neg_of_pos, neg_zero,
               mul_neg_of_pos_of_neg, mul_pos]
end

/-- `sign` as a `monoid_with_zero_hom` for a nontrivial ordered semiring. Note that linearity
is required; consider ℂ with the order `z ≤ w` iff they have the same imaginary part and
`z - w ≤ 0` in the reals; then `1 + i` and `1 - i` are incomparable to zero, and thus we have:
`0 * 0 = sign (1 + i) * sign (1 - i) ≠ sign 2 = 1`. (`complex.ordered_comm_ring`) -/
def sign_hom : α →*₀ sign_type :=
{ to_fun := sign,
  map_zero' := sign_zero,
  map_one' := sign_one,
  map_mul' := sign_mul }

lemma sign_pow (x : α) (n : ℕ) : sign (x ^ n) = (sign x) ^ n :=
begin
  change sign_hom (x ^ n) = (sign_hom x) ^ n,
  exact map_pow _ _ _
end

end linear_ordered_ring

section add_group

variables [add_group α] [preorder α] [decidable_rel ((<) : α → α → Prop)]

lemma left.sign_neg [covariant_class α α (+) (<)] (a : α) : sign (-a) = - sign a :=
begin
  simp_rw [sign_apply, left.neg_pos_iff, left.neg_neg_iff],
  split_ifs with h h',
  { exact false.elim (lt_asymm h h') },
  { simp },
  { simp },
  { simp }
end

lemma right.sign_neg [covariant_class α α (function.swap (+)) (<)] (a : α) : sign (-a) = - sign a :=
begin
  simp_rw [sign_apply, right.neg_pos_iff, right.neg_neg_iff],
  split_ifs with h h',
  { exact false.elim (lt_asymm h h') },
  { simp },
  { simp },
  { simp }
end

end add_group

section linear_ordered_add_comm_group

open_locale big_operators

variables [linear_ordered_add_comm_group α]

/- I'm not sure why this is necessary, see
https://leanprover.zulipchat.com/#narrow/stream/113488-general/topic/Decidable.20vs.20decidable_rel -/
local attribute [instance] linear_ordered_add_comm_group.decidable_lt

lemma sign_sum {ι : Type*} {s : finset ι} {f : ι → α} (hs : s.nonempty) (t : sign_type)
  (h : ∀ i ∈ s, sign (f i) = t) : sign (∑ i in s, f i) = t :=
begin
  cases t,
  { simp_rw [zero_eq_zero, sign_eq_zero_iff] at ⊢ h,
    exact finset.sum_eq_zero h },
  { simp_rw [neg_eq_neg_one, sign_eq_neg_one_iff] at ⊢ h,
    exact finset.sum_neg h hs },
  { simp_rw [pos_eq_one, sign_eq_one_iff] at ⊢ h,
    exact finset.sum_pos h hs }
end

end linear_ordered_add_comm_group

namespace int

lemma sign_eq_sign (n : ℤ) : n.sign = _root_.sign n :=
begin
  obtain ((_ | _) | _) := n,
  { exact congr_arg coe sign_zero.symm },
  { exact congr_arg coe (sign_pos $ int.succ_coe_nat_pos _).symm },
  { exact congr_arg coe (_root_.sign_neg $ neg_succ_lt_zero _).symm }
end
end int

open finset nat
open_locale big_operators

private lemma exists_signed_sum_aux [decidable_eq α] (s : finset α) (f : α → ℤ) :
  ∃ (β : Type u_1) (t : finset β) (sgn : β → sign_type) (g : β → α), (∀ b, g b ∈ s) ∧
    t.card = ∑ a in s, (f a).nat_abs ∧
    ∀ a ∈ s, (∑ b in t, if g b = a then (sgn b : ℤ) else 0) = f a :=
begin
  refine ⟨Σ a : {x // x ∈ s}, ℕ, finset.univ.sigma (λ a, range (f a).nat_abs), λ a, sign (f a.1),
    λ a, a.1, λ a, a.1.prop, _, _⟩,
  { simp [@sum_attach _ _ _ _ (λ a, (f a).nat_abs)] },
  { intros x hx,
    simp [sum_sigma, hx, ← int.sign_eq_sign, int.sign_mul_abs, mul_comm (|f _|),
      @sum_attach _ _ _ _ (λ a, ∑ j in range (f a).nat_abs, if a = x then (f a).sign else 0)] }
end

/-- We can decompose a sum of absolute value `n` into a sum of `n` signs. -/
lemma exists_signed_sum [decidable_eq α] (s : finset α) (f : α → ℤ) :
  ∃ (β : Type u_1) (_ : fintype β) (sgn : β → sign_type) (g : β → α), by exactI (∀ b, g b ∈ s) ∧
    fintype.card β = ∑ a in s, (f a).nat_abs ∧
    ∀ a ∈ s, (∑ b, if g b = a then (sgn b : ℤ) else 0) = f a :=
let ⟨β, t, sgn, g, hg, ht, hf⟩ := exists_signed_sum_aux s f in
  ⟨t, infer_instance, λ b, sgn b, λ b, g b, λ b, hg b, by simp [ht], λ a ha,
    (@sum_attach _ _ t _ (λ b, ite (g b = a) (sgn b : ℤ) 0)).trans $ hf _ ha⟩

/-- We can decompose a sum of absolute value less than `n` into a sum of at most `n` signs. -/
lemma exists_signed_sum' [nonempty α] [decidable_eq α] (s : finset α) (f : α → ℤ) (n : ℕ)
  (h : ∑ i in s, (f i).nat_abs ≤ n) :
  ∃ (β : Type u_1) (_ : fintype β) (sgn : β → sign_type) (g : β → α), by exactI
    (∀ b, g b ∉ s → sgn b = 0) ∧ fintype.card β = n ∧
    ∀ a ∈ s, (∑ i, if g i = a then (sgn i : ℤ) else 0) = f a :=
begin
  obtain ⟨β, _, sgn, g, hg, hβ, hf⟩ := exists_signed_sum s f,
  resetI,
  refine ⟨β ⊕ fin (n - ∑ i in s, (f i).nat_abs), infer_instance, sum.elim sgn 0,
    sum.elim g $ classical.arbitrary _, _, by simp [hβ, h], λ a ha, by simp [hf _ ha]⟩,
  rintro (b | b) hb,
  { cases hb (hg _) },
  { refl }
end
