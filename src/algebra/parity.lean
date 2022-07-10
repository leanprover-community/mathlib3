/-
Copyright (c) 2022 Damiano Testa. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Damiano Testa
-/

import algebra.ring.basic
import algebra.algebra.basic
import algebra.group_power.basic
import algebra.field_power
import algebra.opposites

/-!  # Squares, even and odd elements

This file proves some general facts about squares, even and odd elements of semirings.

In the implementation, we define `is_square` and we let `even` be the notion transported by
`to_additive`.  The definition are therefore as follows:
```lean
is_square a ↔ ∃ r, a = r * r
even a ↔ ∃ r, a = r + r
```

Odd elements are not unified with a multiplicative notion.

## Future work

* TODO: Try to generalize further the typeclass assumptions on `is_square/even`.
  For instance, in some cases, there are `semiring` assumptions that I (DT) am not convinced are
  necessary.
* TODO: Consider moving the definition and lemmas about `odd` to a separate file.
* TODO: The "old" definition of `even a` asked for the existence of an element `c` such that
  `a = 2 * c`.  For this reason, several fixes introduce an extra `two_mul` or `← two_mul`.
  It might be the case that by making a careful choice of `simp` lemma, this can be avoided.
 -/

open mul_opposite
variables {F α β R : Type*}

section has_mul
variables [has_mul α]

/--  An element `a` of a type `α` with multiplication satisfies `square a` if `a = r * r`,
for some `r : α`. -/
@[to_additive
"An element `a` of a type `α` with addition satisfies `even a` if `a = r + r`,
for some `r : α`."]
def is_square (a : α) : Prop := ∃ r, a = r * r

@[simp, to_additive] lemma is_square_mul_self (m : α) : is_square (m * m) := ⟨m, rfl⟩

@[to_additive] lemma is_square_op_iff (a : α) : is_square (op a) ↔ is_square a :=
⟨λ ⟨c, hc⟩, ⟨unop c, by rw [← unop_mul, ← hc, unop_op]⟩, λ ⟨c, hc⟩, by simp [hc]⟩

/-- Create a decidability instance for `is_square` on `fintype`s. -/
instance is_square_decidable [fintype α] [decidable_eq α] : decidable_pred (is_square : α → Prop) :=
λ a, fintype.decidable_exists_fintype

end has_mul

@[simp, to_additive]
lemma is_square_one [mul_one_class α] : is_square (1 : α) := ⟨1, (mul_one _).symm⟩

@[to_additive]
lemma is_square.map [mul_one_class α] [mul_one_class β] [monoid_hom_class F α β] {m : α} (f : F) :
  is_square m → is_square (f m) :=
by { rintro ⟨m, rfl⟩, exact ⟨f m, by simp⟩ }

section monoid
variables [monoid α]

@[to_additive even_iff_exists_two_nsmul]
lemma is_square_iff_exists_sq (m : α) : is_square m ↔ ∃ c, m = c ^ 2 :=
by simp [is_square, pow_two]

alias is_square_iff_exists_sq ↔ is_square.exists_sq is_square_of_exists_sq

attribute [to_additive even.exists_two_nsmul "Alias of the forwards direction of
`even_iff_exists_two_nsmul`."] is_square.exists_sq

attribute [to_additive even_of_exists_two_nsmul "Alias of the backwards direction of
`even_iff_exists_two_nsmul`."] is_square_of_exists_sq

@[simp, to_additive even_two_nsmul]
lemma is_square_sq (a : α) : is_square (a ^ 2) := ⟨a, pow_two _⟩

variables [has_distrib_neg α] {n : ℕ}

lemma even.neg_pow : even n → ∀ a : α, (-a) ^ n = a ^ n :=
by { rintro ⟨c, rfl⟩ a, simp_rw [←two_mul, pow_mul, neg_sq] }

lemma even.neg_one_pow (h : even n) : (-1 : α) ^ n = 1 := by rw [h.neg_pow, one_pow]

end monoid

/-- `0` is always a square (in a monoid with zero). -/
lemma is_square_zero (M : Type*) [monoid_with_zero M] : is_square (0 : M) :=
by { use 0, simp only [mul_zero] }

@[to_additive] lemma is_square.mul [comm_semigroup α] {a b : α} :
  is_square a → is_square b → is_square (a * b) :=
by { rintro ⟨a, rfl⟩ ⟨b, rfl⟩, exact ⟨a * b, mul_mul_mul_comm _ _ _ _⟩ }

section division_monoid
variables [division_monoid α] {a : α}

@[simp, to_additive] lemma is_square_inv : is_square a⁻¹ ↔ is_square a :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rw [← is_square_op_iff, ← inv_inv a],
    exact h.map (mul_equiv.inv' α) },
  { exact ((is_square_op_iff a).mpr h).map (mul_equiv.inv' α).symm }
end

alias is_square_inv ↔ _ is_square.inv

attribute [to_additive] is_square.inv

variables [has_distrib_neg α] {n : ℤ}

lemma even.neg_zpow : even n → ∀ a : α, (-a) ^ n = a ^ n :=
by { rintro ⟨c, rfl⟩ a, exact zpow_bit0_neg _ _ }

lemma even.neg_one_zpow (h : even n) : (-1 : α) ^ n = 1 := by rw [h.neg_zpow, one_zpow]

end division_monoid

lemma even_abs [subtraction_monoid α] [linear_order α] {a : α} : even (|a|) ↔ even a :=
by cases abs_choice a; simp only [h, even_neg]

@[to_additive]
lemma is_square.div [division_comm_monoid α] {a b : α} (ha : is_square a) (hb : is_square b) :
  is_square (a / b) :=
by { rw div_eq_mul_inv, exact ha.mul hb.inv }

-- `odd.tsub` requires `canonically_linear_ordered_semiring`, which we don't have
lemma even.tsub [canonically_linear_ordered_add_monoid α] [has_sub α] [has_ordered_sub α]
  [contravariant_class α α (+) (≤)] {m n : α} (hm : even m) (hn : even n) : even (m - n) :=
begin
  obtain ⟨a, rfl⟩ := hm,
  obtain ⟨b, rfl⟩ := hn,
  refine ⟨a - b, _⟩,
  obtain h | h := le_total a b,
  { rw [tsub_eq_zero_of_le h, tsub_eq_zero_of_le (add_le_add h h), add_zero] },
  { exact (tsub_add_tsub_comm h h).symm }
end

lemma even_iff_exists_bit0 [has_add α] {a : α} : even a ↔ ∃ b, a = bit0 b := iff.rfl

alias even_iff_exists_bit0 ↔ even.exists_bit0 _

section semiring
variables [semiring α] [semiring β] {m n : α}

lemma even_iff_exists_two_mul (m : α) : even m ↔ ∃ c, m = 2 * c :=
by simp [even_iff_exists_two_nsmul]

lemma even_iff_two_dvd {a : α} : even a ↔ 2 ∣ a := by simp [even, has_dvd.dvd, two_mul]

@[simp] lemma range_two_mul (α : Type*) [semiring α] :
  set.range (λ x : α, 2 * x) = {a | even a} :=
by { ext x, simp [eq_comm, two_mul, even] }

@[simp] lemma even_bit0 (a : α) : even (bit0 a) :=
⟨a, rfl⟩

@[simp] lemma even_two : even (2 : α) := ⟨1, rfl⟩

@[simp] lemma even.mul_left (hm : even m) (n) : even (n * m) :=
hm.map (add_monoid_hom.mul_left n)

@[simp] lemma even.mul_right (hm : even m) (n) : even (m * n) :=
hm.map (add_monoid_hom.mul_right n)

lemma even_two_mul (m : α) : even (2 * m) := ⟨m, two_mul _⟩

lemma even.pow_of_ne_zero (hm : even m) : ∀ {a : ℕ}, a ≠ 0 → even (m ^ a)
| 0       a0 := (a0 rfl).elim
| (a + 1) _  := by { rw pow_succ, exact hm.mul_right _ }

section with_odd

/-- An element `a` of a semiring is odd if there exists `k` such `a = 2*k + 1`. -/
def odd (a : α) : Prop := ∃ k, a = 2*k + 1

lemma odd_iff_exists_bit1 {a : α} : odd a ↔ ∃ b, a = bit1 b :=
exists_congr $ λ b, by { rw two_mul, refl }

alias odd_iff_exists_bit1 ↔ odd.exists_bit1 _

@[simp] lemma odd_bit1 (a : α) : odd (bit1 a) := odd_iff_exists_bit1.2 ⟨a, rfl⟩

@[simp] lemma range_two_mul_add_one (α : Type*) [semiring α] :
  set.range (λ x : α, 2 * x + 1) = {a | odd a} :=
by { ext x, simp [odd, eq_comm] }

lemma even.add_odd : even m → odd n → odd (m + n) :=
by { rintro ⟨m, rfl⟩ ⟨n, rfl⟩, exact ⟨m + n, by rw [mul_add, ← two_mul, add_assoc]⟩ }

lemma odd.add_even (hm : odd m) (hn : even n) : odd (m + n) :=
by { rw add_comm, exact hn.add_odd hm }

lemma odd.add_odd : odd m → odd n → even (m + n) :=
begin
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩,
  refine ⟨n + m + 1, _⟩,
  rw [← two_mul, ←add_assoc, add_comm _ (2 * n), ←add_assoc, ←mul_add, add_assoc, mul_add _ (n + m),
    mul_one],
  refl
end

@[simp] lemma odd_one : odd (1 : α) :=
⟨0, (zero_add _).symm.trans (congr_arg (+ (1 : α)) (mul_zero _).symm)⟩

@[simp] lemma odd_two_mul_add_one (m : α) : odd (2 * m + 1) := ⟨m, rfl⟩

lemma odd.map [ring_hom_class F α β] (f : F) : odd m → odd (f m) :=
by { rintro ⟨m, rfl⟩, exact ⟨f m, by simp [two_mul]⟩ }

@[simp] lemma odd.mul : odd m → odd n → odd (m * n) :=
begin
  rintro ⟨m, rfl⟩ ⟨n, rfl⟩,
  refine ⟨2 * m * n + n + m, _⟩,
  rw [mul_add, add_mul, mul_one, ← add_assoc, one_mul, mul_assoc, ← mul_add, ← mul_add, ← mul_assoc,
    ← nat.cast_two, ← nat.cast_comm],
end

lemma odd.pow (hm : odd m) : ∀ {a : ℕ}, odd (m ^ a)
| 0       := by { rw pow_zero, exact odd_one }
| (a + 1) := by { rw pow_succ, exact hm.mul odd.pow }

end with_odd
end semiring

section monoid
variables [monoid α] [has_distrib_neg α] {a : α} {n : ℕ}

lemma odd.neg_pow : odd n → ∀ a : α, (-a) ^ n = - a ^ n :=
by { rintro ⟨c, rfl⟩ a, simp_rw [pow_add, pow_mul, neg_sq, pow_one, mul_neg] }
lemma odd.neg_one_pow (h : odd n) : (-1 : α) ^ n = -1 := by rw [h.neg_pow, one_pow]

end monoid

section ring
variables [ring α] {a b : α} {n : ℕ}

@[simp] lemma even_neg_two : even (- 2 : α) := by simp only [even_neg, even_two]

lemma odd.neg (hp : odd a) : odd (-a) :=
begin
  obtain ⟨k, hk⟩ := hp,
  use -(k + 1),
  rw [mul_neg, mul_add, neg_add, add_assoc, two_mul (1 : α), neg_add,
    neg_add_cancel_right, ←neg_add, hk],
end

@[simp] lemma odd_neg : odd (-a) ↔ odd a := ⟨λ h, neg_neg a ▸ h.neg, odd.neg⟩

@[simp] lemma odd_neg_one : odd (- 1 : α) := by simp

lemma odd.sub_even (ha : odd a) (hb : even b) : odd (a - b) :=
by { rw sub_eq_add_neg, exact ha.add_even hb.neg }

lemma even.sub_odd (ha : even a) (hb : odd b) : odd (a - b) :=
by { rw sub_eq_add_neg, exact ha.add_odd hb.neg }

lemma odd.sub_odd (ha : odd a) (hb : odd b) : even (a - b) :=
by { rw sub_eq_add_neg, exact ha.add_odd hb.neg }

lemma odd_abs [linear_order α] : odd (abs a) ↔ odd a :=
by cases abs_choice a with h h; simp only [h, odd_neg]

end ring

section powers
variables [linear_ordered_ring R] {a : R} {n : ℕ}

lemma even.pow_nonneg (hn : even n) (a : R) : 0 ≤ a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using pow_bit0_nonneg a k

lemma even.pow_pos (hn : even n) (ha : a ≠ 0) : 0 < a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using pow_bit0_pos ha k

lemma odd.pow_nonpos (hn : odd n) (ha : a ≤ 0) : a ^ n ≤ 0:=
by cases hn with k hk; simpa only [hk, two_mul] using pow_bit1_nonpos_iff.mpr ha

lemma odd.pow_neg (hn : odd n) (ha : a < 0) : a ^ n < 0:=
by cases hn with k hk; simpa only [hk, two_mul] using pow_bit1_neg_iff.mpr ha

lemma odd.pow_nonneg_iff (hn : odd n) : 0 ≤ a ^ n ↔ 0 ≤ a :=
⟨λ h, le_of_not_lt (λ ha, h.not_lt $ hn.pow_neg ha), λ ha, pow_nonneg ha n⟩

lemma odd.pow_nonpos_iff (hn : odd n) : a ^ n ≤ 0 ↔ a ≤ 0 :=
⟨λ h, le_of_not_lt (λ ha, h.not_lt $ pow_pos ha _), hn.pow_nonpos⟩

lemma odd.pow_pos_iff (hn : odd n) : 0 < a ^ n ↔ 0 < a :=
⟨λ h, lt_of_not_le (λ ha, h.not_le $ hn.pow_nonpos ha), λ ha, pow_pos ha n⟩

lemma odd.pow_neg_iff (hn : odd n) : a ^ n < 0 ↔ a < 0 :=
⟨λ h, lt_of_not_le (λ ha, h.not_le $ pow_nonneg ha _), hn.pow_neg⟩

lemma even.pow_pos_iff (hn : even n) (h₀ : 0 < n) : 0 < a ^ n ↔ a ≠ 0 :=
⟨λ h ha, by { rw [ha, zero_pow h₀] at h, exact lt_irrefl 0 h }, hn.pow_pos⟩

lemma even.pow_abs {p : ℕ} (hp : even p) (a : R) : |a| ^ p = a ^ p :=
begin
  rw [←abs_pow, abs_eq_self],
  exact hp.pow_nonneg _
end

@[simp] lemma pow_bit0_abs (a : R) (p : ℕ) : |a| ^ bit0 p = a ^ bit0 p := (even_bit0 _).pow_abs _

lemma odd.strict_mono_pow (hn : odd n) : strict_mono (λ a : R, a ^ n) :=
by cases hn with k hk; simpa only [hk, two_mul] using strict_mono_pow_bit1 _

end powers

/-- The cardinality of `fin (bit0 k)` is even, `fact` version.
This `fact` is needed as an instance by `matrix.special_linear_group.has_neg`. -/
lemma fintype.card_fin_even {k : ℕ} : fact (even (fintype.card (fin (bit0 k)))) :=
⟨by { rw [fintype.card_fin], exact even_bit0 k }⟩

section field_power
variable {K : Type*}

section division_ring
variables [division_ring K] {n : ℤ}

lemma odd.neg_zpow (h : odd n) (a : K) : (-a) ^ n = - a ^ n :=
by { obtain ⟨k, rfl⟩ := h.exists_bit1, exact zpow_bit1_neg _ _ }

lemma odd.neg_one_zpow (h : odd n) : (-1 : K) ^ n = -1 := by rw [h.neg_zpow, one_zpow]

end division_ring

variables [linear_ordered_field K] {n : ℤ} {a : K}

protected lemma even.zpow_nonneg (hn : even n) (a : K) : 0 ≤ a ^ n :=
begin
  cases le_or_lt 0 a with h h,
  { exact zpow_nonneg h _ },
  { exact (hn.neg_zpow a).subst (zpow_nonneg (neg_nonneg_of_nonpos h.le) _) }
end

theorem even.zpow_pos (hn : even n) (ha : a ≠ 0) : 0 < a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit0_pos ha k

protected lemma odd.zpow_nonneg (hn : odd n) (ha : 0 ≤ a) : 0 ≤ a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_nonneg_iff.mpr ha

theorem odd.zpow_pos (hn : odd n) (ha : 0 < a) : 0 < a ^ n :=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_pos_iff.mpr ha

theorem odd.zpow_nonpos (hn : odd n) (ha : a ≤ 0) : a ^ n ≤ 0:=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_nonpos_iff.mpr ha

theorem odd.zpow_neg (hn : odd n) (ha : a < 0) : a ^ n < 0:=
by cases hn with k hk; simpa only [hk, two_mul] using zpow_bit1_neg_iff.mpr ha

lemma even.zpow_abs {p : ℤ} (hp : even p) (a : K) : |a| ^ p = a ^ p :=
begin
  cases abs_choice a with h h;
  simp only [h, hp.neg_zpow _],
end

@[simp] lemma zpow_bit0_abs (a : K) (p : ℤ) : |a| ^ bit0 p = a ^ bit0 p :=
(even_bit0 _).zpow_abs _

lemma even.abs_zpow {p : ℤ} (hp : even p) (a : K) : |a ^ p| = a ^ p :=
begin
  rw [abs_eq_self],
  exact hp.zpow_nonneg _
end

@[simp] lemma abs_zpow_bit0 (a : K) (p : ℤ) :
  |a ^ bit0 p| = a ^ bit0 p :=
(even_bit0 _).abs_zpow _

end field_power
