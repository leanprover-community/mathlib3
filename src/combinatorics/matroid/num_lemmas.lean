

import data.set.intervals data.nat.parity
import tactic

universes u v w
open_locale classical

/-! Some simple additions to the api -/

open set

namespace int

/-
Phased out lemmas and definitions:
  * `to_nat_zero_of_neg`
  * `gpow`
-/


lemma le_sub_one_of_le_of_ne {x y : ℤ} :
  x ≤ y → x ≠ y → x ≤ y - 1 :=
  λ h h', int.le_sub_one_of_lt (lt_of_le_of_ne h h')

lemma le_of_not_gt' {x y : ℤ} :
  ¬ (y < x) → x ≤ y :=
  not_lt.mp

lemma nonneg_le_one_iff {x : ℤ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
  x = 0 ∨ x = 1 :=
by {by_cases h : x ≤ 0, left, apply le_antisymm h h0,
    push_neg at h, rw int.le_sub_one_iff.symm at h,
    right, linarith, }

lemma nat_le_two_iff {x : ℕ} (h2 : x ≤ 2) :
  x = 0 ∨ x = 1 ∨ x = 2 :=
by {cases x, tauto, cases x, tauto, cases x, tauto, repeat {rw nat.succ_eq_add_one at h2}, linarith}

lemma nonneg_le_two_iff {x : ℤ} (h0 : 0 ≤ x) (h2 : x ≤ 2) :
  x = 0 ∨ x = 1 ∨ x = 2 :=
begin
  by_cases h2' : 2 ≤ x, right, right, apply le_antisymm h2 h2',
  push_neg at h2', rw int.le_sub_one_iff.symm at h2',
  cases nonneg_le_one_iff h0 h2', {left, exact h}, {right, left, exact h},
end

lemma to_nat_zero_of_nonpos {x : ℤ} (hx : x ≤ 0):
  x.to_nat = 0 :=
by {
  /-rcases em (x = 0) with (rfl | hx'),
  simp only [to_nat_zero],
  cases x,-/
  rw le_iff_eq_or_lt at hx,
  cases hx with hz hn,
  rw hz,
  refl,
  rw ← to_nat_zero,
  sorry,
 }
  --apply to_nat_zero_of_neg (lt_of_le_of_ne hx hx'), }

end int



namespace nat

lemma lt_iff_succ_le {a b : ℕ} :
  a < b ↔ a.succ ≤ b :=
⟨λ h, succ_le_of_lt h, λ h, lt_of_succ_le h⟩

end nat



section order

variables {α : Type*} [partial_order α] {a b c : α}

lemma squeeze_le_trans_left (hab : a ≤ b) (hbc : b ≤ c) (hac : a = c):
  a = b :=
le_antisymm hab (hbc.trans hac.symm.le)

lemma squeeze_le_trans_right (hab : a ≤ b) (hbc : b ≤ c) (hac : a = c):
  b = c :=
le_antisymm hbc (hac.symm.le.trans hab)

lemma squeeze_le_trans (hab : a ≤ b) (hbc : b ≤ c) (hac : a = c):
  a = b ∧ b = c :=
⟨squeeze_le_trans_left hab hbc hac, squeeze_le_trans_right hab hbc hac⟩

end order

section neg_one_pow


lemma nat.neg_one_pow_sum_eq_zero_of_sum_odd {n m : ℕ} (h : odd (n+m)) :
  (-1 :ℤ)^m + (-1)^n = 0 :=
begin
  obtain ⟨ (⟨k,rfl⟩ | ⟨k,rfl⟩), (⟨j,rfl⟩ | ⟨j,rfl⟩)⟩ := ⟨nat.even_or_odd n, nat.even_or_odd m⟩,
  { exfalso, apply nat.odd_iff_not_even.mp h ⟨k+j, by {rw mul_add}⟩, },
  { simp [nat.neg_one_pow_of_odd ⟨j,rfl⟩, nat.neg_one_pow_of_even ⟨k,rfl⟩]},
  { simp [nat.neg_one_pow_of_even ⟨j,rfl⟩, nat.neg_one_pow_of_odd ⟨k,rfl⟩]},
  { exfalso, apply nat.odd_iff_not_even.mp h ⟨j+k+1, by linarith⟩},
end

def int.neg_one_pow (n : ℤˣ) : ℤ := @group.zpow (units ℤ) _ (-1) n
-- gpow looks like it's been completely deprecated
-- for some reason i get an error when i try to do `(n : ℤ)`

lemma int.neg_one_pow_eq_neg_one_pow_neg (n : ℤˣ) :
  int.neg_one_pow n = int.neg_one_pow (-n) :=
begin
  unfold int.neg_one_pow,
  simp only [zpow_neg, group.zpow_eq_has_pow],
  /- rw [eq_comm],
  apply units.inv_eq_of_mul_eq_one,
  simp,-/
  sorry,
end

lemma int.neg_one_pow_eq_abs (n : ℤ):
  int.neg_one_pow n = (-1)^(n.nat_abs) :=
begin
  unfold int.neg_one_pow,
  rcases int.nat_abs_eq n with (h | h), rw h, simp,
  rw h,
  simp only [int.nat_abs_of_nat, gpow_neg, int.nat_abs_neg, group.gpow_eq_has_pow, gpow_coe_nat],
  apply units.inv_eq_of_mul_eq_one,
  simp only [units.coe_neg_one, units.coe_pow, ← pow_add, ← two_mul],
  apply nat.neg_one_pow_of_even,
  exact ⟨_, rfl⟩,
end

lemma int.neg_one_pow_coe {n : ℕ}: int.neg_one_pow n = (-1)^n :=
by {rw int.neg_one_pow_eq_abs, congr', }

lemma neg_one_pow_of_even {n : ℤ} (hn : even n) : int.neg_one_pow n = 1 :=
begin
  obtain ⟨k,rfl⟩ := hn,
  obtain ⟨a, (rfl | rfl)⟩ := k.eq_coe_or_neg, swap,
  rw [(by simp : ((2 : ℤ) * - (a : ℤ) = - (2*a ))), int.neg_one_pow_eq_neg_one_pow_neg, neg_neg],
  all_goals
  { rw [← (by simp: ((2 * a : ℕ) : ℤ) = ((2 : ℤ)* (a : ℤ))), int.neg_one_pow_coe,
    nat.neg_one_pow_of_even ⟨_, rfl⟩]},
end
/-
lemma neg_one_pow_of_odd {n : ℤ} (hn : odd n) : int.neg_one_pow n = -1 :=
begin
  obtain ⟨k,rfl⟩ := hn,
  rw [int.neg_one_pow], convert gpow_add_one (-1 : units ℤ) (2*k),
end
-/
end neg_one_pow
