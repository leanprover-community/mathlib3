/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.order
import algebra.big_operators.ring
import data.nat.modeq

/-!
# The Oxf*rd Invariants - Week 3, Problem 1

## Original statement

## Formalised statement
-/

open_locale big_operators

lemma nat.modeq_zero_iff {a b : ℕ} : a ≡ b [MOD 0] ↔ a = b :=
by rw [nat.modeq, nat.mod_zero, nat.mod_zero]

@[simp] lemma nat.add_modeq_left {a n : ℕ} : n + a ≡ a [MOD n] :=
by rw [nat.modeq, nat.add_mod_left]
@[simp] lemma nat.add_modeq_right {a n : ℕ} : a + n ≡ a [MOD n] :=
by rw [nat.modeq, nat.add_mod_right]


/-- Duplicate of `nat.mul_div_mul` -/
lemma nat.mul_div_mul_left (a b : ℕ) {c : ℕ} (hc : 0 < c) : c * a / (c * b) = a / b :=
nat.mul_div_mul a b hc
lemma nat.mul_div_mul_right (a b : ℕ) {c : ℕ} (hc : 0 < c) : a * c / (b * c) = a / b :=
by rw [mul_comm, mul_comm b, nat.mul_div_mul_left a b hc]

@[simp] lemma nat.add_sub_sub_cancel {a c : ℕ} (h : c ≤ a) (b : ℕ) : a + b - (a - c) = b + c :=
by rw [add_comm, nat.add_sub_assoc (nat.sub_le_self _ _), nat.sub_sub_self h]

theorem week3_p1_aux (n : ℕ) (a : ℕ → ℕ) (a_pos : ∀ i, 0 < a i)
  (ha : ∀ i < n, a (i + 1) ∣ a i + a (i + 2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 1), (a 0 * a (n + 1))/(a i * a (i + 1)) :=
begin
  suffices h : ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 1), (a 0 * a (n + 1))/(a i * a (i + 1))
           ∧ a (n + 1) ∣ a n * b - a 0,
  { obtain ⟨b, hb, -⟩ := h,
    exact ⟨b, hb⟩ },
  simp_rw ←@nat.cast_pos ℚ at a_pos,
  induction n with n ih,
  { refine ⟨1, _, _⟩,
    { rw [nat.cast_one, finset.sum_range_one, div_self],
      exact (mul_pos (a_pos 0) (a_pos 1)).ne' },
    { rw [mul_one, nat.sub_self],
      exact dvd_zero _ } },
  obtain ⟨b, hb, han⟩ := ih (λ i hi, ha i $ nat.lt_succ_of_lt hi),
  specialize ha n n.lt_succ_self,
  have ha₀ : a 0 ≤ a n * b, -- Needing this is an artifact of `ℕ`-substraction.
  { rw [←@nat.cast_le ℚ, nat.cast_mul, hb, ←div_le_iff' (a_pos _),
      ←mul_div_mul_right _ _ (a_pos $ n + 1).ne'],
    suffices h : ∀ i, i ∈ finset.range (n + 1) → 0 ≤ (a 0 : ℚ) * a (n + 1) / (a i * a (i + 1)),
    { exact finset.single_le_sum h (finset.self_mem_range_succ n) },
    refine (λ i _, div_nonneg _ _); refine mul_nonneg _ _; exact nat.cast_nonneg _ },
  refine ⟨(a n + a (n + 2))/ a (n + 1) * b - (a n * b - a 0) / a (n + 1), _, _⟩,
  { calc
      (((a n + a (n + 2)) / a (n + 1) * b - (a n * b - a 0) / a (n + 1) : ℕ) : ℚ)
        = (a n + a (n + 2)) / a (n + 1) * b - (a n * b - a 0) / a (n + 1) : begin
          rw [nat.cast_sub, nat.cast_mul, nat.cast_dvd_char_zero ha, nat.cast_add,
            nat.cast_dvd_char_zero han, nat.cast_sub ha₀, nat.cast_mul],
            { apply_instance }, -- char_zero ℚ
            { apply_instance }, -- char_zero ℚ
            { refine nat.div_le_of_le_mul _,
              rw [←mul_assoc, nat.mul_div_cancel' ha, add_mul],
              exact (nat.sub_le_self _ _).trans (nat.le_add_right _ _) }
        end
    ... = a (n + 2) / a (n + 1) * b + (a 0 * a (n + 2)) / (a (n + 1) * a (n + 2))
        : by rw [add_div, add_mul, sub_div, mul_div_right_comm, add_sub_sub_cancel,
            mul_div_mul_right _ _ (a_pos _).ne']
    ... = ∑ (i : ℕ) in finset.range (n + 2), a 0 * a (n + 2) / (a i * a (i + 1))
        : begin
          rw [finset.sum_range_succ, hb, finset.mul_sum],
          congr, ext i,
          rw [←mul_div_assoc, ←mul_div_right_comm, mul_div_assoc, mul_div_cancel _ (a_pos _).ne',
            mul_comm],
        end },
  { rw [nat.mul_sub_left_distrib, ← mul_assoc, nat.mul_div_cancel' ha, add_mul,
      nat.mul_div_cancel' han, nat.add_sub_sub_cancel ha₀, nat.add_sub_cancel],
    exact dvd_mul_right _ _ }
end

theorem week3_p1 {n : ℕ} (hn : 1 ≤ n) (a : ℕ → ℕ) (a_pos : ∀ i, 0 < a i)
  (ha : ∀ i < n - 1, a (i + 1) ∣ a i + a (i + 2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1)) :=
begin
  cases n,
  { exact (nat.not_succ_le_zero 0 hn).elim },
  { exact week3_p1_aux n a a_pos ha }
end
