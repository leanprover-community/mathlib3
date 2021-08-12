/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
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

@[simp] lemma nat.modeq_add_left {a n : ℕ} : n + a ≡ a [MOD n] :=
by rw [nat.modeq, nat.add_mod_left]
@[simp] lemma nat.modeq_add_right {a n : ℕ} : a + n ≡ a [MOD n] :=
by rw [nat.modeq, nat.add_mod_right]


/-- Duplicate of `nat.mul_div_mul` -/
lemma nat.mul_div_mul_left (a b : ℕ) {c : ℕ} (hc : 0 < c) : c * a / (c * b) = a / b :=
nat.mul_div_mul a b hc
lemma nat.mul_div_mul_right (a b : ℕ) {c : ℕ} (hc : 0 < c) : a * c / (b * c) = a / b :=
by rw [mul_comm, mul_comm b, nat.mul_div_mul_left a b hc]

@[simp] lemma nat.add_sub_sub_cancel {a c : ℕ} (h : c ≤ a) (b : ℕ) : a + b - (a - c) = b + c :=
by rw [add_comm, nat.add_sub_assoc (nat.sub_le_self _ _), nat.sub_sub_self h]

theorem week3_p1_aux_pos (n : ℕ) (a : ℕ → ℕ) (a_pos : ∀ i, 0 < a i)
  (ha : ∀ i < n, a (i + 1) ∣ a i + a (i + 2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 1), (a 0 * a (n + 1))/(a i * a (i + 1)) :=
begin
  suffices h : ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 1), (a 0 * a (n + 1))/(a i * a (i + 1))
           ∧ a (n + 1) ∣ a n * b - a 0,
  { obtain ⟨b, hb, -⟩ := h,
    exact ⟨b, hb⟩ },
  induction n with n ih,
  { refine ⟨1, _, _⟩,
    { rw [nat.cast_one, finset.sum_range_one, div_self],
      rw [←nat.cast_mul, nat.cast_ne_zero],
      exact (mul_pos (a_pos 0) (a_pos 1)).ne' },
    { rw [mul_one, nat.sub_self],
      exact dvd_zero _ } },
  obtain ⟨b, hb, han⟩ := ih (λ i hi, ha i $ nat.lt_succ_of_lt hi),
  specialize ha n n.lt_succ_self,
  refine ⟨(a n + a (n + 2))/ a (n + 1) * b - (a n * b - a 0) / a (n + 1), _, _⟩,
  { calc
      (((a n + a (n + 2)) / a (n + 1) * b - (a n * b - a 0) / a (n + 1) : ℕ) : ℚ)
        = (a n + a (n + 2)) / a (n + 1) * b - (a n * b - a 0) / a (n + 1) : begin
          rw [nat.cast_sub, nat.cast_mul, nat.cast_dvd_char_zero ha, nat.cast_add,
            nat.cast_dvd_char_zero han, nat.cast_sub, nat.cast_mul],
            sorry,
            { apply_instance }, -- char_zero ℚ
            { apply_instance }, -- char_zero ℚ
            sorry,
        end
    ... = a (n + 2) / a (n + 1) * b + (a 0 * a (n + 2)) / (a (n + 1) * a (n + 2)) : begin
          rw [add_div, add_mul, sub_div, mul_div_right_comm, add_sub_sub_cancel, mul_div_mul_right],
          exact nat.cast_ne_zero.2 (a_pos (n + 2)).ne',
        end
    ... = ∑ (i : ℕ) in finset.range (n + 2), a 0 * a (n + 2) / (a i * a (i + 1))
        : begin
          rw [finset.sum_range_succ, hb, finset.mul_sum],
          congr, ext i,
          rw [←mul_div_assoc, ←mul_div_right_comm, mul_div_assoc, mul_div_cancel, mul_comm],
          sorry,
        end },
  rw [nat.mul_sub_left_distrib, ← mul_assoc, nat.mul_div_cancel' ha, add_mul,
    nat.mul_div_cancel' han, nat.add_sub_sub_cancel, nat.add_sub_cancel],
  exact dvd_mul_right _ _,
  sorry,
end

theorem week3_p1 {n : ℕ} (hn : 1 ≤ n) (a : ℕ → ℕ) (a_pos : ∀ i, 0 < a i)
  (ha : ∀ i < n - 1, a (i + 1) ∣ a i + a (i + 2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1)) :=
begin
  cases n,
  { exact (nat.not_succ_le_zero 0 hn).elim },
  { exact week3_p1_aux_pos n a a_pos ha }
end

#exit

theorem week3_p1_aux_dvd {n : ℕ} (a : ℕ → ℕ) (ha : ∀ i < n + 1, a (i + 1) ∣ a i + a (i + 2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 2), (a 0 * a (n + 2))/(a i * a (i + 1)) :=
begin
  suffices h : ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 2), (a 0 * a (n + 2))/(a i * a (i + 1))
           ∧ a (n + 2) ∣ a (n + 1) * b - a 0,
  { obtain ⟨b, hb, -⟩ := h,
    exact ⟨b, hb⟩ },
  induction n with n ih,
  { /-obtain ha₀ | ha₀ := eq_or_ne (a 0) 0,
    { refine ⟨0, by simp_rw [ha₀, nat.cast_zero, zero_mul, zero_div, finset.sum_const_zero],
        by rw [ha₀, mul_zero]⟩ },
    specialize ha 0 nat.zero_lt_one,
    simp_rw zero_add at *,
    obtain ha₂ | ha₂ := eq_or_ne (a 2) 0,
    { refine ⟨0, by simp_rw [ha₂, nat.cast_zero, mul_zero, zero_div, finset.sum_const_zero], _⟩,
      rw ha₂ at ha,
      rwa [mul_zero, nat.modeq.comm, nat.modeq.modeq_zero_iff, ha₂, zero_dvd_iff],
      sorry },
    refine ⟨(a 0 + a 2)/a 1, _, _⟩, --by rw [nat.modeq, nat.mod_self, nat.mul_mod_right]
    { rw [nat.cast_dvd_char_zero ha, finset.sum_range_succ, finset.sum_range_one],
      norm_num,
      rw [mul_div_mul_left, mul_div_mul_right, add_div, add_comm],
      { exact nat.cast_ne_zero.2 ha₂ },
      { exact nat.cast_ne_zero.2 ha₀ },
      { apply_instance } },
    { rw nat.mul_div_cancel' ha,
      exact nat.modeq_add_right}-/
      sorry },
  obtain ⟨b, hb, han⟩ := ih (λ i hi, ha i $ nat.lt_succ_of_lt hi),
  use (a (n + 1) + a (n + 3))/ a (n + 2) * b - (a (n + 1) * b - a 0) / a (n + 2),
  split,
  sorry,
  /-{ calc
      (((a (n + 1) + a (n + 3)) / a (n + 2) * b - (a (n + 1) * b - a 0) / a (n + 2) : ℕ) : ℚ)
        = (a (n + 1) + a (n + 3)) / a (n + 2) * b - (a (n + 1) * b - a 0) / a (n + 2) : begin
          rw [nat.cast_sub, nat.cast_mul,
            nat.cast_dvd_char_zero (ha (n + 1) $ nat.lt_succ_self _), nat.cast_add,
            nat.cast_dvd_char_zero, nat.cast_sub, nat.cast_mul],
            sorry,
            sorry,
            sorry,
            sorry,
        end
    ... = a (n + 3) / a (n + 2) * b + (a 0 * a (n + 3)) / (a (n + 2) * a (n + 3)) : begin
          rw [add_div, add_mul, sub_div, mul_div_right_comm, add_sub_sub_cancel, mul_div_mul_right],
            sorry,
        end
    ... = ∑ (i : ℕ) in finset.range (n + 3), a 0 * a (n + 3) / (a i * a (i + 1))
        : begin
          rw [finset.sum_range_succ, hb, finset.mul_sum],
          congr, ext i,
          rw [←mul_div_assoc, ←mul_div_right_comm, mul_div_assoc, mul_div_cancel, mul_comm],
          sorry,
        end },-/
  rw [nat.mul_sub_left_distrib, ← mul_assoc, nat.mul_div_cancel' (ha n.succ $ nat.lt_succ_self _),
    add_mul, nat.mul_div_cancel' han, nat.add_sub_sub_cancel, nat.add_sub_cancel],
  exact dvd_mul_right _ _,
  sorry,
end

theorem week3_p1_aux {n : ℕ} (a : ℕ → ℕ) (ha : ∀ i < n + 1, a (i + 1) ∣ a i + a (i + 2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 2), (a 0 * a (n + 2))/(a i * a (i + 1)) :=
begin
  suffices h : ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 2), (a 0 * a (n + 2))/(a i * a (i + 1))
           ∧ a (n + 1) * b ≡ a 0 [MOD a (n + 2)],
  { obtain ⟨b, hb, -⟩ := h,
    exact ⟨b, hb⟩ },
  induction n with n ih,
  { /-obtain ha₀ | ha₀ := eq_or_ne (a 0) 0,
    { refine ⟨0, by simp_rw [ha₀, nat.cast_zero, zero_mul, zero_div, finset.sum_const_zero],
        by rw [ha₀, mul_zero]⟩ },
    specialize ha 0 nat.zero_lt_one,
    simp_rw zero_add at *,
    obtain ha₂ | ha₂ := eq_or_ne (a 2) 0,
    { refine ⟨0, by simp_rw [ha₂, nat.cast_zero, mul_zero, zero_div, finset.sum_const_zero], _⟩,
      rw ha₂ at ha,
      rwa [mul_zero, nat.modeq.comm, nat.modeq.modeq_zero_iff, ha₂, zero_dvd_iff],
      sorry },
    refine ⟨(a 0 + a 2)/a 1, _, _⟩, --by rw [nat.modeq, nat.mod_self, nat.mul_mod_right]
    { rw [nat.cast_dvd_char_zero ha, finset.sum_range_succ, finset.sum_range_one],
      norm_num,
      rw [mul_div_mul_left, mul_div_mul_right, add_div, add_comm],
      { exact nat.cast_ne_zero.2 ha₂ },
      { exact nat.cast_ne_zero.2 ha₀ },
      { apply_instance } },
    { rw nat.mul_div_cancel' ha,
      exact nat.modeq_add_right}-/
      sorry },
  obtain ⟨b, hb, han⟩ := ih (λ i hi, ha i $ nat.lt_succ_of_lt hi),
  use (a (n + 1) + a (n + 3))/ a (n + 2) * b - (a (n + 1) * b - a 0) / a (n + 2),
  split,
  sorry,
  /-{ calc
      (((a (n + 1) + a (n + 3)) / a (n + 2) * b - (a (n + 1) * b - a 0) / a (n + 2) : ℕ) : ℚ)
        = (a (n + 1) + a (n + 3)) / a (n + 2) * b - (a (n + 1) * b - a 0) / a (n + 2) : begin
          rw [nat.cast_sub, nat.cast_mul,
            nat.cast_dvd_char_zero (ha (n + 1) $ nat.lt_succ_self _), nat.cast_add,
            nat.cast_dvd_char_zero, nat.cast_sub, nat.cast_mul],
            sorry,
            sorry,
            sorry,
            sorry,
        end
    ... = a (n + 3) / a (n + 2) * b + (a 0 * a (n + 3)) / (a (n + 2) * a (n + 3)) : begin
          rw [add_div, add_mul, sub_div, mul_div_right_comm, add_sub_sub_cancel, mul_div_mul_right],
            sorry,
        end
    ... = ∑ (i : ℕ) in finset.range (n + 3), a 0 * a (n + 3) / (a i * a (i + 1))
        : begin
          rw [finset.sum_range_succ, hb, finset.mul_sum],
          congr, ext i,
          rw [←mul_div_assoc, ←mul_div_right_comm, mul_div_assoc, mul_div_cancel, mul_comm],
          sorry,
        end },-/
  rw [nat.mul_sub_left_distrib, ← mul_assoc, nat.mul_div_cancel', add_mul, nat.mul_div_cancel',
    nat.add_sub_sub_cancel, nat.modeq, add_comm, nat.add_mul_mod_self_left],
  rw [nat.modeq, add_comm, nat.add_mul_mod_self_left],
  nth_rewrite 1 ←zero_add (a 0),
  refine nat.modeq.modeq_add _ _,
end

theorem week3_p1_aux_aux {n : ℕ} (a : ℕ → ℕ) (ha : ∀ i < n, a (i + 1) ∣ a i + a (i + 2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1)) :=
begin
  suffices : ∀ n, (∀ i < n, a (i + 1) ∣ a i + a (i + 2)) →
    ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1))
           ∧ a (n - 1) * b ≡ a 0 [MOD a n],
  { obtain ⟨b, hb, -⟩ := this n ha,
    exact ⟨b, hb⟩ },
  clear_dependent n,
  intros n ha,
  induction n with n ih,
  { simp,
    rw [nat.modeq.comm, nat.modeq.modeq_zero_iff] },
  obtain ⟨b, hb₁, hb₂⟩ := ih (λ i hi, ha i $ nat.lt_succ_of_lt hi),
  cases n,
  {
    simp at hb₁,
  },
  use (a (n - 1) + a (n + 1))/a n + a 0 - a (n - 1) * b,
  obtain han | han := eq_or_ne (a n) 0,
  {
    rw [han, nat.modeq.modeq_zero_iff'] at hb₂,
    suffices h : a (n.succ - 1) * ((a (n - 1) + a (n + 1)) / a n + a 0 - a (n - 1) * b) ≡ a 0
      [MOD a n.succ],
    { sorry },
    have := ha (n - 1) ((nat.sub_le_self _ _).trans_lt $ nat.lt_succ_self _),
    rw [nat.succ_sub_one, han, zero_mul, ←hb₂, nat.modeq.comm, nat.modeq.modeq_zero_iff],
  },
  split,
  { sorry },
  { sorry },

end
