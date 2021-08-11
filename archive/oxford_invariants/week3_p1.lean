/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import data.nat.modeq

/-!
# The Oxf*rd Invariants - Week 3, Problem 1

## Original statement

## Formalised statement
-/

open_locale big_operators

lemma nat.modeq.modeq_zero_iff' {a b : ℕ} : a ≡ b [MOD 0] ↔ a = b :=
by rw [nat.modeq, nat.mod_zero, nat.mod_zero]

/-- Duplicate of `nat.mul_div_mul` -/
lemma nat.mul_div_mul_left (a b : ℕ) {c : ℕ} (hc : 0 < c) : c * a / (c * b) = a / b :=
nat.mul_div_mul a b hc
lemma nat.mul_div_mul_right (a b : ℕ) {c : ℕ} (hc : 0 < c) : a * c / (b * c) = a / b :=
by rw [mul_comm, mul_comm b, nat.mul_div_mul_left a b hc]

theorem week3_p1_aux {n : ℕ} (a : ℕ → ℕ) (ha : ∀ i < n + 1, a (i+1) ∣ a i + a (i+2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 2), (a 0 * a (n + 2))/(a i * a (i + 1)) :=
begin
  suffices h : ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range (n + 2), (a 0 * a (n + 2))/(a i * a (i + 1))
           ∧ a n * b ≡ a 0 [MOD a (n + 1)],
  { obtain ⟨b, hb, -⟩ := h,
    exact ⟨b, hb⟩ },
  induction n with n ih,
  { obtain ha₀ | ha₀ := eq_or_ne (a 0) 0,
    { exact ⟨0, by simp_rw [ha₀, nat.cast_zero, zero_mul, zero_div, finset.sum_const_zero],
        by rw [ha₀, zero_mul]⟩ },
    specialize ha 0 nat.zero_lt_one,
    simp_rw zero_add at *,
    obtain ha₂ | ha₂ := eq_or_ne (a 2) 0,
    { refine ⟨0, by simp_rw [ha₂, nat.cast_zero, mul_zero, zero_div, finset.sum_const_zero], _⟩,
      rw ha₂ at ha,
      rwa [mul_zero, nat.modeq.comm, nat.modeq.modeq_zero_iff] },
    refine ⟨(a 0 + a 2)/a 1, _, _⟩, --by rw [nat.modeq, nat.mod_self, nat.mul_mod_right]
    rw [nat.cast_dvd_char_zero ha, finset.sum_range_succ, finset.sum_range_one],
    norm_num,
    rw [mul_div_mul_left, mul_div_mul_right, add_div, add_comm],
    { exact nat.cast_ne_zero.2 ha₂ },
    { exact nat.cast_ne_zero.2 ha₀ },
    { apply_instance },
    sorry
     },
  obtain ⟨b, hb₁, hb₂⟩ := ih (λ i hi, ha i $ nat.lt_succ_of_lt hi),
  use (a (n + 1) + a (n + 3))/ a (n + 2) * b - (a (n + 1) * b - a 0) / a (n + 2),
  split,
  {
    rw [finset.sum_range_succ],
    rw nat.succ_eq_add_one, norm_num,

  },

end

theorem week3_p1_aux_aux {n : ℕ} (a : ℕ → ℕ) (ha : ∀ i < n, a (i+1) ∣ a i + a (i+2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1)) :=
begin
  suffices : ∀ n, (∀ i < n, a (i+1) ∣ a i + a (i+2)) →
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

theorem week3_p1 {n : ℕ} (hn : 2 ≤ n) (a : ℕ → ℕ) (ha : ∀ i < n, a (i+1) ∣ a i + a (i+2)) :
  ∃ b : ℕ, (b : ℚ) = ∑ i in finset.range n, (a 0 * a n)/(a i * a (i + 1)) :=
begin
  obtain ⟨_, rfl⟩ := nat.le.dest hn,
  have := week3_p1_aux a,
  -- obtain _ | _ | _ := hn,
  -- { sorry },

  -- { sorry },
  -- exact week3_p1_aux a ha,
end
