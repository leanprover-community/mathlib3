/-
Copyright (c) 2014 Floris van Doorn (c) 2016 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Leonardo de Moura, Jeremy Avigad, Mario Carneiro
-/
import data.nat.order.basic
import algebra.ring.divisibility
import algebra.group_with_zero.divisibility
import algebra.order.with_zero

/-!
# Further lemmas about the natural numbers

The distinction between this file and `data.nat.order.basic` is not particularly clear.
They are separated by now to minimize the porting requirements for tactics during the transition to
mathlib4. After `data.rat.order` has been ported, please feel free to reorganize these two files.
-/

universes u v

variables {m n k : ℕ}
namespace nat

/-! ### `succ` -/

@[simp] lemma lt_one_iff {n : ℕ} : n < 1 ↔ n = 0 :=
lt_succ_iff.trans le_zero_iff

/-! ### `div` -/

protected lemma lt_div_iff_mul_lt {n d : ℕ} (hnd : d ∣ n) (a : ℕ) : a < n / d ↔ d * a < n :=
begin
  rcases d.eq_zero_or_pos with rfl | hd0, { simp [zero_dvd_iff.mp hnd] },
  rw [←mul_lt_mul_left hd0, ←nat.eq_mul_of_div_eq_right hnd rfl],
end

lemma div_eq_iff_eq_of_dvd_dvd {n x y : ℕ} (hn : n ≠ 0) (hx : x ∣ n) (hy : y ∣ n) :
  n / x = n / y ↔ x = y :=
begin
  split,
  { intros h,
    rw ←mul_right_inj' hn,
    apply nat.eq_mul_of_div_eq_left (dvd_mul_of_dvd_left hy x),
    rw [eq_comm, mul_comm, nat.mul_div_assoc _ hy],
    exact nat.eq_mul_of_div_eq_right hx h },
  { intros h, rw h },
end

/-! ### `mod`, `dvd` -/

protected lemma div_div_self : ∀ {a b : ℕ}, b ∣ a → 0 < a → a / (a / b) = b
| a     0     h₁ h₂ := by rw [eq_zero_of_zero_dvd h₁, nat.div_zero, nat.div_zero]
| 0     b     h₁ h₂ := absurd h₂ dec_trivial
| (a+1) (b+1) h₁ h₂ :=
(nat.mul_left_inj (nat.div_pos (le_of_dvd (succ_pos a) h₁) (succ_pos b))).1 $
  by rw [nat.div_mul_cancel (div_dvd_of_dvd h₁), nat.mul_div_cancel' h₁]

@[simp] protected theorem dvd_one {n : ℕ} : n ∣ 1 ↔ n = 1 :=
⟨eq_one_of_dvd_one, λ e, e.symm ▸ dvd_rfl⟩

@[simp] protected theorem not_two_dvd_bit1 (n : ℕ) : ¬ 2 ∣ bit1 n :=
by { rw [bit1, nat.dvd_add_right two_dvd_bit0, nat.dvd_one], cc }

/-- A natural number `m` divides the sum `m + n` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_left {m n : ℕ} :
  m ∣ m + n ↔ m ∣ n :=
nat.dvd_add_right (dvd_refl m)

/-- A natural number `m` divides the sum `n + m` if and only if `m` divides `n`.-/
@[simp] protected lemma dvd_add_self_right {m n : ℕ} :
  m ∣ n + m ↔ m ∣ n :=
nat.dvd_add_left (dvd_refl m)

-- TODO: update `nat.dvd_sub` in core
lemma dvd_sub' {k m n : ℕ} (h₁ : k ∣ m) (h₂ : k ∣ n) : k ∣ m - n :=
begin
  cases le_total n m with H H,
  { exact dvd_sub H h₁ h₂ },
  { rw tsub_eq_zero_iff_le.mpr H,
    exact dvd_zero k },
end

lemma succ_div : ∀ (a b : ℕ), (a + 1) / b =
  a / b + if b ∣ a + 1 then 1 else 0
| a     0     := by simp
| 0     1     := by simp
| 0     (b+2) := have hb2 : b + 2 > 1, from dec_trivial,
  by simp [ne_of_gt hb2, div_eq_of_lt hb2]
| (a+1) (b+1) := begin
  rw [nat.div_def], conv_rhs { rw nat.div_def },
  by_cases hb_eq_a : b = a + 1,
  { simp [hb_eq_a, le_refl] },
  by_cases hb_le_a1 : b ≤ a + 1,
  { have hb_le_a : b ≤ a, from le_of_lt_succ (lt_of_le_of_ne hb_le_a1 hb_eq_a),
    have h₁ : (0 < b + 1 ∧ b + 1 ≤ a + 1 + 1),
      from ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a1⟩,
    have h₂ : (0 < b + 1 ∧ b + 1 ≤ a + 1),
      from ⟨succ_pos _, (add_le_add_iff_right _).2 hb_le_a⟩,
    have dvd_iff : b + 1 ∣ a - b + 1 ↔  b + 1 ∣ a + 1 + 1,
    { rw [nat.dvd_add_iff_left (dvd_refl (b + 1)),
        ← add_tsub_add_eq_tsub_right a 1 b, add_comm (_ - _), add_assoc,
        tsub_add_cancel_of_le (succ_le_succ hb_le_a), add_comm 1] },
    have wf : a - b < a + 1, from lt_succ_of_le tsub_le_self,
    rw [if_pos h₁, if_pos h₂, add_tsub_add_eq_tsub_right, ← tsub_add_eq_add_tsub hb_le_a,
      by exact have _ := wf, succ_div (a - b),
      add_tsub_add_eq_tsub_right],
    simp [dvd_iff, succ_eq_add_one, add_comm 1, add_assoc] },
  { have hba : ¬ b ≤ a,
      from not_le_of_gt (lt_trans (lt_succ_self a) (lt_of_not_ge hb_le_a1)),
    have hb_dvd_a : ¬ b + 1 ∣ a + 2,
      from λ h, hb_le_a1 (le_of_succ_le_succ (le_of_dvd (succ_pos _) h)),
    simp [hba, hb_le_a1, hb_dvd_a], }
end

lemma succ_div_of_dvd {a b : ℕ} (hba : b ∣ a + 1) :
  (a + 1) / b = a / b + 1 :=
by rw [succ_div, if_pos hba]

lemma succ_div_of_not_dvd {a b : ℕ} (hba : ¬ b ∣ a + 1) :
  (a + 1) / b = a / b :=
by rw [succ_div, if_neg hba, add_zero]

lemma dvd_iff_div_mul_eq (n d : ℕ) : d ∣ n ↔ n / d * d = n :=
⟨λ h, nat.div_mul_cancel h, λ h, dvd.intro_left (n / d) h⟩

lemma dvd_iff_le_div_mul (n d : ℕ) : d ∣ n ↔ n ≤ n / d * d :=
((dvd_iff_div_mul_eq _ _).trans le_antisymm_iff).trans (and_iff_right (div_mul_le_self n d))

lemma dvd_iff_dvd_dvd (n d : ℕ) : d ∣ n ↔ ∀ k : ℕ, k ∣ d → k ∣ n :=
⟨λ h k hkd, dvd_trans hkd h, λ h, h _ dvd_rfl⟩

lemma dvd_div_of_mul_dvd {a b c : ℕ} (h : a * b ∣ c) : b ∣ c / a :=
if ha : a = 0 then
  by simp [ha]
else
  have ha : 0 < a, from nat.pos_of_ne_zero ha,
  have h1 : ∃ d, c = a * b * d, from h,
  let ⟨d, hd⟩ := h1 in
  have h2 : c / a = b * d, from nat.div_eq_of_eq_mul_right ha (by simpa [mul_assoc] using hd),
  show ∃ d, c / a = b * d, from ⟨d, h2⟩

@[simp] lemma dvd_div_iff {a b c : ℕ} (hbc : c ∣ b) : a ∣ b / c ↔ c * a ∣ b :=
⟨λ h, mul_dvd_of_dvd_div hbc h, λ h, dvd_div_of_mul_dvd h⟩

@[simp]
lemma div_div_div_eq_div : ∀ {a b c : ℕ} (dvd : b ∣ a) (dvd2 : a ∣ c), (c / (a / b)) / b = c / a
| 0 _ := by simp
| (a + 1) 0 := λ _ dvd _, by simpa using dvd
| (a + 1) (c + 1) :=
have a_split : a + 1 ≠ 0 := succ_ne_zero a,
have c_split : c + 1 ≠ 0 := succ_ne_zero c,
λ b dvd dvd2,
begin
  rcases dvd2 with ⟨k, rfl⟩,
  rcases dvd with ⟨k2, pr⟩,
  have k2_nonzero : k2 ≠ 0 := λ k2_zero, by simpa [k2_zero] using pr,
  rw [nat.mul_div_cancel_left k (nat.pos_of_ne_zero a_split), pr,
    nat.mul_div_cancel_left k2 (nat.pos_of_ne_zero c_split), nat.mul_comm ((c + 1) * k2) k,
    ←nat.mul_assoc k (c + 1) k2, nat.mul_div_cancel _ (nat.pos_of_ne_zero k2_nonzero),
    nat.mul_div_cancel _ (nat.pos_of_ne_zero c_split)],
end

/-- `n` is not divisible by `a` iff it is between `a * k` and `a * (k + 1)` for some `k`. -/
lemma not_dvd_iff_between_consec_multiples (n : ℕ) {a : ℕ} (ha : 0 < a) :
  (∃ k : ℕ, a * k < n ∧ n < a * (k + 1)) ↔ ¬ a ∣ n :=
begin
  refine ⟨λ ⟨k, hk1, hk2⟩, not_dvd_of_between_consec_multiples hk1 hk2,
          λ han, ⟨n/a, ⟨lt_of_le_of_ne (mul_div_le n a) _, lt_mul_div_succ _ ha⟩⟩⟩,
  exact mt (dvd.intro (n/a)) han,
end

/-- Two natural numbers are equal if and only if they have the same multiples. -/
lemma dvd_right_iff_eq {m n : ℕ} : (∀ a : ℕ, m ∣ a ↔ n ∣ a) ↔ m = n :=
⟨λ h, dvd_antisymm ((h _).mpr dvd_rfl) ((h _).mp dvd_rfl), λ h n, by rw h⟩

/-- Two natural numbers are equal if and only if they have the same divisors. -/
lemma dvd_left_iff_eq {m n : ℕ} : (∀ a : ℕ, a ∣ m ↔ a ∣ n) ↔ m = n :=
⟨λ h, dvd_antisymm ((h _).mp dvd_rfl) ((h _).mpr dvd_rfl), λ h n, by rw h⟩

/-- `dvd` is injective in the left argument -/
lemma dvd_left_injective : function.injective ((∣) : ℕ → ℕ → Prop) :=
λ m n h, dvd_right_iff_eq.mp $ λ a, iff_of_eq (congr_fun h a)

lemma div_lt_div_of_lt_of_dvd {a b d : ℕ} (hdb : d ∣ b) (h : a < b) : a / d < b / d :=
by { rw nat.lt_div_iff_mul_lt hdb, exact lt_of_le_of_lt (mul_div_le a d) h }

end nat
