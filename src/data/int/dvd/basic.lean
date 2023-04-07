/-
Copyright (c) 2016 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import data.int.order.basic
import data.nat.cast.basic

/-!
# Basic lemmas about the divisibility relation in `ℤ`.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

open nat

namespace int

@[norm_cast] theorem coe_nat_dvd {m n : ℕ} : (↑m : ℤ) ∣ ↑n ↔ m ∣ n :=
⟨λ ⟨a, ae⟩, m.eq_zero_or_pos.elim
  (λm0, by simp [m0] at ae; simp [ae, m0])
  (λm0l, by
  { cases eq_coe_of_zero_le (@nonneg_of_mul_nonneg_right ℤ _ m a
      (by simp [ae.symm]) (by simpa using m0l)) with k e,
    subst a, exact ⟨k, int.coe_nat_inj ae⟩ }),
 λ ⟨k, e⟩, dvd.intro k $ by rw [e, int.coe_nat_mul]⟩

theorem coe_nat_dvd_left {n : ℕ} {z : ℤ} : (↑n : ℤ) ∣ z ↔ n ∣ z.nat_abs :=
by rcases nat_abs_eq z with eq | eq; rw eq; simp [←coe_nat_dvd]

theorem coe_nat_dvd_right {n : ℕ} {z : ℤ} : z ∣ (↑n : ℤ) ↔ z.nat_abs ∣ n :=
by rcases nat_abs_eq z with eq | eq; rw eq; simp [←coe_nat_dvd]

theorem le_of_dvd {a b : ℤ} (bpos : 0 < b) (H : a ∣ b) : a ≤ b :=
match a, b, eq_succ_of_zero_lt bpos, H with
| (m : ℕ), ._, ⟨n, rfl⟩, H := coe_nat_le_coe_nat_of_le $
  nat.le_of_dvd n.succ_pos $ coe_nat_dvd.1 H
| -[1+ m], ._, ⟨n, rfl⟩, _ :=
  le_trans (le_of_lt $ neg_succ_lt_zero _) (coe_zero_le _)
end

theorem eq_one_of_dvd_one {a : ℤ} (H : 0 ≤ a) (H' : a ∣ 1) : a = 1 :=
match a, eq_coe_of_zero_le H, H' with
| ._, ⟨n, rfl⟩, H' := congr_arg coe $
  nat.eq_one_of_dvd_one $ coe_nat_dvd.1 H'
end

theorem eq_one_of_mul_eq_one_right {a b : ℤ} (H : 0 ≤ a) (H' : a * b = 1) : a = 1 :=
eq_one_of_dvd_one H ⟨b, H'.symm⟩

theorem eq_one_of_mul_eq_one_left {a b : ℤ} (H : 0 ≤ b) (H' : a * b = 1) : b = 1 :=
eq_one_of_mul_eq_one_right H (by rw [mul_comm, H'])

lemma of_nat_dvd_of_dvd_nat_abs {a : ℕ} : ∀ {z : ℤ} (haz : a ∣ z.nat_abs), ↑a ∣ z
| (int.of_nat _) haz := int.coe_nat_dvd.2 haz
| -[1+k] haz :=
  begin
    change ↑a ∣ -(k+1 : ℤ),
    apply dvd_neg_of_dvd,
    apply int.coe_nat_dvd.2,
    exact haz
  end

lemma dvd_nat_abs_of_of_nat_dvd {a : ℕ} : ∀ {z : ℤ} (haz : ↑a ∣ z), a ∣ z.nat_abs
| (int.of_nat _) haz := int.coe_nat_dvd.1 (int.dvd_nat_abs.2 haz)
| -[1+k] haz :=
  have haz' : (↑a:ℤ) ∣ (↑(k+1):ℤ), from dvd_of_dvd_neg haz,
  int.coe_nat_dvd.1 haz'

theorem dvd_antisymm {a b : ℤ} (H1 : 0 ≤ a) (H2 : 0 ≤ b) : a ∣ b → b ∣ a → a = b :=
begin
  rw [← abs_of_nonneg H1, ← abs_of_nonneg H2, abs_eq_nat_abs, abs_eq_nat_abs],
  rw [coe_nat_dvd, coe_nat_dvd, coe_nat_inj'],
  apply nat.dvd_antisymm
end

end int
