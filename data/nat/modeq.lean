/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Modular equality relation.
-/
import data.int.gcd

namespace nat

/-- Modular equality. `modeq n a b`, or `a ≡ b [MOD n]`, means
  that `a - b` is a multiple of `n`. -/
def modeq (n a b : ℕ) := a % n = b % n

notation a ` ≡ `:50 b ` [MOD `:50 n `]`:0 := modeq n a b

namespace modeq
variables {n m a b c d : ℕ}

@[refl] protected theorem refl (a : ℕ) : a ≡ a [MOD n] := @rfl _ _

@[symm] protected theorem symm : a ≡ b [MOD n] → b ≡ a [MOD n] := eq.symm

@[trans] protected theorem trans : a ≡ b [MOD n] → b ≡ c [MOD n] → a ≡ c [MOD n] := eq.trans

instance : decidable (a ≡ b [MOD n]) := by unfold modeq; apply_instance

theorem modeq_zero_iff : a ≡ 0 [MOD n] ↔ n ∣ a :=
by rw [modeq, zero_mod, dvd_iff_mod_eq_zero]

theorem modeq_iff_dvd : a ≡ b [MOD n] ↔ (n:ℤ) ∣ b - a :=
by rw [modeq, eq_comm, ← int.coe_nat_inj'];
   simp [int.mod_eq_mod_iff_mod_sub_eq_zero, int.dvd_iff_mod_eq_zero]

theorem modeq_of_dvd : (n:ℤ) ∣ b - a → a ≡ b [MOD n] := modeq_iff_dvd.2
theorem dvd_of_modeq : a ≡ b [MOD n] → (n:ℤ) ∣ b - a := modeq_iff_dvd.1

theorem mod_modeq (a n) : a % n ≡ a [MOD n] := nat.mod_mod _ _

theorem modeq_of_dvd_of_modeq (d : m ∣ n) (h : a ≡ b [MOD n]) : a ≡ b [MOD m] :=
modeq_of_dvd $ dvd_trans (int.coe_nat_dvd.2 d) (dvd_of_modeq h)

theorem modeq_mul_left' (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD (c * n)] :=
by unfold modeq at *; rw [mul_mod_mul_left, mul_mod_mul_left, h]

theorem modeq_mul_left (c : ℕ) (h : a ≡ b [MOD n]) : c * a ≡ c * b [MOD n] :=
modeq_of_dvd_of_modeq (dvd_mul_left _ _) $ modeq_mul_left' _ h

theorem modeq_mul_right' (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD (n * c)] :=
by rw [mul_comm a, mul_comm b, mul_comm n]; exact modeq_mul_left' c h

theorem modeq_mul_right (c : ℕ) (h : a ≡ b [MOD n]) : a * c ≡ b * c [MOD n] :=
by rw [mul_comm a, mul_comm b]; exact modeq_mul_left c h

theorem modeq_mul (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a * c ≡ b * d [MOD n] :=
(modeq_mul_left _ h₂).trans (modeq_mul_right _ h₁)

theorem modeq_add (h₁ : a ≡ b [MOD n]) (h₂ : c ≡ d [MOD n]) : a + c ≡ b + d [MOD n] :=
modeq_of_dvd $ by simpa using dvd_add (dvd_of_modeq h₁) (dvd_of_modeq h₂)

theorem modeq_add_cancel_left (h₁ : a ≡ b [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) : c ≡ d [MOD n] :=
have (n:ℤ) ∣ a + (-a + (d + -c)),
by simpa using _root_.dvd_sub (dvd_of_modeq h₂) (dvd_of_modeq h₁),
modeq_of_dvd $ by rwa add_neg_cancel_left at this

theorem modeq_add_cancel_right (h₁ : c ≡ d [MOD n]) (h₂ : a + c ≡ b + d [MOD n]) : a ≡ b [MOD n] :=
by rw [add_comm a, add_comm b] at h₂; exact modeq_add_cancel_left h₁ h₂

theorem modeq_of_modeq_mul_left (m : ℕ) (h : a ≡ b [MOD m * n]) : a ≡ b [MOD n] :=
by rw [modeq_iff_dvd] at *; exact dvd.trans (dvd_mul_left (n : ℤ) (m : ℤ)) h

theorem modeq_of_modeq_mul_right (m : ℕ) : a ≡ b [MOD n * m] → a ≡ b [MOD n] :=
mul_comm m n ▸ modeq_of_modeq_mul_left _

def chinese_remainder (co : coprime n m) (a b : ℕ) : {k // k ≡ a [MOD n] ∧ k ≡ b [MOD m]} :=
⟨let (c, d) := xgcd n m in int.to_nat ((b * c * n + a * d * m) % (n * m)), begin
  rw xgcd_val, dsimp [chinese_remainder._match_1],
  rw [modeq_iff_dvd, modeq_iff_dvd],
  rw [int.to_nat_of_nonneg], swap,
  { by_cases h₁ : n = 0, {simp [coprime, h₁] at co, substs m n, simp},
    by_cases h₂ : m = 0, {simp [coprime, h₂] at co, substs m n, simp},
    exact int.mod_nonneg _
      (mul_ne_zero (int.coe_nat_ne_zero.2 h₁) (int.coe_nat_ne_zero.2 h₂)) },
  have := gcd_eq_gcd_ab n m, simp [co.gcd_eq_one, mul_comm] at this,
  rw [int.mod_def, ← sub_add, ← sub_add]; split,
  { refine dvd_add _ (dvd_trans (dvd_mul_right _ _) (dvd_mul_right _ _)),
    rw [add_comm, ← sub_sub], refine _root_.dvd_sub _ (dvd_mul_left _ _),
    have := congr_arg ((*) ↑a) this,
    exact ⟨_, by rwa [mul_add, ← mul_assoc, ← mul_assoc, mul_one, mul_comm,
        ← sub_eq_iff_eq_add] at this⟩ },
  { refine dvd_add _ (dvd_trans (dvd_mul_left _ _) (dvd_mul_right _ _)),
    rw [← sub_sub], refine _root_.dvd_sub _ (dvd_mul_left _ _),
    have := congr_arg ((*) ↑b) this,
    exact ⟨_, by rwa [mul_add, ← mul_assoc, ← mul_assoc, mul_one, mul_comm _ ↑m,
        ← sub_eq_iff_eq_add'] at this⟩ }
end⟩

end modeq

@[simp] lemma mod_mul_right_mod (a b c : ℕ) : a % (b * c) % b = a % b :=
modeq.modeq_of_modeq_mul_right _ (modeq.mod_modeq _ _)

@[simp] lemma mod_mul_left_mod (a b c : ℕ) : a % (b * c) % c = a % c :=
modeq.modeq_of_modeq_mul_left _ (modeq.mod_modeq _ _)

end nat
