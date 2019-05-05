/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Modular equality relation.
-/
import data.int.gcd algebra.ordered_ring

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

lemma modeq_and_modeq_iff_modeq_mul {a b m n : ℕ} (hmn : coprime m n) :
  a ≡ b [MOD m] ∧ a ≡ b [MOD n] ↔ (a ≡ b [MOD m * n]) :=
⟨λ h, begin
    rw [nat.modeq.modeq_iff_dvd, nat.modeq.modeq_iff_dvd, ← int.dvd_nat_abs,
      int.coe_nat_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd] at h,
    rw [nat.modeq.modeq_iff_dvd, ← int.dvd_nat_abs, int.coe_nat_dvd],
    exact hmn.mul_dvd_of_dvd_of_dvd h.1 h.2
  end,
λ h, ⟨nat.modeq.modeq_of_modeq_mul_right _ h, nat.modeq.modeq_of_modeq_mul_left _ h⟩⟩

lemma coprime_of_mul_modeq_one (b : ℕ) {a n : ℕ} (h : a * b ≡ 1 [MOD n]) : coprime a n :=
nat.coprime_of_dvd' (λ k ⟨ka, hka⟩ ⟨kb, hkb⟩, int.coe_nat_dvd.1 begin
  rw [hka, hkb, modeq_iff_dvd] at h,
  cases h with z hz,
  rw [sub_eq_iff_eq_add] at hz,
  rw [hz, int.coe_nat_mul, mul_assoc, mul_assoc, int.coe_nat_mul, ← mul_add],
  exact dvd_mul_right _ _,
end)

end modeq

@[simp] lemma mod_mul_right_mod (a b c : ℕ) : a % (b * c) % b = a % b :=
modeq.modeq_of_modeq_mul_right _ (modeq.mod_modeq _ _)

@[simp] lemma mod_mul_left_mod (a b c : ℕ) : a % (b * c) % c = a % c :=
modeq.modeq_of_modeq_mul_left _ (modeq.mod_modeq _ _)

lemma odd_mul_odd {n m : ℕ} (hn1 : n % 2 = 1) (hm1 : m % 2 = 1) : (n * m) % 2 = 1 :=
show (n * m) % 2 = (1 * 1) % 2, from nat.modeq.modeq_mul hn1 hm1

lemma odd_mul_odd_div_two {m n : ℕ} (hm1 : m % 2 = 1) (hn1 : n % 2 = 1) :
  (m * n) / 2 = m * (n / 2) + m / 2 :=
have hm0 : 0 < m := nat.pos_of_ne_zero (λ h, by simp * at *),
have hn0 : 0 < n := nat.pos_of_ne_zero (λ h, by simp * at *),
(nat.mul_left_inj (show 0 < 2, from dec_trivial)).1 $
by rw [mul_add, two_mul_odd_div_two hm1, mul_left_comm, two_mul_odd_div_two hn1,
  two_mul_odd_div_two (nat.odd_mul_odd hm1 hn1), nat.mul_sub_left_distrib, mul_one,
  ← nat.add_sub_assoc hm0, nat.sub_add_cancel (le_mul_of_ge_one_right' (nat.zero_le _) hn0)]

lemma odd_of_mod_four_eq_one {n : ℕ} (h : n % 4 = 1) : n % 2 = 1 :=
@modeq.modeq_of_modeq_mul_left 2 n 1 2 h

lemma odd_of_mod_four_eq_three {n : ℕ} (h : n % 4 = 3) : n % 2 = 1 :=
@modeq.modeq_of_modeq_mul_left 2 n 3 2 h

end nat

namespace list
variable {α : Type*}

lemma nth_rotate : ∀ {l : list α} {n m : ℕ} (hml : m < l.length),
  (l.rotate n).nth m = l.nth ((m + n) % l.length)
| []     n     m hml := (nat.not_lt_zero _ hml).elim
| l      0     m hml := by simp [nat.mod_eq_of_lt hml]
| (a::l) (n+1) m hml :=
have h₃ : m < list.length (l ++ [a]), by simpa using hml,
(lt_or_eq_of_le (nat.le_of_lt_succ $ nat.mod_lt (m + n)
  (lt_of_le_of_lt (nat.zero_le _) hml))).elim
(λ hml',
  have h₁ : (m + (n + 1)) % ((a :: l : list α).length) =
      (m + n) % ((a :: l : list α).length) + 1,
    from calc (m + (n + 1)) % (l.length + 1) =
      ((m + n) % (l.length + 1) + 1) % (l.length + 1) :
      add_assoc m n 1 ▸ nat.modeq.modeq_add (nat.mod_mod _ _).symm rfl
    ... = (m + n) % (l.length + 1) + 1 : nat.mod_eq_of_lt (nat.succ_lt_succ hml'),
  have h₂ : (m + n) % (l ++ [a]).length < l.length, by simpa [nat.add_one] using hml',
  by rw [list.rotate_cons_succ, nth_rotate h₃, list.nth_append h₂, h₁, list.nth]; simp)
(λ hml',
  have h₁ : (m + (n + 1)) % (l.length + 1) = 0,
    from calc (m + (n + 1)) % (l.length + 1) = (l.length + 1) % (l.length + 1) :
      add_assoc m n 1 ▸ nat.modeq.modeq_add
        (hml'.trans (nat.mod_eq_of_lt (nat.lt_succ_self _)).symm) rfl
    ... = 0 : by simp,
  have h₂ : l.length < (l ++ [a]).length, by simp [nat.lt_succ_self],
  by rw [list.length, list.rotate_cons_succ, nth_rotate h₃, list.length_append,
    list.length_cons, list.length, zero_add, hml', h₁, list.nth_concat_length]; refl)

lemma rotate_eq_self_iff_eq_repeat [hα : nonempty α] : ∀ {l : list α},
  (∀ n, l.rotate n = l) ↔ ∃ a, l = list.repeat a l.length
| []     := ⟨λ h, nonempty.elim hα (λ a, ⟨a, by simp⟩), by simp⟩
| (a::l) :=
⟨λ h, ⟨a, list.ext_le (by simp) $ λ n hn h₁,
  begin
    rw [← option.some_inj, ← list.nth_le_nth],
    conv {to_lhs, rw ← h ((list.length (a :: l)) - n)},
    rw [nth_rotate hn, nat.add_sub_cancel' (le_of_lt hn),
      nat.mod_self, nth_le_repeat _ hn], refl
  end⟩,
  λ ⟨a, ha⟩ n, ha.symm ▸ list.ext_le (by simp)
    (λ m hm h,
      have hm' : (m + n) % (list.repeat a (list.length (a :: l))).length < list.length (a :: l),
        by rw list.length_repeat; exact nat.mod_lt _ (nat.succ_pos _),
      by rw [nth_le_repeat, ← option.some_inj, ← list.nth_le_nth, nth_rotate h, list.nth_le_nth,
        nth_le_repeat]; simp * at *)⟩

end list