/-
Copyright (c) 2020 Patrick Stevens. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Patrick Stevens, Yury Kudryashov
-/
import algebra.big_operators.associated
import data.nat.choose.sum
import data.nat.choose.dvd
import data.nat.parity
import data.nat.prime

/-!
# Primorial

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file defines the primorial function (the product of primes less than or equal to some bound),
and proves that `primorial n ≤ 4 ^ n`.

## Notations

We use the local notation `n#` for the primorial of `n`: that is, the product of the primes less
than or equal to `n`.
-/

open finset
open nat
open_locale big_operators nat

/-- The primorial `n#` of `n` is the product of the primes less than or equal to `n`.
-/
def primorial (n : ℕ) : ℕ := ∏ p in (filter nat.prime (range (n + 1))), p
local notation x`#` := primorial x

lemma primorial_pos (n : ℕ) : 0 < n# :=
prod_pos $ λ p hp, (mem_filter.1 hp).2.pos

lemma primorial_succ {n : ℕ} (hn1 : n ≠ 1) (hn : odd n) : (n + 1)# = n# :=
begin
  refine prod_congr _ (λ _ _, rfl),
  rw [range_succ, filter_insert, if_neg (λ h, odd_iff_not_even.mp hn _)],
  exact (h.even_sub_one $ mt succ.inj hn1)
end

lemma primorial_add (m n : ℕ) :
  (m + n)# = m# * ∏ p in filter nat.prime (Ico (m + 1) (m + n + 1)), p :=
begin
  rw [primorial, primorial, ← Ico_zero_eq_range, ← prod_union, ← filter_union,
    Ico_union_Ico_eq_Ico],
  exacts [zero_le _, add_le_add_right (nat.le_add_right _ _) _,
    disjoint_filter_filter $ Ico_disjoint_Ico_consecutive _ _ _]
end

lemma primorial_add_dvd {m n : ℕ} (h : n ≤ m) : (m + n)# ∣ m# * choose (m + n) m :=
calc (m + n)# = m# * ∏ p in filter nat.prime (Ico (m + 1) (m + n + 1)), p :
  primorial_add _ _
... ∣ m# * choose (m + n) m :
  mul_dvd_mul_left _ $ prod_primes_dvd _ (λ k hk, (mem_filter.1 hk).2.prime) $ λ p hp,
    begin
      rw [mem_filter, mem_Ico] at hp,
      exact hp.2.dvd_choose_add hp.1.1 (h.trans_lt (m.lt_succ_self.trans_le hp.1.1))
        (nat.lt_succ_iff.1 hp.1.2)
    end

lemma primorial_add_le {m n : ℕ} (h : n ≤ m) : (m + n)# ≤ m# * choose (m + n) m :=
le_of_dvd (mul_pos (primorial_pos _) (choose_pos $ nat.le_add_right _ _)) (primorial_add_dvd h)

lemma primorial_le_4_pow (n : ℕ) : n# ≤ 4 ^ n :=
begin
  induction n using nat.strong_induction_on with n ihn,
  cases n, { refl },
  rcases n.even_or_odd with (⟨m, rfl⟩ | ho),
  { rcases m.eq_zero_or_pos with rfl | hm, { dec_trivial },
    calc (m + m + 1)# = (m + 1 + m)# : by rw [add_right_comm]
    ... ≤ (m + 1)# * choose (m + 1 + m) (m + 1) : primorial_add_le m.le_succ
    ... = (m + 1)# * choose (2 * m + 1) m : by rw [choose_symm_add, two_mul, add_right_comm]
    ... ≤ 4 ^ (m + 1) * 4 ^ m :
      mul_le_mul' (ihn _ $ succ_lt_succ $ (lt_add_iff_pos_left _).2 hm) (choose_middle_le_pow _)
    ... ≤ 4 ^ (m + m + 1) : by rw [← pow_add, add_right_comm] },
  { rcases decidable.eq_or_ne n 1 with rfl | hn,
    { dec_trivial },
    { calc (n + 1)# = n# : primorial_succ hn ho
      ... ≤ 4 ^ n : ihn n n.lt_succ_self
      ... ≤ 4 ^ (n + 1) : pow_le_pow_of_le_right  four_pos n.le_succ } }
end
