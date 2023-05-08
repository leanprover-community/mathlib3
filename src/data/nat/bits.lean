/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import data.nat.basic

/-!
# Additional properties of binary recursion on `nat`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file documents additional properties of binary recursion,
which allows us to more easily work with operations which do depend
on the number of leading zeros in the binary representation of `n`.
For example, we can more easily work with `nat.bits` and `nat.size`.

See also: `nat.bitwise`, `nat.pow` (for various lemmas about `size` and `shiftl`/`shiftr`),
and `nat.digits`.
-/

namespace nat

universe u
variables {n : ℕ}

/-! ### `bodd_div2` and `bodd` -/

@[simp] theorem bodd_div2_eq (n : ℕ) : bodd_div2 n = (bodd n, div2 n) :=
by unfold bodd div2; cases bodd_div2 n; refl

@[simp] lemma bodd_bit0 (n) : bodd (bit0 n) = ff := bodd_bit ff n
@[simp] lemma bodd_bit1 (n) : bodd (bit1 n) = tt := bodd_bit tt n

@[simp] lemma div2_bit0 (n) : div2 (bit0 n) = n := div2_bit ff n
@[simp] lemma div2_bit1 (n) : div2 (bit1 n) = n := div2_bit tt n

/-! ### `bit0` and `bit1` -/

-- There is no need to prove `bit0_eq_zero : bit0 n = 0 ↔ n = 0`
-- as this is true for any `[semiring R] [no_zero_divisors R] [char_zero R]`

-- However the lemmas `bit0_eq_bit0`, `bit1_eq_bit1`, `bit1_eq_one`, `one_eq_bit1`
-- need `[ring R] [no_zero_divisors R] [char_zero R]` in general,
-- so we prove `ℕ` specialized versions here.
@[simp] lemma bit0_eq_bit0 {m n : ℕ} : bit0 m = bit0 n ↔ m = n :=
⟨nat.bit0_inj, λ h, by subst h⟩

@[simp] lemma bit1_eq_bit1 {m n : ℕ} : bit1 m = bit1 n ↔ m = n :=
⟨nat.bit1_inj, λ h, by subst h⟩

@[simp] lemma bit1_eq_one {n : ℕ} : bit1 n = 1 ↔ n = 0 :=
⟨@nat.bit1_inj n 0, λ h, by subst h⟩
@[simp] lemma one_eq_bit1 {n : ℕ} : 1 = bit1 n ↔ n = 0 :=
⟨λ h, (@nat.bit1_inj 0 n h).symm, λ h, by subst h⟩

theorem bit_add : ∀ (b : bool) (n m : ℕ), bit b (n + m) = bit ff n + bit b m
| tt := bit1_add
| ff := bit0_add

theorem bit_add' : ∀ (b : bool) (n m : ℕ), bit b (n + m) = bit b n + bit ff m
| tt := bit1_add'
| ff := bit0_add

theorem bit_ne_zero (b) {n} (h : n ≠ 0) : bit b n ≠ 0 :=
by cases b; [exact nat.bit0_ne_zero h, exact nat.bit1_ne_zero _]

lemma bit0_mod_two : bit0 n % 2 = 0 := by { rw nat.mod_two_of_bodd, simp }

lemma bit1_mod_two : bit1 n % 2 = 1 := by { rw nat.mod_two_of_bodd, simp }

lemma pos_of_bit0_pos {n : ℕ} (h : 0 < bit0 n) : 0 < n :=
by { cases n, cases h, apply succ_pos, }

@[simp] lemma bit_cases_on_bit {C : ℕ → Sort u} (H : Π b n, C (bit b n)) (b : bool) (n : ℕ) :
  bit_cases_on (bit b n) H = H b n :=
eq_of_heq $ (eq_rec_heq _ _).trans $ by rw [bodd_bit, div2_bit]

@[simp] lemma bit_cases_on_bit0 {C : ℕ → Sort u} (H : Π b n, C (bit b n)) (n : ℕ) :
  bit_cases_on (bit0 n) H = H ff n :=
bit_cases_on_bit H ff n

@[simp] lemma bit_cases_on_bit1 {C : ℕ → Sort u} (H : Π b n, C (bit b n)) (n : ℕ) :
  bit_cases_on (bit1 n) H = H tt n :=
bit_cases_on_bit H tt n

lemma bit_cases_on_injective {C : ℕ → Sort u} :
  function.injective (λ H : Π b n, C (bit b n), λ n, bit_cases_on n H) :=
begin
  intros H₁ H₂ h,
  ext b n,
  simpa only [bit_cases_on_bit] using congr_fun h (bit b n)
end

@[simp] lemma bit_cases_on_inj {C : ℕ → Sort u} (H₁ H₂ : Π b n, C (bit b n)) :
  (λ n, bit_cases_on n H₁) = (λ n, bit_cases_on n H₂) ↔ H₁ = H₂ :=
bit_cases_on_injective.eq_iff

protected lemma bit0_eq_zero {n : ℕ} : bit0 n = 0 ↔ n = 0 :=
⟨nat.eq_zero_of_add_eq_zero_left, λ h, by simp [h]⟩

lemma bit_eq_zero_iff {n : ℕ} {b : bool} : bit b n = 0 ↔ n = 0 ∧ b = ff :=
by { split, { cases b; simp [nat.bit, nat.bit0_eq_zero], }, rintro ⟨rfl, rfl⟩, refl, }

/-- The same as binary_rec_eq, but that one unfortunately requires `f` to be the identity when
  appending `ff` to `0`. Here, we allow you to explicitly say that that case is not happening, i.e.
  supplying `n = 0 → b = tt`. -/
lemma binary_rec_eq' {C : ℕ → Sort*} {z : C 0} {f : ∀ b n, C n → C (bit b n)}
  (b n) (h : f ff 0 z = z ∨ (n = 0 → b = tt)) :
  binary_rec z f (bit b n) = f b n (binary_rec z f n) :=
begin
  rw [binary_rec],
  split_ifs with h',
  { rcases bit_eq_zero_iff.mp h' with ⟨rfl, rfl⟩,
    rw binary_rec_zero,
    simp only [imp_false, or_false, eq_self_iff_true, not_true] at h,
    exact h.symm },
  { generalize_proofs e, revert e,
    rw [bodd_bit, div2_bit],
    intros, refl, }
end

/-- The same as `binary_rec`, but the induction step can assume that if `n=0`,
  the bit being appended is `tt`-/
@[elab_as_eliminator]
def binary_rec' {C : ℕ → Sort*} (z : C 0) (f : ∀ b n, (n = 0 → b = tt) → C n → C (bit b n)) :
  ∀ n, C n :=
binary_rec z (λ b n ih, if h : n = 0 → b = tt then f b n h ih else
  by { convert z, rw bit_eq_zero_iff, simpa using h, })

/-- The same as `binary_rec`, but special casing both 0 and 1 as base cases -/
@[elab_as_eliminator]
def binary_rec_from_one {C : ℕ → Sort*} (z₀ : C 0) (z₁ : C 1)
  (f : ∀ b n, n ≠ 0 → C n → C (bit b n)) : ∀ n, C n :=
binary_rec' z₀ (λ b n h ih, if h' : n = 0 then by { rw [h', h h'], exact z₁ } else f b n h' ih)

@[simp] lemma zero_bits : bits 0 = [] := by simp [nat.bits]

@[simp] lemma bits_append_bit (n : ℕ) (b : bool) (hn : n = 0 → b = tt) :
  (bit b n).bits = b :: n.bits :=
by { rw [nat.bits, binary_rec_eq'], simpa, }

@[simp] lemma bit0_bits (n : ℕ) (hn : n ≠ 0) : (bit0 n).bits = ff :: n.bits :=
bits_append_bit n ff (λ hn', absurd hn' hn)

@[simp] lemma bit1_bits (n : ℕ) : (bit1 n).bits = tt :: n.bits :=
bits_append_bit n tt (λ _, rfl)

@[simp] lemma one_bits : nat.bits 1 = [tt] := by { convert bit1_bits 0, simp, }

-- TODO Find somewhere this can live.
-- example : bits 3423 = [tt, tt, tt, tt, tt, ff, tt, ff, tt, ff, tt, tt] := by norm_num

lemma bodd_eq_bits_head (n : ℕ) : n.bodd = n.bits.head :=
begin
  induction n using nat.binary_rec' with b n h ih, { simp, },
  simp [bodd_bit, bits_append_bit _ _ h],
end

lemma div2_bits_eq_tail (n : ℕ) : n.div2.bits = n.bits.tail :=
begin
  induction n using nat.binary_rec' with b n h ih, { simp, },
  simp [div2_bit, bits_append_bit _ _ h],
end

end nat
