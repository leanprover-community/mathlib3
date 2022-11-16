/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import tactic.generalize_proofs
import tactic.norm_num

/-!
# Additional properties of binary recursion on `nat`

This file documents additional properties of binary recursion,
which allows us to more easily work with operations which do depend
on the number of leading zeros in the binary representation of `n`.
For example, we can more easily work with `nat.bits` and `nat.size`.

See also: `nat.bitwise`, `nat.pow` (for various lemmas about `size` and `shiftl`/`shiftr`),
and `nat.digits`.
-/

namespace nat

lemma bit_eq_zero_iff {n : ℕ} {b : bool} : bit b n = 0 ↔ n = 0 ∧ b = ff :=
by { split, { cases b; simp [nat.bit], }, rintro ⟨rfl, rfl⟩, refl, }

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

example : bits 3423 = [tt, tt, tt, tt, tt, ff, tt, ff, tt, ff, tt, tt] := by norm_num

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

lemma size_eq_bits_len (n : ℕ) : n.bits.length = n.size :=
begin
  induction n using nat.binary_rec' with b n h ih, { simp, },
  rw [size_bit, bits_append_bit _ _ h],
  { simp [ih], },
  { simpa [bit_eq_zero_iff], }
end

end nat
