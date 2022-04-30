/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import data.num.to_bits
import data.list.basic
import tactic.ring

/-!
# Efficient Pairing

One issue with the standard `nat.mkpair` is that it isn't suitable for polytime encoding.
While the pairing function itself runs in polynomial time, repeated applications of it
(even only polynomially many) can cause the result to blow up exponentially. Therefore, we cannot
e.g. create lists by encoding `[a, b, c, ...] = (a, (b, (c, ...)))` in polynomial time.

This file defines an efficient pairing function. We first define a pairing function
on lists which take `list bool`'s of `a` and `b`, and outputs an encoding of `(a, b)`,
which has size `a.length + b.length + O(log a.length)` (so only logarithmic overhead in the first
argument). We then extend this to `nat`'s using `encode_num`.

## Main definitions

### List pairing
  - `list.mkpair'` - Encodes a pair of `list bool`'s with linear overhead i.e.
      `|(a, b)| = O(|a|) + |b|`, where `|a|` denotes the size of list `a`.
  - `list.mkpair` - Encodes a pair of `list bool`'s with logarithmic overhead i.e.
      `|(a, b)| = |a| + |b| + O(log |a|)`

### Nat pairing
  - `nat.mkpair'` Encodes a pair of natural numbers with logarithmic overhead i.e.
      `log₂ (nat.mkpair a b) = log₂ a + log₂ b + O(log log a)`
-/

namespace list

/-- A preliminary pairing function.
This encodes (a, b) as a unary encoding of the length of `a` followed by `a ++ b`. -/
def mkpair' (a b : list bool) : list bool :=
(repeat ff a.length) ++ (tt :: (a ++ b))

/-- Left inverse to `list.mkpair'` -/
def unpair' (x : list bool) : list bool × list bool :=
(x.after (=tt)).split_at (x.take_while (=ff)).length

@[simp] lemma unpair'_mkpair' (a b : list bool) : unpair' (mkpair' a b) = (a, b) :=
begin
  have h₁ : (mkpair' a b).after (=tt) = a ++ b,
  { apply after_spec, { simp [mem_repeat], }, { refl, }, },
  have h₂ : ((mkpair' a b).take_while (=ff)).length = a.length,
  { erw take_while_spec, { apply length_repeat, }, { simp [mem_repeat], }, trivial, },
  simp [unpair', h₁, h₂],
end

/-- Size bound for `mkpair'`: `|(a, b)| = O(|a|) + |b|` -/
@[simp] lemma mkpair'_length (a b : list bool) : (mkpair' a b).length = 2*a.length + b.length + 1 :=
by { simp [mkpair'], ring, }

/-- The efficient pairing function on `list bool`'s.
This function encodes (a, b) as a unary encoding of the number of bits in `a.length`, followed
by `a.length`, followed by `a ++ b`. -/
def mkpair (a b : list bool) : list bool :=
mkpair' (num.to_bits a.length) (a ++ b)

/-- Left inverse to `list.mkpair` -/
def unpair (ls : list bool) : list bool × list bool :=
(unpair' ls).2.split_at (num.of_bits (unpair' ls).1)

@[simp] lemma unpair_mkpair (a b : list bool) : unpair (mkpair a b) = (a, b) :=
by simp [unpair, mkpair]

lemma mkpair_length (a b : list bool) : (mkpair a b).length =
  if a.length = 0 then b.length + 1 else 2*(nat.log 2 a.length) + a.length + b.length + 3 :=
by { split_ifs with h; simp [mkpair, num.to_bits_len, h], ring, }

/-- Size bound for `mkpair'`: `|(a, b)| = |a| + |b| + O(log |a|)` -/
lemma mkpair_length_le (a b : list bool) :
  (mkpair a b).length ≤ 2*(nat.log 2 a.length) + a.length + b.length + 3 :=
by { rw mkpair_length, split_ifs; linarith, }

/-- A nice coincidence in our choice of pairing function: if `a` and `b` have most significant
bit `1`, then so does `mkpair' a b`. This allows for easy encoding of nat's in the standard way -/
lemma mkpair_mem_num_encode_range {a b : list bool}
  (h₁ : b ∈ set.range num.to_bits) (h₂ : b = [] → a ∈ set.range num.to_bits) :
  a.mkpair b ∈ set.range num.to_bits :=
begin
  simp only [mkpair, mkpair', num.mem_to_bits_range_iff] at ⊢ h₁ h₂,
  induction b using list.reverse_cases_on with st lt, swap,
  { simpa [last'_eq_head'_reverse] using h₁, },
  induction a using list.reverse_cases_on with st lt, swap,
  { simpa [last'_eq_head'_reverse] using h₂, },
  right, simp,
end

lemma unpair_fst_len_lt (a : list bool) (ha : a ≠ []) : a.unpair.1.length < a.length :=
begin
  simp only [unpair, unpair', drop_drop, length_drop, length_take, split_at_eq_take_drop],
  rcases a with _|_|_, { simp at ha, contradiction, }, all_goals { clear ha },
  { simp only [min_lt_iff], right, apply nat.lt_of_le_of_lt (nat.sub_le _ _),
    simpa [after, nat.lt_succ_iff] using length_le_of_sublist (after_sublist _ _), },
  { simp only [min_lt_iff], left, simp [take_while], },
end

lemma unpair_snd_len_lt (a : list bool) (ha : a ≠ []) : a.unpair.2.length < a.length :=
begin
  simp only [unpair, unpair', drop_drop, split_at_eq_take_drop, length_drop],
  apply lt_of_le_of_lt (nat.sub_le _ _),
  rwa [after_length_lt, length_pos_iff_ne_nil],
end

end list

namespace nat
open num (to_bits of_bits)

/-- Efficient pairing function on ℕ, where result has size log(a) + log(b) + O(log log a) bits -/
def mkpair' (a b : ℕ) : ℕ :=
of_bits (list.mkpair (to_bits a) (to_bits b))

/-- Unpairing function for `mkpair'` -/
def unpair' (n : ℕ) : ℕ × ℕ :=
(of_bits (list.unpair (to_bits n)).1, of_bits (list.unpair (to_bits n)).2)

@[simp] lemma unpair'_mkpair' (a b : ℕ) : unpair' (mkpair' a b) = (a, b) :=
begin
  simp only [unpair', mkpair', num.of_to_nat],
  rw num.to_bits_of_bits_valid, { simp, },
  exact list.mkpair_mem_num_encode_range (set.mem_range_self _) (λ _, set.mem_range_self _),
end

lemma mkpair'_zero (a : ℕ) : mkpair' 0 a = bit1 a :=
by simp [mkpair', list.mkpair, list.mkpair']

lemma mkpair'_one (a : ℕ) : mkpair' 1 a = bit0 (bit1 (bit1 (bit1 a))) :=
by { simp [mkpair', list.mkpair, list.mkpair', to_bits, (show 1 = num.pos 1, from rfl)], }

lemma mkpair'_ne_zero (a b : ℕ) : mkpair' a b ≠ 0 :=
by { simp only [mkpair', list.mkpair, list.mkpair'], norm_cast, simp, }

lemma unpair'_fst_lt (n : ℕ) : (unpair' n.succ).1 < n.succ :=
begin
  convert_to (unpair' n.succ).1 < of_bits (to_bits n.succ), { simp, },
  apply num.of_bits_strict_mono,
  apply list.unpair_fst_len_lt, simp, norm_cast, simp,
end

lemma unpair'_snd_lt (n : ℕ) : (unpair' n.succ).2 < n.succ :=
begin
  convert_to (unpair' n.succ).2 < of_bits (to_bits n.succ), { simp, },
  apply num.of_bits_strict_mono,
  apply list.unpair_snd_len_lt, simp, norm_cast, simp,
end

/-- Size bound for `mkpair'`: `log₂ (mkpair' a b) = log₂ a + log₂ b + O(log log a) `-/
lemma mkpair'_le (a b : ℕ) : log 2 (mkpair' a b) ≤
  log 2 a + log 2 b + 2 * log 2 (log 2 a + 1) + 5 :=
calc log 2 (of_bits (list.mkpair (to_bits a) (to_bits b)))
    ≤ log 2 (2^((list.mkpair (to_bits a) (to_bits b)).length) - 1) :
      by { apply log_monotone, apply le_pred_of_lt, apply num.of_bits_lt, }
... ≤ (list.mkpair (to_bits a) (to_bits b)).length :
      by { conv_rhs { rw ← log_pow (show 1 < 2, by norm_num) (list.mkpair _ _).length },
           apply log_monotone, exact tsub_le_self, }
... ≤ 2*(log 2 (to_bits a).length) + (to_bits a).length + (to_bits b).length + 3 :
      list.mkpair_length_le _ _
... ≤ 2*(log 2 (log 2 a + 1)) + (log 2 a + 1) + (log 2 b + 1) + 3 :
      by { mono*, all_goals { try { apply log_monotone }, try { exact zero_le _, }, },
           all_goals { convert num.to_bits_len_le _, simp, }, }
... = _ : by ring_nf

end nat
