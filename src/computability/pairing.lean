/-
Copyright (c) 2022 Praneeth Kolichala. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Praneeth Kolichala
-/
import data.num.encode_list_bool
import data.list.basic

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

-- TODO: move this to `list.basic`

lemma after_spec {α : Type*} (p : α → Prop) [decidable_pred p]
  (as : list α) (x : α) (xs : list α) (has : ∀ a ∈ as, ¬ p a) (hx : p x) :
  (as ++ x :: xs).after p = xs :=
begin
  induction as with hd tl ih, { simp [after, hx], },
  simp [after, has hd, ih (λ a ha, has a (or.inr ha))],
end

lemma take_while_spec {α : Type*} (p : α → Prop) [decidable_pred p]
  (as : list α) (x : α) (xs : list α) (has : ∀ a ∈ as, p a) (hx : ¬ p x) :
  (as ++ x :: xs).take_while p = as :=
begin
  induction as with hd tl ih, { simp [take_while, hx], },
  simp [take_while, has hd, ih (λ a ha, has a (or.inr ha))],
end

lemma after_sublist {α : Type*} (p : α → Prop) [decidable_pred p] (xs : list α) :
  xs.after p <+ xs :=
begin
  induction xs, { refl, },
  simp only [after], split_ifs; apply sublist.cons, { refl, }, { assumption, }
end

lemma after_sublist_strict {α : Type*} (p : α → Prop) [decidable_pred p] (x : α) (xs : list α) :
  (x :: xs).after p <+ xs :=
by { simp only [after], split_ifs, { refl, }, { apply after_sublist, } }

lemma after_length_lt {α : Type*} (p : α → Prop) [decidable_pred p] {xs : list α} :
  (xs.after p).length < xs.length ↔ 0 < xs.length :=
⟨pos_of_gt, by { cases xs, { simp, },
  intro, simpa [nat.lt_succ_iff] using length_le_of_sublist (after_sublist_strict p _ _), }⟩

lemma last'_eq_head'_reverse {α : Type*} (xs : list α) :
  xs.last' = xs.reverse.head' :=
by apply reverse_cases_on xs; simp

/-- A preliminary pairing function.
This encodes (a, b) as a unary encoding of the length of `a` followed by `a ++ b`. -/
def mkpair' (a b : list bool) : list bool :=
(repeat ff a.length) ++ (tt :: (a ++ b))

/-- Left inverse to `list.mkpair'` -/
def unpair' (x : list bool) : list bool × list bool :=
(x.after (=tt)).split_at (x.take_while (=ff)).length

@[simp] lemma unpair'_mkpair' (a b : list bool) : unpair' (mkpair' a b) = (a, b) :=
begin
  simp only [unpair'],
  have h₁ : (mkpair' a b).after (=tt) = a ++ b,
  { apply after_spec, { simp [mem_repeat], }, { refl, }, },
  have h₂ : ((mkpair' a b).take_while (=ff)).length = a.length,
  { erw take_while_spec, { apply length_repeat, }, { simp [mem_repeat], }, trivial, },
  simp [h₁, h₂],
end

/-- Size bound for `mkpair'`: `|(a, b)| = O(|a|) + |b|` -/
@[simp] lemma mkpair'_length (a b : list bool) : (mkpair' a b).length = 2*a.length + b.length + 1 :=
by { simp [mkpair'], ring, }

/-- The efficient pairing function on `list bool`'s.
This function encodes (a, b) as a unary encoding of the number of bits in `a.length`, followed
by `a.length`, followed by `a ++ b`. -/
def mkpair (a b : list bool) : list bool :=
mkpair' (num.encode_num a.length) (a ++ b)

/-- Left inverse to `list.mkpair` -/
def unpair (ls : list bool) : list bool × list bool :=
(unpair' ls).2.split_at (num.decode_num (unpair' ls).1)

@[simp] lemma unpair_mkpair (a b : list bool) : unpair (mkpair a b) = (a, b) :=
by simp [unpair, mkpair]

lemma mkpair_length (a b : list bool) : (mkpair a b).length =
  if a.length = 0 then b.length + 1 else 2*(nat.log 2 a.length) + a.length + b.length + 3 :=
by { split_ifs with h; simp [mkpair, num.encode_num_len, h], ring, }

/-- Size bound for `mkpair'`: `|(a, b)| = |a| + |b| + O(log |a|)` -/
lemma mkpair_length_le (a b : list bool) :
  (mkpair a b).length ≤ 2*(nat.log 2 a.length) + a.length + b.length + 3 :=
by { rw mkpair_length, split_ifs; linarith, }

/-- A nice coincidence in our choice of pairing function: if `a` and `b` have most significant
bit `1`, then so does `mkpair' a b`. This allows for easy encoding of nat's in the standard way -/
lemma mkpair_mem_num_encode_range {a b : list bool}
  (h₁ : b ∈ set.range num.encode_num) (h₂ : b = [] → a ∈ set.range num.encode_num) :
  a.mkpair b ∈ set.range num.encode_num :=
begin
  simp only [mkpair, mkpair', num.mem_encode_range_iff] at ⊢ h₁ h₂,
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
open num (encode_num decode_num)

/-- Efficient pairing function on ℕ, where result has size log(a) + log(b) + O(log log a) bits -/
def mkpair' (a b : ℕ) : ℕ :=
decode_num (list.mkpair (encode_num a) (encode_num b))

/-- Unpairing function for `mkpair'` -/
def unpair' (n : ℕ) : ℕ × ℕ :=
(decode_num (list.unpair (encode_num n)).1, decode_num (list.unpair (encode_num n)).2)

@[simp] lemma unpair'_mkpair' (a b : ℕ) : unpair' (mkpair' a b) = (a, b) :=
begin
  simp only [unpair', mkpair', num.of_to_nat],
  rw num.encode_decode_list_bool_valid, { simp, },
  exact list.mkpair_mem_num_encode_range (set.mem_range_self _) (λ _, set.mem_range_self _),
end

lemma mkpair'_zero (a : ℕ) : mkpair' 0 a = bit1 a :=
by simp [mkpair', list.mkpair, list.mkpair']

lemma mkpair'_one (a : ℕ) : mkpair' 1 a = bit0 (bit1 (bit1 (bit1 a))) :=
by { simp [mkpair', list.mkpair, list.mkpair', encode_num, (show 1 = num.pos 1, from rfl)], }

lemma mkpair'_ne_zero (a b : ℕ) : mkpair' a b ≠ 0 :=
by { simp only [mkpair', list.mkpair, list.mkpair'], norm_cast, simp, }

lemma unpair'_fst_lt (n : ℕ) : (unpair' n.succ).1 < n.succ :=
begin
  convert_to (unpair' n.succ).1 < decode_num (encode_num n.succ), { simp, },
  apply num.decode_num_strict_mono,
  apply list.unpair_fst_len_lt, simp, norm_cast, simp,
end

lemma unpair'_snd_lt (n : ℕ) : (unpair' n.succ).2 < n.succ :=
begin
  convert_to (unpair' n.succ).2 < decode_num (encode_num n.succ), { simp, },
  apply num.decode_num_strict_mono,
  apply list.unpair_snd_len_lt, simp, norm_cast, simp,
end

/-- Size bound for `mkpair'`: `log₂ (mkpair' a b) = log₂ a + log₂ b + O(log log a) `-/
lemma mkpair'_le (a b : ℕ) : nat.log 2 (mkpair' a b) ≤
  log 2 a + log 2 b + 2 * log 2 (log 2 a + 1) + 5 :=
calc log 2 (decode_num (list.mkpair (encode_num a) (encode_num b)))
    ≤ log 2 (2^((list.mkpair (encode_num a) (encode_num b)).length) - 1) :
      by { apply log_monotone, apply le_pred_of_lt, apply num.decode_num_lt, }
... ≤ (list.mkpair (encode_num a) (encode_num b)).length :
      by { conv_rhs { rw ← log_pow (show 1 < 2, by norm_num) (list.mkpair _ _).length },
           apply log_monotone, exact tsub_le_self, }
... ≤ 2*(log 2 (encode_num a).length) + (encode_num a).length + (encode_num b).length + 3 :
      list.mkpair_length_le _ _
... ≤ 2*(log 2 (log 2 a + 1)) + (log 2 a + 1) + (log 2 b + 1) + 3 :
      by { mono*, all_goals { try { apply log_monotone }, try { exact zero_le _, }, },
           all_goals { convert num.encode_num_len_le _, simp, }, }
... = _ : by ring_nf

end nat
