/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.computation.basic
import algebra.continued_fractions.translations
/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary

This is a collection of simple lemmas between the different structures used for the computation
of continued fractions defined in `algebra.continued_fractions.computation.basic`. The file consists
of three sections:
1. Recurrences and inversion lemmas for `int_fract_pair.stream`: these lemmas give us inversion
   rules and recurrences for the computation of the stream of integer and fractional parts of
   a value.
2. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
3. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`int_fract_pair.stream`, `int_fract_pair.seq1`, and
   `generalized_continued_fraction.of`) are connected, i.e. how the values are moved along the
   structures and the termination of one sequence implies the termination of another sequence.

## Main Theorems

- `succ_nth_stream_eq_some_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of non-termination.
- `succ_nth_stream_eq_none_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of termination.
- `nth_of_eq_some_of_succ_nth_int_fract_pair_stream` and
  `nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero` show how the entries of the sequence
  of the computed continued fraction can be obtained from the stream of integer and fractional
  parts.
-/

namespace generalized_continued_fraction
open generalized_continued_fraction (of)
open stream.seq as seq

/- Fix a discrete linear ordered floor field and a value `v`. -/
variables {K : Type*} [linear_ordered_field K] [floor_ring K] {v : K}

namespace int_fract_pair
/-!
### Recurrences and Inversion Lemmas for `int_fract_pair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/

lemma stream_zero (v : K) : int_fract_pair.stream v 0 = some (int_fract_pair.of v) := rfl

variable {n : ℕ}

lemma stream_eq_none_of_fr_eq_zero {ifp_n : int_fract_pair K}
  (stream_nth_eq : int_fract_pair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
  int_fract_pair.stream v (n + 1) = none :=
begin
  cases ifp_n with _ fr,
  change fr = 0 at nth_fr_eq_zero,
  simp [int_fract_pair.stream, stream_nth_eq, nth_fr_eq_zero]
end

/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
lemma succ_nth_stream_eq_none_iff : int_fract_pair.stream v (n + 1) = none
  ↔ (int_fract_pair.stream v n = none ∨ ∃ ifp, int_fract_pair.stream v n = some ifp ∧ ifp.fr = 0) :=
begin
  rw [int_fract_pair.stream],
  cases int_fract_pair.stream v n; simp [imp_false]
end

/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of non-termination.
-/
lemma succ_nth_stream_eq_some_iff {ifp_succ_n : int_fract_pair K} :
    int_fract_pair.stream v (n + 1) = some ifp_succ_n
  ↔ ∃ (ifp_n : int_fract_pair K), int_fract_pair.stream v n = some ifp_n
      ∧ ifp_n.fr ≠ 0
      ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n :=
by simp [int_fract_pair.stream, ite_eq_iff]

/--
An easier to use version of one direction of
`generalized_continued_fraction.int_fract_pair.succ_nth_stream_eq_some_iff`.
-/
lemma stream_succ_of_some {p : int_fract_pair K}
  (h : int_fract_pair.stream v n = some p) (h' : p.fr ≠ 0) :
  int_fract_pair.stream v (n + 1) = some (int_fract_pair.of (p.fr)⁻¹) :=
succ_nth_stream_eq_some_iff.mpr ⟨p, h, h', rfl⟩

/--
The stream of `int_fract_pair`s of an integer stops after the first term.
-/
lemma stream_succ_of_int (a : ℤ) (n : ℕ) : int_fract_pair.stream (a : K) (n + 1) = none :=
begin
  induction n with n ih,
  { refine int_fract_pair.stream_eq_none_of_fr_eq_zero (int_fract_pair.stream_zero (a : K)) _,
    simp only [int_fract_pair.of, int.fract_int_cast], },
  { exact int_fract_pair.succ_nth_stream_eq_none_iff.mpr (or.inl ih), }
end

lemma exists_succ_nth_stream_of_fr_zero {ifp_succ_n : int_fract_pair K}
  (stream_succ_nth_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n)
  (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
  ∃ ifp_n : int_fract_pair K, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
begin
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases (succ_nth_stream_eq_some_iff.mp stream_succ_nth_eq) with
    ⟨ifp_n, seq_nth_eq, nth_fr_ne_zero, rfl⟩,
  refine ⟨ifp_n, seq_nth_eq, _⟩,
  simpa only [int_fract_pair.of, int.fract, sub_eq_zero] using succ_nth_fr_eq_zero
end

/--
A recurrence relation that expresses the `(n+1)`th term of the stream of `int_fract_pair`s
of `v` for non-integer `v` in terms of the `n`th term of the stream associated to
the inverse of the fractional part of `v`.
-/
lemma stream_succ  (h : int.fract v ≠ 0) (n : ℕ) :
  int_fract_pair.stream v (n + 1) = int_fract_pair.stream (int.fract v)⁻¹ n :=
begin
  induction n with n ih,
  { have H : (int_fract_pair.of v).fr = int.fract v := rfl,
    rw [stream_zero, stream_succ_of_some (stream_zero v) (ne_of_eq_of_ne H h), H], },
  { cases eq_or_ne (int_fract_pair.stream (int.fract v)⁻¹ n) none with hnone hsome,
    { rw hnone at ih,
      rw [succ_nth_stream_eq_none_iff.mpr (or.inl hnone),
          succ_nth_stream_eq_none_iff.mpr (or.inl ih)], },
    { obtain ⟨p, hp⟩ := option.ne_none_iff_exists'.mp hsome,
      rw hp at ih,
      cases eq_or_ne p.fr 0 with hz hnz,
      { rw [stream_eq_none_of_fr_eq_zero hp hz, stream_eq_none_of_fr_eq_zero ih hz], },
      { rw [stream_succ_of_some hp hnz, stream_succ_of_some ih hnz], } } }
end

end int_fract_pair

section head
/-!
### Translation of the Head Term

Here we state some lemmas that show us that the head term of the computed continued fraction of a
value `v` is `⌊v⌋` and how this head term is moved along the structures used in the computation
process.
-/

/-- The head term of the sequence with head of `v` is just the integer part of `v`. -/
@[simp]
lemma int_fract_pair.seq1_fst_eq_of : (int_fract_pair.seq1 v).fst = int_fract_pair.of v := rfl

lemma of_h_eq_int_fract_pair_seq1_fst_b : (of v).h = (int_fract_pair.seq1 v).fst.b :=
by { cases aux_seq_eq : (int_fract_pair.seq1 v), simp [of, aux_seq_eq] }

/-- The head term of the gcf of `v` is `⌊v⌋`. -/
@[simp]
lemma of_h_eq_floor : (of v).h = ⌊v⌋ :=
by simp [of_h_eq_int_fract_pair_seq1_fst_b, int_fract_pair.of]

end head

section sequence
/-!
### Translation of the Sequences

Here we state some lemmas that show how the sequences of the involved structures
(`int_fract_pair.stream`, `int_fract_pair.seq1`, and `generalized_continued_fraction.of`) are
connected, i.e. how the values are moved along the structures and how the termination of one
sequence implies the termination of another sequence.
-/

variable {n : ℕ}

lemma int_fract_pair.nth_seq1_eq_succ_nth_stream :
  (int_fract_pair.seq1 v).snd.nth n = (int_fract_pair.stream v) (n + 1) := rfl

section termination
/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/

lemma of_terminated_at_iff_int_fract_pair_seq1_terminated_at :
  (of v).terminated_at n ↔ (int_fract_pair.seq1 v).snd.terminated_at n :=
option.map_eq_none

lemma of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none :
  (of v).terminated_at n ↔ int_fract_pair.stream v (n + 1) = none :=
by rw [of_terminated_at_iff_int_fract_pair_seq1_terminated_at, stream.seq.terminated_at,
  int_fract_pair.nth_seq1_eq_succ_nth_stream]

end termination

section values
/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/

lemma int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some {gp_n : pair K}
  (s_nth_eq : (of v).s.nth n = some gp_n) :
  ∃ (ifp : int_fract_pair K), int_fract_pair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b :=
begin
  obtain ⟨ifp, stream_succ_nth_eq, gp_n_eq⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ pair.mk 1 (ifp.b : K) = gp_n, by
    { unfold of int_fract_pair.seq1 at s_nth_eq,
      rwa [seq.map_tail, seq.nth_tail, seq.map_nth, option.map_eq_some'] at s_nth_eq },
  cases gp_n_eq,
  injection gp_n_eq with _ ifp_b_eq_gp_n_b,
  existsi ifp,
  exact ⟨stream_succ_nth_eq, ifp_b_eq_gp_n_b⟩
end

/--
Shows how the entries of the sequence of the computed continued fraction can be obtained by the
integer parts of the stream of integer and fractional parts.
-/
lemma nth_of_eq_some_of_succ_nth_int_fract_pair_stream {ifp_succ_n : int_fract_pair K}
  (stream_succ_nth_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) :
  (of v).s.nth n = some ⟨1, ifp_succ_n.b⟩ :=
begin
  unfold of int_fract_pair.seq1,
  rw [seq.map_tail, seq.nth_tail, seq.map_nth],
  simp [seq.nth, stream_succ_nth_eq]
end

/--
Shows how the entries of the sequence of the computed continued fraction can be obtained by the
fractional parts of the stream of integer and fractional parts.
-/
lemma nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero {ifp_n : int_fract_pair K}
  (stream_nth_eq : int_fract_pair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
  (of v).s.nth n = some ⟨1, (int_fract_pair.of ifp_n.fr⁻¹).b⟩ :=
have int_fract_pair.stream v (n + 1) = some (int_fract_pair.of ifp_n.fr⁻¹), by
  { cases ifp_n, simp [int_fract_pair.stream, stream_nth_eq, nth_fr_ne_zero] },
nth_of_eq_some_of_succ_nth_int_fract_pair_stream this

open int int_fract_pair

lemma of_s_head_aux (v : K) :
  (of v).s.nth 0 = (int_fract_pair.stream v 1).bind (some ∘ λ p, {a := 1, b := p.b}) :=
begin
  rw [of, int_fract_pair.seq1, of._match_1],
  simp only [seq.map_tail, seq.map, seq.tail, seq.head, seq.nth, stream.map],
  rw [← stream.nth_succ, stream.nth, option.map],
end

/--
This gives the first pair of coefficients of the continued fraction of a non-integer `v`.
-/
lemma of_s_head (h : fract v ≠ 0) : (of v).s.head = some ⟨1, ⌊(fract v)⁻¹⌋⟩ :=
begin
  change (of v).s.nth 0 = _,
  rw [of_s_head_aux, stream_succ_of_some (stream_zero v) h, option.bind],
  refl,
end

variables (K)

/--
If `a` is an integer, then the coefficient sequence of its continued fraction is empty.
-/
lemma of_s_of_int (a : ℤ) : (of (a : K)).s = seq.nil :=
begin
  have h : ∀ n, (of (a : K)).s.nth n = none,
  { intro n,
    induction n with n ih,
    { rw [of_s_head_aux, stream_succ_of_int, option.bind], },
    { exact (of (a : K)).s.prop ih, } },
  exact seq.ext (λ n, (h n).trans (seq.nth_nil n).symm),
end

variables {K} (v)

/--
Recurrence for the `generalized_continued_fraction.of` an element `v` of `K` in terms of
that of the inverse of the fractional part of `v`.
-/
lemma of_s_succ (n : ℕ) : (of v).s.nth (n + 1) = (of (fract v)⁻¹).s.nth n :=
begin
  cases eq_or_ne (fract v) 0 with h h,
  { obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋,  eq_of_sub_eq_zero h⟩,
    rw [fract_int_cast, inv_zero, of_s_of_int, ← cast_zero, of_s_of_int, seq.nth_nil,
        seq.nth_nil], },
  cases eq_or_ne ((of (fract v)⁻¹).s.nth n) none with h₁ h₁,
  { rwa [h₁, ← terminated_at_iff_s_none,
         of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none, stream_succ h,
         ← of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none,
         terminated_at_iff_s_none], },
  { obtain ⟨p, hp⟩ := option.ne_none_iff_exists'.mp h₁,
    obtain ⟨p', hp'₁, _⟩ := exists_succ_nth_stream_of_gcf_of_nth_eq_some hp,
    have Hp := nth_of_eq_some_of_succ_nth_int_fract_pair_stream hp'₁,
    rw [← stream_succ h] at hp'₁,
    rw [Hp, nth_of_eq_some_of_succ_nth_int_fract_pair_stream hp'₁], }
end

/--
This expresses the tail of the coefficient sequence of the `generalized_continued_fraction.of`
an element `v` of `K` as the coefficient sequence of that of the inverse of the
fractional part of `v`.
-/
lemma of_s_tail : (of v).s.tail = (of (fract v)⁻¹).s :=
seq.ext $ λ n, seq.nth_tail (of v).s n ▸ of_s_succ v n

variables (K) (n)

/--
If `a` is an integer, then the `convergents'` of its continued fraction expansion
are all equal to `a`.
-/
lemma convergents'_of_int (a : ℤ) : (of (a : K)).convergents' n = a :=
begin
  induction n with n ih,
  { simp only [zeroth_convergent'_eq_h, of_h_eq_floor, floor_int_cast], },
  { rw [convergents', of_h_eq_floor, floor_int_cast, add_right_eq_self],
    exact convergents'_aux_succ_none ((of_s_of_int K a).symm ▸ seq.nth_nil 0) _, }
end

variables {K} (v)

/--
The recurrence relation for the `convergents'` of the continued fraction expansion
of an element `v` of `K` in terms of the convergents of the inverse of its fractional part.
-/
lemma convergents'_succ :
  (of v).convergents' (n + 1) = ⌊v⌋ + 1 / (of (fract v)⁻¹).convergents' n :=
begin
  cases eq_or_ne (fract v) 0 with h h,
  { obtain ⟨a, rfl⟩ : ∃ a : ℤ, v = a := ⟨⌊v⌋, eq_of_sub_eq_zero h⟩,
    rw [convergents'_of_int, fract_int_cast, inv_zero, ← cast_zero,
        convergents'_of_int, cast_zero, div_zero, add_zero, floor_int_cast], },
  { rw [convergents', of_h_eq_floor, add_right_inj, convergents'_aux_succ_some (of_s_head h)],
    exact congr_arg ((/) 1) (by rw [convergents', of_h_eq_floor, add_right_inj, of_s_tail]), }
end

end values
end sequence
end generalized_continued_fraction
