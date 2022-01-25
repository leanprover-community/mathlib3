/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.computation.basic
import algebra.continued_fractions.translations
/-!
# Basic Translation Lemmas Between Structures Defined for Computing Continued Fractions

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

/- Fix a discrete linear ordered floor field and a value `v`. -/
variables {K : Type*} [linear_ordered_field K] [floor_ring K] {v : K}

namespace int_fract_pair
/-!
### Recurrences and Inversion Lemmas for `int_fract_pair.stream`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/

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
  cases stream_nth_eq : (int_fract_pair.stream v n) with ifp,
  case option.none : { simp [stream_nth_eq, int_fract_pair.stream] },
  case option.some :
  { cases ifp with _ fr,
    by_cases h : fr = 0, -- `finish [int_fract_pair.stream]` closes both goals
    { simp [int_fract_pair.stream, h, stream_nth_eq] },
    { suffices : ¬ (int_fract_pair.of fr⁻¹: option $ int_fract_pair K) = none,
        by simp [int_fract_pair.stream, h, stream_nth_eq, this],
      exact λ h, option.no_confusion h } }
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
begin
  split,
  { assume stream_succ_nth_eq,
    have : int_fract_pair.stream v (n + 1) ≠ none, by simp [stream_succ_nth_eq],
    have : ¬int_fract_pair.stream v n = none
           ∧ ¬(∃ ifp, int_fract_pair.stream v n = some ifp ∧ ifp.fr = 0), by
    { have not_none_not_fract_zero,
        from (not_iff_not_of_iff succ_nth_stream_eq_none_iff).elim_left this,
      exact (not_or_distrib.elim_left not_none_not_fract_zero) },
    cases this with stream_nth_ne_none nth_fr_ne_zero,
    replace nth_fr_ne_zero : ∀ ifp, int_fract_pair.stream v n = some ifp → ifp.fr ≠ 0, by
      simpa using nth_fr_ne_zero,
    obtain ⟨ifp_n, stream_nth_eq⟩ : ∃ ifp_n, int_fract_pair.stream v n = some ifp_n, from
      option.ne_none_iff_exists'.mp stream_nth_ne_none,
    existsi ifp_n,
    have ifp_n_fr_ne_zero : ifp_n.fr ≠ 0, from nth_fr_ne_zero ifp_n stream_nth_eq,
    cases ifp_n with _ ifp_n_fr,
    suffices : int_fract_pair.of ifp_n_fr⁻¹ = ifp_succ_n,
      by simpa [stream_nth_eq, ifp_n_fr_ne_zero],
    simp only [int_fract_pair.stream, stream_nth_eq, ifp_n_fr_ne_zero, option.some_bind, if_false]
      at stream_succ_nth_eq,
    injection stream_succ_nth_eq },
  { rintro ⟨⟨_⟩, ifp_n_props⟩, -- `finish [int_fract_pair.stream, ifp_n_props]` closes this goal
    simpa only [int_fract_pair.stream, ifp_n_props, option.some_bind, if_false] }
end

lemma exists_succ_nth_stream_of_fr_zero {ifp_succ_n : int_fract_pair K}
  (stream_succ_nth_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n)
  (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
  ∃ ifp_n : int_fract_pair K, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
begin
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases (succ_nth_stream_eq_some_iff.elim_left stream_succ_nth_eq) with
    ⟨ifp_n, stream_nth_eq, nth_fr_ne_zero, _⟩,
  existsi ifp_n,
  cases ifp_n with _ ifp_n_fr,
  suffices : ifp_n_fr⁻¹ = ⌊ifp_n_fr⁻¹⌋, by simpa [stream_nth_eq],
  have : int_fract_pair.of ifp_n_fr⁻¹ = ifp_succ_n := h_right_right,
  cases ifp_succ_n with _ ifp_succ_n_fr,
  change ifp_succ_n_fr = 0 at succ_nth_fr_eq_zero,
  have : int.fract ifp_n_fr⁻¹ = ifp_succ_n_fr, by injection this,
  have : int.fract ifp_n_fr⁻¹ = 0, by rwa [succ_nth_fr_eq_zero] at this,
  calc
    ifp_n_fr⁻¹ = int.fract ifp_n_fr⁻¹ + ⌊ifp_n_fr⁻¹⌋ : by rw (int.fract_add_floor ifp_n_fr⁻¹)
           ... = ⌊ifp_n_fr⁻¹⌋                    : by simp [‹int.fract ifp_n_fr⁻¹ = 0›]
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
begin
  rw [terminated_at_iff_s_none, of],
  rcases (int_fract_pair.seq1 v) with ⟨head, ⟨st⟩⟩,
  cases st_n_eq : st n;
  simp [of, st_n_eq, seq.map, seq.nth, stream.map, seq.terminated_at, stream.nth]
end

lemma of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none :
  (of v).terminated_at n ↔ int_fract_pair.stream v (n + 1) = none :=
by rw [of_terminated_at_iff_int_fract_pair_seq1_terminated_at, seq.terminated_at,
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
  { cases ifp_n, simp [int_fract_pair.stream, stream_nth_eq, nth_fr_ne_zero], refl },
nth_of_eq_some_of_succ_nth_int_fract_pair_stream this

end values
end sequence
end generalized_continued_fraction
