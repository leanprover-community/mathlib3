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
1. Recurrences and inversion lemmas for `int_fract_pair.seq`: these lemmas give us inversion
   rules and recurrences for the computation of the stream of integer and fractional parts of
   a value.
2. Translation lemmas for the head term: these lemmas show us that the head term of the computed
   continued fraction of a value `v` is `⌊v⌋` and how this head term is moved along the structures
   used in the computation process.
3. Translation lemmas for the sequence: these lemmas show how the sequences of the involved
   structures (`int_fract_pair.seq`, `int_fract_pair.seq1`, and
   `generalized_continued_fraction.of`) are connected, i.e. how the values are moved along the
   structures and the termination of one sequence implies the termination of another sequence.

## Main Theorems

- `succ_nth_seq_eq_some_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of non-termination.
- `succ_nth_seq_eq_none_iff` gives as a recurrence to compute the `n + 1`th value of the sequence
  of integer and fractional parts of a value in case of termination.
- `nth_of_eq_some_of_succ_nth_int_fract_pair_seq` and
  `nth_of_eq_some_of_nth_int_fract_pair_seq_fr_ne_zero` show how the entries of the sequence
  of the computed continued fraction can be obtained from the stream of integer and fractional
  parts.
-/

namespace generalized_continued_fraction
open generalized_continued_fraction (of)

/- Fix a discrete linear ordered floor field and a value `v`. -/
variables {K : Type*} [linear_ordered_field K] [floor_ring K] {v : K}

namespace int_fract_pair
/-!
### Recurrences and Inversion Lemmas for `int_fract_pair.seq`

Here we state some lemmas that give us inversion rules and recurrences for the computation of the
stream of integer and fractional parts of a value.
-/

variable {n : ℕ}

/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
lemma terminated_at_seq_succ_iff' : (int_fract_pair.seq v).terminated_at (n + 1)
  ↔ ∀ ifp ∈ (int_fract_pair.seq v).nth n, fr ifp = (0 : K) :=
begin
  simp only [int_fract_pair.seq, seq.terminated_at, exists_prop, option.mem_def,
    stream.nth_iterate_succ', option.bind_eq_none', int_fract_pair.next, ite_eq_iff,
    and_false, false_or, not_and', not_not],
  exact ⟨λ h ifp hn, h _ _ hn rfl, λ h b a hn hb, h _ hn⟩
end

/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of termination.
-/
lemma terminated_at_seq_succ_iff : (int_fract_pair.seq v).terminated_at (n + 1)
  ↔ (int_fract_pair.seq v).terminated_at n ∨
    ∃ ifp ∈ (int_fract_pair.seq v).nth n, fr ifp = (0 : K) :=
begin
  simp_rw [terminated_at_seq_succ_iff', exists_prop, seq.terminated_at],
  cases (int_fract_pair.seq v).val.nth n; simp
end

lemma terminated_at_seq_of_fr_eq_zero {ifp_n : int_fract_pair K}
  (seq_nth_eq : (int_fract_pair.seq v).nth n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
  (int_fract_pair.seq v).terminated_at (n + 1) :=
terminated_at_seq_succ_iff.2 $ or.inr ⟨ifp_n, seq_nth_eq, nth_fr_eq_zero⟩

/--
Gives a recurrence to compute the `n + 1`th value of the sequence of integer and fractional
parts of a value in case of non-termination.
-/
lemma succ_nth_seq_eq_some_iff {ifp_succ_n : int_fract_pair K} :
    (int_fract_pair.seq v).nth (n + 1) = some ifp_succ_n
  ↔ ∃ (ifp_n : int_fract_pair K), (int_fract_pair.seq v).nth n = some ifp_n
      ∧ ifp_n.fr ≠ 0
      ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n :=
by simp only [int_fract_pair.seq, seq.terminated_at, exists_prop, option.mem_def, and_false,
  false_or, stream.nth_iterate_succ', option.bind_eq_some', int_fract_pair.next, ite_eq_iff]

lemma exists_succ_nth_seq_of_fr_zero {ifp_succ_n : int_fract_pair K}
  (seq_succ_nth_eq : (int_fract_pair.seq v).nth (n + 1) = some ifp_succ_n)
  (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
  ∃ ifp_n : int_fract_pair K, (int_fract_pair.seq v).nth n = some ifp_n ∧
    ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
begin
  -- get the witness from `succ_nth_seq_eq_some_iff` and prove that it has the additional
  -- properties
  rcases (succ_nth_seq_eq_some_iff.mp seq_succ_nth_eq) with
    ⟨ifp_n, seq_nth_eq, nth_fr_ne_zero, rfl⟩,
  refine ⟨ifp_n, seq_nth_eq, _⟩,
  simpa only [int_fract_pair.of, int.fract, sub_eq_zero] using succ_nth_fr_eq_zero
end

end int_fract_pair

section sequence
/-!
### Translation of the Sequences

Here we state some lemmas that show how the sequences of the involved structures
(`int_fract_pair.seq`, `int_fract_pair.seq1`, and `generalized_continued_fraction.of`) are
connected, i.e. how the values are moved along the structures and how the termination of one
sequence implies the termination of another sequence.
-/

variable {n : ℕ}

lemma int_fract_pair.nth_seq1_eq_succ_nth_seq :
  (int_fract_pair.seq1 v).2.nth n = (int_fract_pair.seq v).nth (n + 1) := rfl

section termination
/-!
#### Translation of the Termination of the Sequences

Let's first show how the termination of one sequence implies the termination of another sequence.
-/

lemma of_terminated_at_iff_int_fract_pair_seq1_terminated_at :
  (of v).terminated_at n ↔ (int_fract_pair.seq1 v).tail.terminated_at n :=
option.map_eq_none

lemma of_terminated_at_n_iff_succ_nth_int_fract_pair_seq_eq_none :
  (of v).terminated_at n ↔ (int_fract_pair.seq v).nth (n + 1) = none :=
of_terminated_at_iff_int_fract_pair_seq1_terminated_at

end termination

section values
/-!
#### Translation of the Values of the Sequence

Now let's show how the values of the sequences correspond to one another.
-/

lemma int_fract_pair.exists_succ_nth_seq_of_gcf_of_nth_eq_some {gp_n : pair K}
  (s_nth_eq : (of v).s.nth n = some gp_n) :
  ∃ ifp ∈ (int_fract_pair.seq v).nth (n + 1), (ifp.b : K) = gp_n.b :=
begin
  obtain ⟨ifp, seq_succ_nth_eq, rfl⟩ :
    ∃ ifp, (int_fract_pair.seq v).nth (n + 1) = some ifp ∧ pair.mk 1 (ifp.b : K) = gp_n,
  { unfold of int_fract_pair.seq1 at s_nth_eq,
    rwa [seq.map_tail, seq.nth_tail, seq.nth_map, option.map_eq_some'] at s_nth_eq },
  exact ⟨ifp, seq_succ_nth_eq, rfl⟩
end

/--
Shows how the entries of the sequence of the computed continued fraction can be obtained by the
integer parts of the stream of integer and fractional parts.
-/
lemma nth_of_eq_some_of_succ_nth_int_fract_pair_seq {ifp_succ_n : int_fract_pair K}
  (seq_succ_nth_eq : (int_fract_pair.seq v).nth (n + 1) = some ifp_succ_n) :
  (of v).s.nth n = some ⟨1, ifp_succ_n.b⟩ :=
by rw [of_s, seq.map_tail, seq.nth_tail, seq.nth_map, seq_succ_nth_eq, option.map_some']

/--
Shows how the entries of the sequence of the computed continued fraction can be obtained by the
fractional parts of the stream of integer and fractional parts.
-/
lemma nth_of_eq_some_of_nth_int_fract_pair_seq_fr_ne_zero {ifp_n : int_fract_pair K}
  (seq_nth_eq : (int_fract_pair.seq v).nth n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
  (of v).s.nth n = some ⟨1, ⌊ifp_n.fr⁻¹⌋⟩ :=
show (of v).s.nth n = some ⟨1, (int_fract_pair.of ifp_n.fr⁻¹).b⟩,
from nth_of_eq_some_of_succ_nth_int_fract_pair_seq $
  int_fract_pair.succ_nth_seq_eq_some_iff.2 ⟨_, seq_nth_eq, nth_fr_ne_zero, rfl⟩

end values
end sequence
end generalized_continued_fraction
