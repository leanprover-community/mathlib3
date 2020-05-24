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

Some simple translation lemmas between the different structures used for the computations defined in
`algebra.continued_fractions.computation.basic`.
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf

/-- Fix a discrete linear order floor field and a value `v`. -/
variables {α : Type*} [discrete_linear_ordered_field α] [floor_ring α] {v : α}

namespace int_fract_pair
/-!
### Translation and Inversion Lemmas for `int_fract_pair.stream`

Here we state some technical lemmas that deal with the computation of the sequence of integer and
fractional parts used to obtain a continued fraction.
The lemmas themselves are not interesting and are just needed to prove properties about the sequence
later on.
-/

variable {n : ℕ}

lemma stream_eq_none_of_fr_eq_zero {ifp_n : int_fract_pair α}
  (stream_nth_eq : int_fract_pair.stream v n = some ifp_n) (nth_fr_eq_zero : ifp_n.fr = 0) :
  int_fract_pair.stream v (n + 1) = none :=
begin
  cases ifp_n with _ fr,
  change fr = 0 at nth_fr_eq_zero,
  simp [int_fract_pair.stream, stream_nth_eq, nth_fr_eq_zero]
end

lemma succ_nth_stream_eq_none_iff : int_fract_pair.stream v (n + 1) = none
  ↔ (int_fract_pair.stream v n = none ∨ ∃ ifp, int_fract_pair.stream v n = some ifp ∧ ifp.fr = 0) :=
begin
  cases stream_nth_eq : (int_fract_pair.stream v n) with ifp,
  case option.none : { simp [stream_nth_eq, int_fract_pair.stream] },
  case option.some :
  { cases ifp with _ fr,
    cases decidable.em (fr = 0);
    finish [int_fract_pair.stream] }
end

lemma succ_nth_stream_eq_some_iff {ifp_succ_n : int_fract_pair α} :
    int_fract_pair.stream v (n + 1) = some ifp_succ_n
  ↔ ∃ (ifp_n : int_fract_pair α), int_fract_pair.stream v n = some ifp_n
      ∧ ifp_n.fr ≠ 0
      ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n :=
begin
  split,
  { assume stream_succ_nth_eq,
    have : int_fract_pair.stream v (n + 1) ≠ none, by simp [stream_succ_nth_eq],
    have : ¬int_fract_pair.stream v n = none
           ∧ ¬(∃ ifp, int_fract_pair.stream v n = some ifp ∧ ifp.fr = 0), by
    { have not_none_not_fract_zero, from (not_iff_not_of_iff succ_nth_stream_eq_none_iff).elim_left this,
      exact (not_or_distrib.elim_left not_none_not_fract_zero) },
    cases this with stream_nth_ne_none nth_fr_ne_zero,
    replace nth_fr_ne_zero : ∀ ifp, int_fract_pair.stream v n = some ifp → ifp.fr ≠ 0, by
      simpa using nth_fr_ne_zero,
    obtain ⟨ifp_n, stream_nth_eq⟩ : ∃ ifp_n, int_fract_pair.stream v n = some ifp_n, from
      with_one.ne_one_iff_exists.elim_left stream_nth_ne_none,
    existsi ifp_n,
    have ifp_n_fr_ne_zero : ifp_n.fr ≠ 0, from nth_fr_ne_zero ifp_n stream_nth_eq,
    cases ifp_n with _ ifp_n_fr,
    suffices : int_fract_pair.of ifp_n_fr⁻¹ = ifp_succ_n, by simpa [stream_nth_eq, ifp_n_fr_ne_zero],
    simp only [int_fract_pair.stream, stream_nth_eq, ifp_n_fr_ne_zero, option.some_bind, if_false]
      at stream_succ_nth_eq,
    injection stream_succ_nth_eq },
  { rintro ⟨⟨_⟩, ifp_n_props⟩, finish [int_fract_pair.stream, ifp_n_props] }
end

lemma obtain_succ_nth_stream_of_fr_zero {ifp_succ_n : int_fract_pair α}
  (stream_succ_nth_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n)
  (succ_nth_fr_eq_zero : ifp_succ_n.fr = 0) :
  ∃ (ifp_n : int_fract_pair α), int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr⁻¹ = ⌊ifp_n.fr⁻¹⌋ :=
begin
  -- get the witness from `succ_nth_stream_eq_some_iff` and prove that it has the additional
  -- properties
  rcases (succ_nth_stream_eq_some_iff.elim_left stream_succ_nth_eq) with
    ⟨ifp_n, stream_nth_eq, nth_fr_ne_zero, _⟩,
  existsi ifp_n,
  cases ifp_n with _ ifp_n_fr,
  suffices : ifp_n_fr⁻¹ = ⌊ifp_n_fr⁻¹⌋, by simpa [stream_nth_eq],
  have : int_fract_pair.of ifp_n_fr⁻¹ = ifp_succ_n, by finish,
  cases ifp_succ_n with _ ifp_succ_n_fr,
  change ifp_succ_n_fr = 0 at succ_nth_fr_eq_zero,
  have : fract ifp_n_fr⁻¹ = ifp_succ_n_fr, by injection this,
  have : fract ifp_n_fr⁻¹ = 0, by rwa [succ_nth_fr_eq_zero] at this,
  calc
    ifp_n_fr⁻¹ = fract ifp_n_fr⁻¹ + ⌊ifp_n_fr⁻¹⌋ : by rw (fract_add_floor ifp_n_fr⁻¹)
           ... = ⌊ifp_n_fr⁻¹⌋                    : by simp [‹fract ifp_n_fr⁻¹ = 0›]
end

end int_fract_pair

section head
/-!
### Translation of The Head Term

Here we give some basic translations that between the various methods that return the head term of
the continued fraction computed for a value.
-/

/- The head term of the sequence with head of `v` is just the integer part of `v`. -/
@[simp]
lemma int_fract_pair.seq1_fst_eq_of : (int_fract_pair.seq1 v).fst = int_fract_pair.of v := rfl

lemma of_h_eq_int_fract_pair_seq1_fst_b : (gcf.of v).h = (int_fract_pair.seq1 v).fst.b :=
by { cases aux_seq_eq : (int_fract_pair.seq1 v), simp [gcf.of, aux_seq_eq] }

/- The head term of the gcf of `v` is ⌊v⌋. -/
@[simp]
lemma of_h_eq_floor : (gcf.of v).h = ⌊v⌋ :=
by simp [of_h_eq_int_fract_pair_seq1_fst_b, int_fract_pair.of]

end head

section sequence
/-!
### Translation of The Sequence

Here we give some basic translations that between the various methods that return the sequence part
of the continued fraction computed for a value.
-/

variable {n : ℕ}

lemma int_fract_pair.nth_seq1_eq_succ_nth_stream :
  (int_fract_pair.seq1 v).snd.nth n = (int_fract_pair.stream v) (n + 1) := rfl

section termination
/-!
#### Translation of The Termination of The Sequence
-/

lemma of_terminated_at_iff_int_fract_pair_seq1_terminated_at :
  (gcf.of v).terminated_at n ↔ (int_fract_pair.seq1 v).snd.terminated_at n :=
begin
  rw [gcf.terminated_at_iff_s_none, gcf.of],
  rcases (int_fract_pair.seq1 v) with ⟨head, ⟨st⟩⟩,
  cases st_n_eq : st n;
  simp [gcf.of, st_n_eq, seq.map, seq.nth, stream.map, seq.terminated_at, stream.nth]
end

lemma of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none :
  (gcf.of v).terminated_at n ↔ int_fract_pair.stream v (n + 1) = none :=
by rw [of_terminated_at_iff_int_fract_pair_seq1_terminated_at, seq.terminated_at,
  int_fract_pair.nth_seq1_eq_succ_nth_stream]

end termination

section values
/-!
#### Translation of The Values of The Sequence
-/

lemma nth_of_eq_some_of_succ_nth_int_fract_pair_stream {ifp_succ_n : int_fract_pair α}
  (stream_succ_nth_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) :
  (gcf.of v).s.nth n = some ⟨1, ifp_succ_n.b⟩ :=
begin
  unfold gcf.of int_fract_pair.seq1,
  rw [seq.map_tail, seq.nth_tail, seq.map_nth],
  simp [seq.nth, stream_succ_nth_eq]
end

lemma int_fract_pair.obtain_succ_nth_stream_of_gcf_of_nth_eq_some {gp_n : gcf.pair α}
  (s_nth_eq : (gcf.of v).s.nth n = some gp_n) :
  ∃ (ifp : int_fract_pair α), int_fract_pair.stream v (n + 1) = some ifp ∧ (ifp.b : α) = gp_n.b :=
begin
  obtain ⟨ifp, stream_succ_nth_eq, gp_n_eq⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ gcf.pair.mk 1 (ifp.b : α) = gp_n, by
    { unfold gcf.of int_fract_pair.seq1 at s_nth_eq,
      rwa [seq.map_tail, seq.nth_tail, seq.map_nth, option.map_eq_some'] at s_nth_eq },
  cases gp_n_eq,
  injection gp_n_eq with _ ifp_b_eq_gp_n_b,
  existsi ifp,
  exact ⟨stream_succ_nth_eq, ifp_b_eq_gp_n_b⟩
end

lemma nth_of_eq_some_of_nth_int_fract_pair_stream_fr_ne_zero {ifp_n : int_fract_pair α}
  (stream_nth_eq : int_fract_pair.stream v n = some ifp_n) (nth_fr_ne_zero : ifp_n.fr ≠ 0) :
  (gcf.of v).s.nth n = some ⟨1, (int_fract_pair.of ifp_n.fr⁻¹).b⟩ :=
have int_fract_pair.stream v (n + 1) = some (int_fract_pair.of ifp_n.fr⁻¹), by
  { cases ifp_n, simp [int_fract_pair.stream, stream_nth_eq, nth_fr_ne_zero], refl },
nth_of_eq_some_of_succ_nth_int_fract_pair_stream this

end values
end sequence
end generalized_continued_fraction
