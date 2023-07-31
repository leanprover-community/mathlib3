/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.computation.approximations
import algebra.continued_fractions.computation.correctness_terminating
import data.rat.floor
/-!
# Termination of Continued Fraction Computations (`gcf.of`)

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

## Summary
We show that the continued fraction for a value `v`, as defined in
`algebra.continued_fractions.computation.basic`, terminates if and only if `v` corresponds to a
rational number, that is `↑v = q` for some `q : ℚ`.

## Main Theorems

- `generalized_continued_fraction.coe_of_rat` shows that
  `generalized_continued_fraction.of v = generalized_continued_fraction.of q` for `v : α` given that
  `↑v = q` and `q : ℚ`.
- `generalized_continued_fraction.terminates_iff_rat` shows that
  `generalized_continued_fraction.of v` terminates if and only if `↑v = q` for some `q : ℚ`.

## Tags

rational, continued fraction, termination
-/

namespace generalized_continued_fraction
open stream.seq as seq

open generalized_continued_fraction (of)

variables {K : Type*} [linear_ordered_field K] [floor_ring K]

/-
We will have to constantly coerce along our structures in the following proofs using their provided
map functions.
-/
local attribute [simp] pair.map int_fract_pair.mapFr

section rat_of_terminates
/-!
### Terminating Continued Fractions Are Rational

We want to show that the computation of a continued fraction `generalized_continued_fraction.of v`
terminates if and only if `v ∈ ℚ`. In this section, we show the implication from left to right.

We first show that every finite convergent corresponds to a rational number `q` and then use the
finite correctness proof (`of_correctness_of_terminates`) of `generalized_continued_fraction.of` to
show that `v = ↑q`.
-/

variables (v : K) (n : ℕ)

lemma exists_gcf_pair_rat_eq_of_nth_conts_aux :
  ∃ (conts : pair ℚ),
    (of v).continuants_aux n = (conts.map coe : pair K) :=
nat.strong_induction_on n
begin
  clear n,
  let g := of v,
  assume n IH,
  rcases n with _|_|n,
  -- n = 0
  { suffices : ∃ (gp : pair ℚ), pair.mk (1 : K) 0 = gp.map coe, by simpa [continuants_aux],
    use (pair.mk 1 0),
    simp },
  -- n = 1
  { suffices : ∃ (conts : pair ℚ), pair.mk g.h 1 = conts.map coe, by
      simpa [continuants_aux],
    use (pair.mk ⌊v⌋ 1),
    simp },
  -- 2 ≤ n
  { cases (IH (n + 1) $ lt_add_one (n + 1)) with pred_conts pred_conts_eq, -- invoke the IH
    cases s_ppred_nth_eq : (g.s.nth n) with gp_n,
    -- option.none
    { use pred_conts,
      have : g.continuants_aux (n + 2) = g.continuants_aux (n + 1), from
        continuants_aux_stable_of_terminated (n + 1).le_succ s_ppred_nth_eq,
      simp only [this, pred_conts_eq] },
    -- option.some
    { -- invoke the IH a second time
      cases (IH n $ lt_of_le_of_lt (n.le_succ) $ lt_add_one $ n + 1)
        with ppred_conts ppred_conts_eq,
      obtain ⟨a_eq_one, z, b_eq_z⟩ : gp_n.a = 1 ∧ ∃ (z : ℤ), gp_n.b = (z : K), from
        of_part_num_eq_one_and_exists_int_part_denom_eq s_ppred_nth_eq,
      -- finally, unfold the recurrence to obtain the required rational value.
      simp only [a_eq_one, b_eq_z,
        (continuants_aux_recurrence s_ppred_nth_eq ppred_conts_eq pred_conts_eq)],
      use (next_continuants 1 (z : ℚ) ppred_conts pred_conts),
      cases ppred_conts, cases pred_conts,
      simp [next_continuants, next_numerator, next_denominator] } }
end

lemma exists_gcf_pair_rat_eq_nth_conts :
  ∃ (conts : pair ℚ), (of v).continuants n = (conts.map coe : pair K) :=
by { rw [nth_cont_eq_succ_nth_cont_aux], exact (exists_gcf_pair_rat_eq_of_nth_conts_aux v $ n + 1) }

lemma exists_rat_eq_nth_numerator : ∃ (q : ℚ), (of v).numerators n = (q : K) :=
begin
  rcases (exists_gcf_pair_rat_eq_nth_conts v n) with ⟨⟨a, _⟩, nth_cont_eq⟩,
  use a,
  simp [num_eq_conts_a, nth_cont_eq],
end

lemma exists_rat_eq_nth_denominator : ∃ (q : ℚ), (of v).denominators n = (q : K) :=
begin
  rcases (exists_gcf_pair_rat_eq_nth_conts v n) with ⟨⟨_, b⟩, nth_cont_eq⟩,
  use b,
  simp [denom_eq_conts_b, nth_cont_eq]
end

/-- Every finite convergent corresponds to a rational number. -/
lemma exists_rat_eq_nth_convergent : ∃ (q : ℚ), (of v).convergents n = (q : K) :=
begin
  rcases (exists_rat_eq_nth_numerator v n) with ⟨Aₙ, nth_num_eq⟩,
  rcases (exists_rat_eq_nth_denominator v n) with ⟨Bₙ, nth_denom_eq⟩,
  use (Aₙ / Bₙ),
  simp [nth_num_eq, nth_denom_eq, convergent_eq_num_div_denom]
end

variable {v}

/-- Every terminating continued fraction corresponds to a rational number. -/
theorem exists_rat_eq_of_terminates
  (terminates : (of v).terminates) :
  ∃ (q : ℚ), v = ↑q :=
begin
  obtain ⟨n, v_eq_conv⟩ : ∃ n, v = (of v).convergents n, from
    of_correctness_of_terminates terminates,
  obtain ⟨q, conv_eq_q⟩ :
    ∃ (q : ℚ), (of v).convergents n = (↑q : K), from exists_rat_eq_nth_convergent v n,
  have : v = (↑q : K), from eq.trans v_eq_conv conv_eq_q,
  use [q, this]
end

end rat_of_terminates

section rat_translation
/-!
### Technical Translation Lemmas

Before we can show that the continued fraction of a rational number terminates, we have to prove
some technical translation lemmas. More precisely, in this section, we show that, given a rational
number `q : ℚ` and value `v : K` with `v = ↑q`, the continued fraction of `q` and `v` coincide.
In particular, we show that
```lean
    (↑(generalized_continued_fraction.of q : generalized_continued_fraction ℚ)
      : generalized_continued_fraction K)
  = generalized_continued_fraction.of v`
```
in `generalized_continued_fraction.coe_of_rat`.

To do this, we proceed bottom-up, showing the correspondence between the basic functions involved in
the computation first and then lift the results step-by-step.
-/

/- The lifting works for arbitrary linear ordered fields with a floor function. -/
variables {v : K} {q : ℚ} (v_eq_q : v = (↑q : K)) (n : ℕ)
include v_eq_q

/-! First, we show the correspondence for the very basic functions in
`generalized_continued_fraction.int_fract_pair`. -/
namespace int_fract_pair

lemma coe_of_rat_eq :
  ((int_fract_pair.of q).mapFr coe : int_fract_pair K) = int_fract_pair.of v :=
by simp [int_fract_pair.of, v_eq_q]

lemma coe_stream_nth_rat_eq :
    ((int_fract_pair.stream q n).map (mapFr coe) : option $ int_fract_pair K)
  = int_fract_pair.stream v n :=
begin
  induction n with n IH,
  case nat.zero : { simp [int_fract_pair.stream, (coe_of_rat_eq v_eq_q)] },
  case nat.succ :
  { rw v_eq_q at IH,
    cases stream_q_nth_eq : (int_fract_pair.stream q n) with ifp_n,
    case option.none : { simp [int_fract_pair.stream, IH.symm, v_eq_q, stream_q_nth_eq] },
    case option.some :
    { cases ifp_n with b fr,
      cases decidable.em (fr = 0) with fr_zero fr_ne_zero,
      { simp [int_fract_pair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_zero] },
      { replace IH : some (int_fract_pair.mk b ↑fr) = int_fract_pair.stream ↑q n, by
          rwa [stream_q_nth_eq] at IH,
        have : (fr : K)⁻¹ = ((fr⁻¹ : ℚ) : K), by norm_cast,
        have coe_of_fr := (coe_of_rat_eq this),
        simpa [int_fract_pair.stream, IH.symm, v_eq_q, stream_q_nth_eq, fr_ne_zero] } } }
end

lemma coe_stream_rat_eq :
  ((int_fract_pair.stream q).map (option.map (mapFr coe)) : stream $ option $ int_fract_pair K) =
    int_fract_pair.stream v :=
by { funext n, exact (int_fract_pair.coe_stream_nth_rat_eq v_eq_q n) }

end int_fract_pair

/-! Now we lift the coercion results to the continued fraction computation. -/

lemma coe_of_h_rat_eq : (↑((of q).h : ℚ) : K) = (of v).h :=
begin
  unfold of int_fract_pair.seq1,
  rw ←(int_fract_pair.coe_of_rat_eq v_eq_q),
  simp
end

lemma coe_of_s_nth_rat_eq :
  (((of q).s.nth n).map (pair.map coe) : option $ pair K) = (of v).s.nth n :=
begin
  simp only [of, int_fract_pair.seq1, seq.map_nth, seq.nth_tail],
  simp only [seq.nth],
  rw [←(int_fract_pair.coe_stream_rat_eq v_eq_q)],
  rcases succ_nth_stream_eq : (int_fract_pair.stream q (n + 1)) with _ | ⟨_, _⟩;
  simp [stream.map, stream.nth, succ_nth_stream_eq]
end

lemma coe_of_s_rat_eq : (((of q).s).map (pair.map coe) : seq $ pair K) = (of v).s :=
by { ext n, rw ←(coe_of_s_nth_rat_eq v_eq_q), refl }

/-- Given `(v : K), (q : ℚ), and v = q`, we have that `gcf.of q = gcf.of v` -/
lemma coe_of_rat_eq :
  (⟨(of q).h, (of q).s.map (pair.map coe)⟩ : generalized_continued_fraction K) = of v :=
begin
  cases gcf_v_eq : (of v) with h s, subst v,
  obtain rfl : ↑⌊↑q⌋ = h, by { injection gcf_v_eq },
  simp [coe_of_h_rat_eq rfl, coe_of_s_rat_eq rfl, gcf_v_eq]
end

lemma of_terminates_iff_of_rat_terminates {v : K} {q : ℚ} (v_eq_q : v = (q : K)) :
  (of v).terminates ↔ (of q).terminates :=
begin
  split;
  intro h;
  cases h with n h;
  use n;
  simp only [seq.terminated_at, (coe_of_s_nth_rat_eq v_eq_q n).symm] at h ⊢;
  cases ((of q).s.nth n);
  trivial
end

end rat_translation

section terminates_of_rat
/-!
### Continued Fractions of Rationals Terminate

Finally, we show that the continued fraction of a rational number terminates.

The crucial insight is that, given any `q : ℚ` with `0 < q < 1`, the numerator of `int.fract q` is
smaller than the numerator of `q`. As the continued fraction computation recursively operates on
the fractional part of a value `v` and `0 ≤ int.fract v < 1`, we infer that the numerator of the
fractional part in the computation decreases by at least one in each step. As `0 ≤ int.fract v`,
this process must stop after finite number of steps, and the computation hence terminates.
-/

namespace int_fract_pair
variables {q : ℚ} {n : ℕ}

/--
Shows that for any `q : ℚ` with `0 < q < 1`, the numerator of the fractional part of
`int_fract_pair.of q⁻¹` is smaller than the numerator of `q`.
-/
lemma of_inv_fr_num_lt_num_of_pos (q_pos : 0 < q) :
  (int_fract_pair.of q⁻¹).fr.num < q.num :=
rat.fract_inv_num_lt_num_of_pos q_pos

/-- Shows that the sequence of numerators of the fractional parts of the stream is strictly
antitone. -/
lemma stream_succ_nth_fr_num_lt_nth_fr_num_rat {ifp_n ifp_succ_n : int_fract_pair ℚ}
  (stream_nth_eq : int_fract_pair.stream q n = some ifp_n)
  (stream_succ_nth_eq : int_fract_pair.stream q (n + 1) = some ifp_succ_n) :
  ifp_succ_n.fr.num < ifp_n.fr.num :=
begin
  obtain ⟨ifp_n', stream_nth_eq', ifp_n_fract_ne_zero, int_fract_pair.of_eq_ifp_succ_n⟩ :
    ∃ ifp_n', int_fract_pair.stream q n = some ifp_n' ∧ ifp_n'.fr ≠ 0
    ∧ int_fract_pair.of ifp_n'.fr⁻¹ = ifp_succ_n, from
      succ_nth_stream_eq_some_iff.elim_left stream_succ_nth_eq,
  have : ifp_n = ifp_n', by injection (eq.trans stream_nth_eq.symm stream_nth_eq'),
  cases this,
  rw [←int_fract_pair.of_eq_ifp_succ_n],
  cases (nth_stream_fr_nonneg_lt_one stream_nth_eq) with zero_le_ifp_n_fract ifp_n_fract_lt_one,
  have : 0 < ifp_n.fr, from (lt_of_le_of_ne zero_le_ifp_n_fract $ ifp_n_fract_ne_zero.symm),
  exact (of_inv_fr_num_lt_num_of_pos this)
end

lemma stream_nth_fr_num_le_fr_num_sub_n_rat : ∀ {ifp_n : int_fract_pair ℚ},
  int_fract_pair.stream q n = some ifp_n → ifp_n.fr.num ≤ (int_fract_pair.of q).fr.num - n :=
begin
  induction n with n IH,
  case nat.zero
  { assume ifp_zero stream_zero_eq,
    have : int_fract_pair.of q = ifp_zero, by injection stream_zero_eq,
    simp [le_refl, this.symm] },
  case nat.succ
  { assume ifp_succ_n stream_succ_nth_eq,
    suffices : ifp_succ_n.fr.num + 1 ≤ (int_fract_pair.of q).fr.num - n, by
    { rw [int.coe_nat_succ, sub_add_eq_sub_sub],
      solve_by_elim [le_sub_right_of_add_le] },
    rcases (succ_nth_stream_eq_some_iff.elim_left stream_succ_nth_eq) with
      ⟨ifp_n, stream_nth_eq, -⟩,
    have : ifp_succ_n.fr.num < ifp_n.fr.num, from
      stream_succ_nth_fr_num_lt_nth_fr_num_rat stream_nth_eq stream_succ_nth_eq,
    have : ifp_succ_n.fr.num + 1 ≤ ifp_n.fr.num, from int.add_one_le_of_lt this,
    exact (le_trans this (IH stream_nth_eq)) }
end

lemma exists_nth_stream_eq_none_of_rat (q : ℚ) : ∃ (n : ℕ), int_fract_pair.stream q n = none :=
begin
  let fract_q_num := (int.fract q).num, let n := fract_q_num.nat_abs + 1,
  cases stream_nth_eq : (int_fract_pair.stream q n) with ifp,
  { use n, exact stream_nth_eq },
  { -- arrive at a contradiction since the numerator decreased num + 1 times but every fractional
    -- value is nonnegative.
    have ifp_fr_num_le_q_fr_num_sub_n : ifp.fr.num ≤ fract_q_num - n, from
      stream_nth_fr_num_le_fr_num_sub_n_rat stream_nth_eq,
    have : fract_q_num - n = -1, by
    { have : 0 ≤ fract_q_num, from rat.num_nonneg_iff_zero_le.elim_right (int.fract_nonneg q),
      simp [(int.nat_abs_of_nonneg this), sub_add_eq_sub_sub_swap, sub_right_comm] },
    have : ifp.fr.num ≤ -1, by rwa this at ifp_fr_num_le_q_fr_num_sub_n,
    have : 0 ≤ ifp.fr, from (nth_stream_fr_nonneg_lt_one stream_nth_eq).left,
    have : 0 ≤ ifp.fr.num, from rat.num_nonneg_iff_zero_le.elim_right this,
    linarith }
end

end int_fract_pair


/-- The continued fraction of a rational number terminates. -/
theorem terminates_of_rat (q : ℚ) : (of q).terminates :=
exists.elim (int_fract_pair.exists_nth_stream_eq_none_of_rat q)
( assume n stream_nth_eq_none,
  exists.intro n
  ( have int_fract_pair.stream q (n + 1) = none, from
      int_fract_pair.stream_is_seq q stream_nth_eq_none,
    (of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none.elim_right this) ) )

end terminates_of_rat


/--
The continued fraction `generalized_continued_fraction.of v` terminates if and only if `v ∈ ℚ`.
-/
theorem terminates_iff_rat (v : K) : (of v).terminates ↔ ∃ (q : ℚ), v = (q : K) :=
iff.intro
( assume terminates_v : (of v).terminates,
  show ∃ (q : ℚ), v = (q : K), from exists_rat_eq_of_terminates terminates_v )
( assume exists_q_eq_v : ∃ (q : ℚ), v = (↑q : K),
  exists.elim exists_q_eq_v
  ( assume q,
    assume v_eq_q : v = ↑q,
    have (of q).terminates, from terminates_of_rat q,
    (of_terminates_iff_of_rat_terminates v_eq_q).elim_right this ) )

end generalized_continued_fraction
