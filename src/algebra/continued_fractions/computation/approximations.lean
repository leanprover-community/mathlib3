/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.computation.correctness_terminating
import data.nat.fib
import tactic.solve_by_elim
/-!
# Approximations for Continued Fraction Computations (`generalized_continued_fraction.of`)

## Summary

This file contains useful approximations for the values involved in the continued fractions
computation `generalized_continued_fraction.of`. In particular, we derive the so-called
*determinant formula* for `generalized_continued_fraction.of`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.

Moreover, we derive some upper bounds for the error term when computing a continued fraction up a
given position, i.e. bounds for the term
`|v - (generalized_continued_fraction.of v).convergents n|`. The derived bounds will show us that
the error term indeed gets smaller. As a corollary, we will be able to show that
`(generalized_continued_fraction.of v).convergents` converges to `v` in
`algebra.continued_fractions.computation.approximation_corollaries`.

## Main Theorems

- `generalized_continued_fraction.of_part_num_eq_one`: shows that all partial numerators `aᵢ` are
  equal to one.
- `generalized_continued_fraction.exists_int_eq_of_part_denom`: shows that all partial denominators
  `bᵢ` correspond to an integer.
- `generalized_continued_fraction.one_le_of_nth_part_denom`: shows that `1 ≤ bᵢ`.
- `generalized_continued_fraction.succ_nth_fib_le_of_nth_denom`: shows that the `n`th denominator
  `Bₙ` is greater than or equal to the `n + 1`th fibonacci number `nat.fib (n + 1)`.
- `generalized_continued_fraction.le_of_succ_nth_denom`: shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is
  the `n`th partial denominator of the continued fraction.
- `generalized_continued_fraction.abs_sub_convergents_le`: shows that
  `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)`, where `Aₙ` is the nth partial numerator.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]
- https://en.wikipedia.org/wiki/Generalized_continued_fraction#The_determinant_formula

-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf

variables {K : Type*} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K]

namespace int_fract_pair
/-!
We begin with some lemmas about the stream of `int_fract_pair`s, which presumably are not
of great interest for the end user.
-/

/-- Shows that the fractional parts of the stream are in `[0,1)`. -/
lemma nth_stream_fr_nonneg_lt_one {ifp_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  0 ≤ ifp_n.fr ∧ ifp_n.fr < 1 :=
begin
  cases n,
  case nat.zero
  { have : int_fract_pair.of v = ifp_n, by injection nth_stream_eq,
    simp [fract_lt_one, fract_nonneg, int_fract_pair.of, this.symm] },
  case nat.succ
  { rcases (succ_nth_stream_eq_some_iff.elim_left nth_stream_eq) with ⟨_, _, _, ifp_of_eq_ifp_n⟩,
    simp [fract_lt_one, fract_nonneg, int_fract_pair.of, ifp_of_eq_ifp_n.symm] }
end

/-- Shows that the fractional parts of the stream are nonnegative. -/
lemma nth_stream_fr_nonneg {ifp_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  0 ≤ ifp_n.fr :=
(nth_stream_fr_nonneg_lt_one nth_stream_eq).left

/-- Shows that the fractional parts of the stream are smaller than one. -/
lemma nth_stream_fr_lt_one {ifp_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  ifp_n.fr < 1 :=
(nth_stream_fr_nonneg_lt_one nth_stream_eq).right

/-- Shows that the integer parts of the stream are at least one. -/
lemma one_le_succ_nth_stream_b {ifp_succ_n : int_fract_pair K}
  (succ_nth_stream_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) :
  1 ≤ ifp_succ_n.b :=
begin
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨-⟩⟩ :
    ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
    ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n, from
      succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq,
  suffices : 1 ≤ ifp_n.fr⁻¹, { rw_mod_cast [le_floor], assumption },
  suffices : ifp_n.fr ≤ 1,
  { have h : 0 < ifp_n.fr, from
      lt_of_le_of_ne (nth_stream_fr_nonneg nth_stream_eq) stream_nth_fr_ne_zero.symm,
    apply one_le_inv h this },
  simp only [le_of_lt (nth_stream_fr_lt_one nth_stream_eq)]
end

/--
Shows that the `n + 1`th integer part `bₙ₊₁` of the stream is smaller or equal than the inverse of
the `n`th fractional part `frₙ` of the stream.
This result is straight-forward as `bₙ₊₁` is defined as the floor of `1 / frₙ`
-/
lemma succ_nth_stream_b_le_nth_stream_fr_inv {ifp_n ifp_succ_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n)
  (succ_nth_stream_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) :
  (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹ :=
begin
  suffices : (⌊ifp_n.fr⁻¹⌋ : K) ≤ ifp_n.fr⁻¹,
  { cases ifp_n with _ ifp_n_fr,
    have : ifp_n_fr ≠ 0,
    { intro h, simpa [h, int_fract_pair.stream, nth_stream_eq] using succ_nth_stream_eq },
    have : int_fract_pair.of ifp_n_fr⁻¹ = ifp_succ_n,
    { simpa [this, int_fract_pair.stream, nth_stream_eq, option.coe_def] using succ_nth_stream_eq },
    rwa ←this },
  exact (floor_le ifp_n.fr⁻¹)
end

end int_fract_pair

/-!
Next we translate above results about the stream of `int_fract_pair`s to the computed continued
fraction `generalized_continued_fraction.of`.
-/

/-- Shows that the integer parts of the continued fraction are at least one. -/
lemma of_one_le_nth_part_denom {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  1 ≤ b :=
begin
  obtain ⟨gp_n,  nth_s_eq, ⟨-⟩⟩ : ∃ gp_n, (gcf.of v).s.nth n = some gp_n ∧ gp_n.b = b, from
    exists_s_b_of_part_denom nth_part_denom_eq,
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b, from
      int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq,
  rw [←ifp_n_b_eq_gp_n_b],
  exact_mod_cast (int_fract_pair.one_le_succ_nth_stream_b succ_nth_stream_eq)
end

/--
Shows that the partial numerators `aᵢ` of the continued fraction are equal to one and the partial
denominators `bᵢ` correspond to integers.
-/
lemma of_part_num_eq_one_and_exists_int_part_denom_eq {gp : gcf.pair K}
  (nth_s_eq : (gcf.of v).s.nth n = some gp) :
  gp.a = 1 ∧ ∃ (z : ℤ), gp.b = (z : K) :=
begin
  obtain ⟨ifp, stream_succ_nth_eq, -⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ _,
      from int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq,
  have : gp = ⟨1, ifp.b⟩, by
  { have : (gcf.of v).s.nth n = some ⟨1, ifp.b⟩, from
      nth_of_eq_some_of_succ_nth_int_fract_pair_stream stream_succ_nth_eq,
    have : some gp = some ⟨1, ifp.b⟩, by rwa nth_s_eq at this,
    injection this },
  finish
end

/-- Shows that the partial numerators `aᵢ` are equal to one. -/
lemma of_part_num_eq_one {a : K} (nth_part_num_eq : (gcf.of v).partial_numerators.nth n = some a) :
  a = 1 :=
begin
  obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : ∃ gp, (gcf.of v).s.nth n = some gp ∧ gp.a = a, from
    exists_s_a_of_part_num nth_part_num_eq,
  have : gp.a = 1, from (of_part_num_eq_one_and_exists_int_part_denom_eq nth_s_eq).left,
  rwa gp_a_eq_a_n at this
end

/-- Shows that the partial denominators `bᵢ` correspond to an integer. -/
lemma exists_int_eq_of_part_denom {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  ∃ (z : ℤ), b = (z : K) :=
begin
  obtain ⟨gp, nth_s_eq, gp_b_eq_b_n⟩ : ∃ gp, (gcf.of v).s.nth n = some gp ∧ gp.b = b, from
    exists_s_b_of_part_denom nth_part_denom_eq,
  have : ∃ (z : ℤ), gp.b = (z : K), from
    (of_part_num_eq_one_and_exists_int_part_denom_eq nth_s_eq).right,
  rwa gp_b_eq_b_n at this
end

/-!
One of our next goals is to show that `bₙ * Bₙ ≤ Bₙ₊₁`. For this, we first show that the partial
denominators `Bₙ` are bounded from below by the fibonacci sequence `nat.fib`. This then implies that
`0 ≤ Bₙ` and hence `Bₙ₊₂ = bₙ₊₁ * Bₙ₊₁ + Bₙ ≥ bₙ₊₁ * Bₙ₊₁ + 0 = bₙ₊₁ * Bₙ₊₁`.
-/

-- open `nat` as we will make use of fibonacci numbers.
open nat

lemma fib_le_of_continuants_aux_b : (n ≤ 1 ∨ ¬(gcf.of v).terminated_at (n - 2)) →
  (fib n : K) ≤ ((gcf.of v).continuants_aux n).b :=
nat.strong_induction_on n
begin
  clear n,
  assume n IH hyp,
  rcases n with _|_|n,
  { simp [fib_succ_succ, continuants_aux] }, -- case n = 0
  { simp [fib_succ_succ, continuants_aux] }, -- case n = 1
  { let g := gcf.of v,  -- case 2 ≤ n
    have : ¬(n + 2 ≤ 1), by linarith,
    have not_terminated_at_n : ¬g.terminated_at n, from or.resolve_left hyp this,
    obtain ⟨gp, s_ppred_nth_eq⟩ : ∃ gp, g.s.nth n = some gp, from
      option.ne_none_iff_exists'.mp not_terminated_at_n,
    set pconts := g.continuants_aux (n + 1) with pconts_eq,
    set ppconts := g.continuants_aux n with ppconts_eq,
    -- use the recurrence of continuants_aux
    suffices : (fib n : K) + fib (n + 1) ≤ gp.a * ppconts.b + gp.b * pconts.b, by
      simpa [fib_succ_succ, add_comm,
        (continuants_aux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq)],
    -- make use of the fact that gp.a = 1
    suffices : (fib n : K) + fib (n + 1) ≤ ppconts.b + gp.b * pconts.b, by
      simpa [(of_part_num_eq_one $ part_num_eq_s_a s_ppred_nth_eq)],
    have not_terminated_at_pred_n : ¬g.terminated_at (n - 1), from
      mt (terminated_stable $ nat.sub_le n 1) not_terminated_at_n,
    have not_terminated_at_ppred_n : ¬terminated_at g (n - 2), from
      mt (terminated_stable (n - 1).pred_le) not_terminated_at_pred_n,
    -- use the IH to get the inequalities for `pconts` and `ppconts`
    have : (fib (n + 1) : K) ≤ pconts.b, from
      IH _ (nat.lt.base $ n + 1) (or.inr not_terminated_at_pred_n),
    have ppred_nth_fib_le_ppconts_B : (fib n : K) ≤ ppconts.b, from
      IH n (lt_trans (nat.lt.base n) $ nat.lt.base $ n + 1) (or.inr not_terminated_at_ppred_n),
    suffices : (fib (n + 1) : K) ≤ gp.b * pconts.b,
      solve_by_elim [add_le_add ppred_nth_fib_le_ppconts_B],
    -- finally use the fact that 1 ≤ gp.b to solve the goal
    suffices : 1 * (fib (n + 1) : K) ≤ gp.b * pconts.b, by rwa [one_mul] at this,
    have one_le_gp_b : (1 : K) ≤ gp.b, from
      of_one_le_nth_part_denom (part_denom_eq_s_b s_ppred_nth_eq),
    have : (0 : K) ≤ fib (n + 1), by exact_mod_cast (fib (n + 1)).zero_le,
    have : (0 : K) ≤ gp.b, from le_trans zero_le_one one_le_gp_b,
    mono }
end

/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number,
that is `nat.fib (n + 1) ≤ Bₙ`. -/
lemma succ_nth_fib_le_of_nth_denom (hyp: n = 0 ∨ ¬(gcf.of v).terminated_at (n - 1)) :
  (fib (n + 1) : K) ≤ (gcf.of v).denominators n :=
begin
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux],
  have : (n + 1) ≤ 1 ∨ ¬(gcf.of v).terminated_at (n - 1), by
  { cases n,
    case nat.zero : { exact (or.inl $ le_refl 1) },
    case nat.succ : { exact or.inr (or.resolve_left hyp n.succ_ne_zero) } },
  exact (fib_le_of_continuants_aux_b this)
end

/-! As a simple consequence, we can now derive that all denominators are nonnegative. -/

lemma zero_le_of_continuants_aux_b : 0 ≤ ((gcf.of v).continuants_aux n).b :=
begin
  let g := gcf.of v,
  induction n with n IH,
  case nat.zero: { refl },
  case nat.succ:
  { cases (decidable.em $ g.terminated_at (n - 1)) with terminated not_terminated,
    { cases n, -- terminating case
      { simp [zero_le_one] },
      { have : g.continuants_aux (n + 2) = g.continuants_aux (n + 1), from
          continuants_aux_stable_step_of_terminated terminated,
        simp only [this, IH] } },
    { calc -- non-terminating case
      (0 : K) ≤ fib (n + 1)                            : by exact_mod_cast (n + 1).fib.zero_le
          ... ≤ ((gcf.of v).continuants_aux (n + 1)).b : fib_le_of_continuants_aux_b
                                                           (or.inr not_terminated) } }
end

/-- Shows that all denominators are nonnegative. -/
lemma zero_le_of_denom : 0 ≤ (gcf.of v).denominators n :=
by { rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux], exact zero_le_of_continuants_aux_b }

lemma le_of_succ_succ_nth_continuants_aux_b {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  b * ((gcf.of v).continuants_aux $ n + 1).b ≤ ((gcf.of v).continuants_aux $ n + 2).b :=
begin
  set g := gcf.of v with g_eq,
  obtain ⟨gp_n, nth_s_eq, gpnb_eq_b⟩ : ∃ gp_n, g.s.nth n = some gp_n ∧ gp_n.b = b, from
    exists_s_b_of_part_denom nth_part_denom_eq,
  let conts := g.continuants_aux (n + 2),
  set pconts := g.continuants_aux (n + 1) with pconts_eq,
  set ppconts := g.continuants_aux n with ppconts_eq,
  -- use the recurrence of continuants_aux and the fact that gp_n.a = 1
  suffices : gp_n.b * pconts.b ≤ ppconts.b + gp_n.b * pconts.b, by
  { have : gp_n.a = 1, from of_part_num_eq_one (part_num_eq_s_a nth_s_eq),
    finish [gcf.continuants_aux_recurrence nth_s_eq ppconts_eq pconts_eq] },
  have : 0 ≤ ppconts.b, from zero_le_of_continuants_aux_b,
  solve_by_elim [le_add_of_nonneg_of_le, le_refl]
end

/-- Shows that `bₙ * Bₙ ≤ Bₙ₊₁`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem le_of_succ_nth_denom {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  b * (gcf.of v).denominators n ≤ (gcf.of v).denominators (n + 1) :=
begin
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux],
  exact (le_of_succ_succ_nth_continuants_aux_b nth_part_denom_eq)
end

/-- Shows that the sequence of denominators is monotone, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem of_denom_mono : (gcf.of v).denominators n ≤ (gcf.of v).denominators (n + 1) :=
begin
  let g := gcf.of v,
  cases (decidable.em $ g.partial_denominators.terminated_at n) with terminated not_terminated,
  { have : g.partial_denominators.nth n = none, by rwa seq.terminated_at at terminated,
    have : g.terminated_at n, from
      terminated_at_iff_part_denom_none.elim_right (by rwa seq.terminated_at at terminated),
    have : g.denominators (n + 1) = g.denominators n, from
      denominators_stable_of_terminated n.le_succ this,
    rw this },
  { obtain ⟨b, nth_part_denom_eq⟩ : ∃ b, g.partial_denominators.nth n = some b, from
      option.ne_none_iff_exists'.mp not_terminated,
    have : 1 ≤ b, from of_one_le_nth_part_denom nth_part_denom_eq,
    calc g.denominators n
        ≤ b * g.denominators n   : by simpa using (mul_le_mul_of_nonneg_right this zero_le_of_denom)
    ... ≤ g.denominators (n + 1) : le_of_succ_nth_denom nth_part_denom_eq }
end

section determinant
/-!
### Determinant Formula

Next we prove the so-called *determinant formula* for `generalized_continued_fraction.of`:
`Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)`.
-/

lemma determinant_aux (hyp: n = 0 ∨ ¬(gcf.of v).terminated_at (n - 1)) :
    ((gcf.of v).continuants_aux n).a * ((gcf.of v).continuants_aux (n + 1)).b
    - ((gcf.of v).continuants_aux n).b * ((gcf.of v).continuants_aux (n + 1)).a
  = (-1)^n :=
begin
  induction n with n IH,
  case nat.zero { simp [continuants_aux] },
  case nat.succ
  { -- set up some shorthand notation
    let g := gcf.of v,
    let conts := continuants_aux g (n + 2),
    set pred_conts := continuants_aux g (n + 1) with pred_conts_eq,
    set ppred_conts := continuants_aux g n with ppred_conts_eq,
    let pA := pred_conts.a,
    let pB := pred_conts.b,
    let ppA := ppred_conts.a,
    let ppB := ppred_conts.b,
    -- let's change the goal to something more readable
    change pA * conts.b - pB * conts.a = (-1)^(n + 1),
    have not_terminated_at_n : ¬terminated_at g n, from or.resolve_left hyp n.succ_ne_zero,
    obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.nth n = some gp, from
      option.ne_none_iff_exists'.elim_left not_terminated_at_n,
    -- unfold the recurrence relation for `conts` once and simplify to derive the following
    suffices : pA * (ppB + gp.b * pB) - pB * (ppA + gp.b * pA) = (-1)^(n + 1), by
    { simp only [conts, (continuants_aux_recurrence s_nth_eq ppred_conts_eq pred_conts_eq)],
      have gp_a_eq_one : gp.a = 1, from of_part_num_eq_one (part_num_eq_s_a s_nth_eq),
      rw [gp_a_eq_one, this.symm],
      ring },
    suffices : pA * ppB - pB * ppA = (-1)^(n + 1), calc
      pA * (ppB + gp.b * pB) - pB * (ppA + gp.b * pA)
          = pA * ppB + pA * gp.b * pB - pB * ppA - pB * gp.b * pA : by ring
      ... = pA * ppB - pB * ppA                                   : by ring
      ... = (-1)^(n + 1)                                          : by assumption,
    suffices : ppA * pB - ppB * pA = (-1)^n, by
    { have pow_succ_n : (-1 : K)^(n + 1) = (-1) * (-1)^n, from pow_succ (-1) n,
      rw [pow_succ_n, ←this],
      ring },
    exact (IH $ or.inr $ mt (terminated_stable $ n.sub_le 1) not_terminated_at_n) }
end

/-- The determinant formula `Aₙ * Bₙ₊₁ - Bₙ * Aₙ₊₁ = (-1)^(n + 1)` -/
lemma determinant (not_terminated_at_n : ¬(gcf.of v).terminated_at n) :
    (gcf.of v).numerators n * (gcf.of v).denominators (n + 1)
    - (gcf.of v).denominators n * (gcf.of v).numerators (n + 1)
  = (-1)^(n + 1) :=
(determinant_aux $ or.inr $ not_terminated_at_n)

end determinant

section error_term
/-!
### Approximation of Error Term

Next we derive some approximations for the error term when computing a continued fraction up a given
position, i.e. bounds for the term `|v - (generalized_continued_fraction.of v).convergents n|`.
-/

/-- This lemma follows from the finite correctness proof, the determinant equality, and
by simplifying the difference. -/
lemma sub_convergents_eq {ifp : int_fract_pair K}
  (stream_nth_eq : int_fract_pair.stream v n = some ifp) :
  let g := gcf.of v in
  let B := (g.continuants_aux (n + 1)).b in
  let pB := (g.continuants_aux n).b in
  v - g.convergents n = if ifp.fr = 0 then 0 else (-1)^n / (B * (ifp.fr⁻¹ * B + pB)) :=
begin
  -- set up some shorthand notation
  let g := gcf.of v,
  let conts := g.continuants_aux (n + 1),
  let pred_conts := g.continuants_aux n,
  have g_finite_correctness : v = gcf.comp_exact_value pred_conts conts ifp.fr, from
    comp_exact_value_correctness_of_stream_eq_some stream_nth_eq,
  cases decidable.em (ifp.fr = 0) with ifp_fr_eq_zero ifp_fr_ne_zero,
  { suffices : v - g.convergents n = 0, by simpa [ifp_fr_eq_zero],
    replace g_finite_correctness : v = g.convergents n, by
      simpa [gcf.comp_exact_value, ifp_fr_eq_zero] using g_finite_correctness,
    exact (sub_eq_zero.elim_right g_finite_correctness) },
  { -- more shorthand notation
    let A := conts.a,
    let B := conts.b,
    let pA := pred_conts.a,
    let pB := pred_conts.b,
    -- first, let's simplify the goal as `ifp.fr ≠ 0`
    suffices : v - A / B = (-1)^n / (B * (ifp.fr⁻¹ * B + pB)), by simpa [ifp_fr_ne_zero],
    -- now we can unfold `g.comp_exact_value` to derive the following equality for `v`
    replace g_finite_correctness : v = (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B), by
      simpa [gcf.comp_exact_value, ifp_fr_ne_zero, next_continuants, next_numerator,
          next_denominator, add_comm] using g_finite_correctness,
    -- let's rewrite this equality for `v` in our goal
    suffices : (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) - A / B
             = (-1)^n / (B * (ifp.fr⁻¹ * B + pB)), by rwa g_finite_correctness,
    -- To continue, we need use the determinant equality. So let's derive the needed hypothesis.
    have n_eq_zero_or_not_terminated_at_pred_n : n = 0 ∨ ¬g.terminated_at (n - 1), by
    { cases n with n',
      { simp },
      { have : int_fract_pair.stream v (n' + 1) ≠ none, by simp [stream_nth_eq],
        have : ¬g.terminated_at n', from
          (not_iff_not_of_iff of_terminated_at_n_iff_succ_nth_int_fract_pair_stream_eq_none)
          .elim_right this,
        exact (or.inr this) } },
    have determinant_eq : pA * B - pB * A = (-1)^n, from
      determinant_aux n_eq_zero_or_not_terminated_at_pred_n,
    -- now all we got to do is to rewrite this equality in our goal and re-arrange terms;
    -- however, for this, we first have to derive quite a few tedious inequalities.
    have pB_ineq : (fib n : K) ≤ pB, by
    { have : n ≤ 1 ∨ ¬g.terminated_at (n - 2), by
      { cases n_eq_zero_or_not_terminated_at_pred_n with n_eq_zero not_terminated_at_pred_n,
        { simp [n_eq_zero] },
        { exact (or.inr $ mt (terminated_stable (n - 1).pred_le) not_terminated_at_pred_n) } },
      exact (fib_le_of_continuants_aux_b this) },
    have B_ineq : (fib (n + 1) : K) ≤ B, by
    { have : n + 1 ≤ 1 ∨ ¬g.terminated_at (n + 1 - 2), by
      { cases n_eq_zero_or_not_terminated_at_pred_n with n_eq_zero not_terminated_at_pred_n,
        { simp [n_eq_zero, le_refl] },
        { exact (or.inr not_terminated_at_pred_n) } },
      exact (fib_le_of_continuants_aux_b this) },
    have zero_lt_B : 0 < B,
    { have : 1 ≤ B, from
        le_trans
        (by exact_mod_cast fib_pos (lt_of_le_of_ne n.succ.zero_le n.succ_ne_zero.symm)) B_ineq,
      exact (lt_of_lt_of_le zero_lt_one this) },
    have zero_ne_B : 0 ≠ B, from ne_of_lt zero_lt_B,
    have : 0 ≠ pB + ifp.fr⁻¹ * B, by
    { have : (0 : K) ≤ fib n, by exact_mod_cast (fib n).zero_le,
      -- 0 ≤ fib n ≤ pB
      have zero_le_pB : 0 ≤ pB, from le_trans this pB_ineq,
      have : 0 < ifp.fr⁻¹, by
      { suffices : 0 < ifp.fr, by rwa inv_pos,
        have : 0 ≤ ifp.fr, from int_fract_pair.nth_stream_fr_nonneg stream_nth_eq,
        change ifp.fr ≠ 0 at ifp_fr_ne_zero,
        exact lt_of_le_of_ne this ifp_fr_ne_zero.symm },
      have : 0 < ifp.fr⁻¹ * B, from mul_pos this zero_lt_B,
      have : 0 < pB + ifp.fr⁻¹ * B, from add_pos_of_nonneg_of_pos zero_le_pB this,
      exact (ne_of_lt this) },
    -- finally, let's do the rewriting
    calc
      (pA + ifp.fr⁻¹ * A) / (pB + ifp.fr⁻¹ * B) - A / B
          = ((pA + ifp.fr⁻¹ * A) * B - (pB + ifp.fr⁻¹ * B) * A)
            / ((pB + ifp.fr⁻¹ * B) * B)                             : by rw (div_sub_div _ _
                                                                           this.symm zero_ne_B.symm)
      ... = (pA * B + ifp.fr⁻¹ * A * B - (pB * A + ifp.fr⁻¹ * B * A))
            / _                                                     : by repeat { rw [add_mul] }
      ... = (pA * B - pB * A) / ((pB + ifp.fr⁻¹ * B) * B)           : by ring
      ... = (-1)^n / ((pB + ifp.fr⁻¹ * B) * B)                      : by rw determinant_eq
      ... = (-1)^n / (B * (ifp.fr⁻¹ * B + pB))                      : by ac_refl }
end

local notation `|` x `|` := abs x

/-- Shows that `|v - Aₙ / Bₙ| ≤ 1 / (Bₙ * Bₙ₊₁)` -/
theorem abs_sub_convergents_le (not_terminated_at_n : ¬(gcf.of v).terminated_at n) :
    |v - (gcf.of v).convergents n|
  ≤ 1 / (((gcf.of v).denominators n) * ((gcf.of v).denominators $ n + 1)) :=
begin
  -- shorthand notation
  let g := gcf.of v,
  let nextConts := g.continuants_aux (n + 2),
  set conts := continuants_aux g (n + 1) with conts_eq,
  set pred_conts := continuants_aux g n with pred_conts_eq,
  -- change the goal to something more readable
  change |v - convergents g n| ≤ 1 / (conts.b * nextConts.b),
  obtain ⟨gp, s_nth_eq⟩ : ∃ gp, g.s.nth n = some gp, from
    option.ne_none_iff_exists'.elim_left not_terminated_at_n,
  have gp_a_eq_one : gp.a = 1, from of_part_num_eq_one (part_num_eq_s_a s_nth_eq),
  -- unfold the recurrence relation for `nextConts.b`
  have nextConts_b_eq : nextConts.b = pred_conts.b + gp.b * conts.b, by
    simp [nextConts, (continuants_aux_recurrence s_nth_eq pred_conts_eq conts_eq), gp_a_eq_one,
      pred_conts_eq.symm, conts_eq.symm, add_comm],
  let denom := conts.b * (pred_conts.b + gp.b * conts.b),
  suffices : |v - g.convergents n| ≤ 1 / denom, by { rw [nextConts_b_eq], congr' 1 },
  obtain ⟨ifp_succ_n, succ_nth_stream_eq, ifp_succ_n_b_eq_gp_b⟩ :
    ∃ ifp_succ_n, int_fract_pair.stream v (n + 1)
                = some ifp_succ_n ∧ (ifp_succ_n.b : K) = gp.b, from
      int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some s_nth_eq,
  obtain ⟨ifp_n, stream_nth_eq, stream_nth_fr_ne_zero, if_of_eq_ifp_succ_n⟩ :
    ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
           ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n, from
      int_fract_pair.succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq,
  let denom' := conts.b * (pred_conts.b + ifp_n.fr⁻¹ * conts.b),
  -- now we can use `sub_convergents_eq` to simplify our goal
  suffices : |(-1)^n / denom'| ≤ 1 / denom, by
  { have : v - g.convergents n = (-1)^n / denom', by
    { -- apply `sub_convergens_eq` and simplify the result
      have tmp, from sub_convergents_eq stream_nth_eq,
      delta at tmp,
      simp only [stream_nth_fr_ne_zero, conts_eq.symm, pred_conts_eq.symm] at tmp,
      rw tmp,
      simp only [denom'],
      ring_nf,
      ac_refl },
    rwa this },
  -- derive some tedious inequalities that we need to rewrite our goal
  have nextConts_b_ineq : (fib (n + 2) : K) ≤ (pred_conts.b + gp.b * conts.b), by
  { have : (fib (n + 2) : K) ≤ nextConts.b, from
      fib_le_of_continuants_aux_b (or.inr not_terminated_at_n),
    rwa [nextConts_b_eq] at this },
  have conts_b_ineq : (fib (n + 1) : K) ≤ conts.b, by
  { have : ¬g.terminated_at (n - 1), from mt (terminated_stable n.pred_le) not_terminated_at_n,
    exact (fib_le_of_continuants_aux_b $ or.inr this) },
  have zero_lt_conts_b : 0 < conts.b, by
  { have : (0 : K) < fib (n + 1), by
      exact_mod_cast (fib_pos (lt_of_le_of_ne n.succ.zero_le n.succ_ne_zero.symm)),
    exact (lt_of_lt_of_le this conts_b_ineq) },
  -- `denom'` is positive, so we can remove `|⬝|` from our goal
  suffices : 1 / denom' ≤ 1 / denom, by
  { have : |(-1)^n / denom'| = 1 / denom', by
    { suffices : 1 / |denom'| = 1 / denom', by rwa [abs_div, (abs_neg_one_pow n)],
      have : 0 < denom', by
      { have : 0 ≤ pred_conts.b, by
        { have : (fib n : K) ≤ pred_conts.b, by
          { have : ¬g.terminated_at (n - 2), from
              mt (terminated_stable (n.sub_le 2)) not_terminated_at_n,
            exact (fib_le_of_continuants_aux_b $ or.inr this) },
          exact le_trans (by exact_mod_cast (fib n).zero_le) this },
        have : 0 < ifp_n.fr⁻¹, by
        { have zero_le_ifp_n_fract : 0 ≤ ifp_n.fr, from
            int_fract_pair.nth_stream_fr_nonneg stream_nth_eq,
          exact inv_pos.elim_right
            (lt_of_le_of_ne zero_le_ifp_n_fract stream_nth_fr_ne_zero.symm) },
        any_goals { repeat { apply mul_pos <|> apply add_pos_of_nonneg_of_pos } }; assumption },
      rwa (abs_of_pos this) },
    rwa this },
  suffices : 0 < denom ∧ denom ≤ denom', from
    div_le_div_of_le_left zero_le_one this.left this.right,
  split,
  { have : 0 < pred_conts.b + gp.b * conts.b, from
      lt_of_lt_of_le
      (by exact_mod_cast (fib_pos (lt_of_le_of_ne n.succ.succ.zero_le n.succ.succ_ne_zero.symm)))
      nextConts_b_ineq,
    solve_by_elim [mul_pos] },
  { -- we can cancel multiplication by `conts.b` and addition with `pred_conts.b`
    suffices : gp.b * conts.b ≤ ifp_n.fr⁻¹ * conts.b, from
      ((mul_le_mul_left zero_lt_conts_b).elim_right $
        (add_le_add_iff_left pred_conts.b).elim_right this),
    suffices : (ifp_succ_n.b : K) * conts.b ≤ ifp_n.fr⁻¹ * conts.b, by rwa [←ifp_succ_n_b_eq_gp_b],
    have : (ifp_succ_n.b : K) ≤ ifp_n.fr⁻¹, from
      int_fract_pair.succ_nth_stream_b_le_nth_stream_fr_inv stream_nth_eq succ_nth_stream_eq,
    have : 0 ≤ conts.b, from le_of_lt zero_lt_conts_b,
    mono }
end

/--
Shows that `|v - Aₙ / Bₙ| ≤ 1 / (bₙ * Bₙ * Bₙ)`. This bound is worse than the one shown in
`gcf.abs_sub_convergents_le`, but sometimes it is easier to apply and sufficient for one's use case.
 -/
lemma abs_sub_convergents_le' {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
    |v - (gcf.of v).convergents n|
  ≤ 1 / (b * ((gcf.of v).denominators n) * ((gcf.of v).denominators n)) :=
begin
  let g := gcf.of v,
  let B := g.denominators n,
  let nB := g.denominators (n + 1),
  have not_terminated_at_n : ¬g.terminated_at n, by
  { have : g.partial_denominators.nth n ≠ none, by simp [nth_part_denom_eq],
    exact (not_iff_not_of_iff terminated_at_iff_part_denom_none).elim_right this },
  suffices : 1 / (B * nB) ≤ (1 : K) / (b * B * B), by
  { have : |v - g.convergents n| ≤ 1 / (B * nB), from abs_sub_convergents_le not_terminated_at_n,
    transitivity;
    assumption },
  -- derive some inequalities needed to show the claim
  have zero_lt_B : 0 < B, by
  { have : (fib (n + 1) : K) ≤ B, from
      succ_nth_fib_le_of_nth_denom (or.inr $
        mt (terminated_stable n.pred_le) not_terminated_at_n),
    exact (lt_of_lt_of_le
      (by exact_mod_cast (fib_pos (lt_of_le_of_ne n.succ.zero_le n.succ_ne_zero.symm))) this) },
  have denoms_ineq : b * B * B ≤ B * nB, by
  { have : b * B ≤ nB, from le_of_succ_nth_denom nth_part_denom_eq,
    rwa [(mul_comm B nB), (mul_le_mul_right zero_lt_B)] },
  have : (0 : K) < b * B * B, by
  { have : 0 < b, from lt_of_lt_of_le zero_lt_one (of_one_le_nth_part_denom nth_part_denom_eq),
    any_goals { repeat { apply mul_pos } }; assumption },
  exact (div_le_div_of_le_left zero_le_one this denoms_ineq)
end

end error_term

end generalized_continued_fraction
