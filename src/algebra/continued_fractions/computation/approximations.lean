/-
Copyright (c) 2020 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.computation.translations
import algebra.continued_fractions.continuants_recurrence
import algebra.continued_fractions.terminated_stable
import data.nat.fib
/-!
# Approximations for Continued Fraction Computations (`gcf.of`)

## Summary

Let us write `gcf` for `generalized_continued_fraction`. This file contains useful approximations
for the values involved in the continued fractions computation `gcf.of`.

## Main Theorems

- `gcf.of_part_num_eq_one`: shows that all partial numerators `aᵢ` are equal to one.
- `gcf.of_part_denom_corr_int`: shows that all partial denominators `bᵢ` correspond to an integer.
- `gcf.of_one_le_nth_part_denom`: shows that `1 ≤ bᵢ`.
- `gcf.of_succ_nth_fib_le_nth_denom`: shows that the `n`th denominator `Bₙ` is greater than or equal to
  the `n + 1`th fibonacci number `nat.fib (n + 1)`.
- `gcf.of_le_succ_nth_denom`: shows that `Bₙ₊₁ ≥ bₙ * Bₙ`, where `bₙ` is the `n`th partial denominator
  of the continued fraction.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf

variables {K : Type*} {v : K} {n : ℕ} [discrete_linear_ordered_field K] [floor_ring K]

/-
We begin with some lemmas about the stream of `int_fract_pair`s, which presumably are not
of great interest for the end user.
-/
namespace int_fract_pair

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
  { rcases (succ_nth_stream_eq_some_iff.elim_left nth_stream_eq) with ⟨_, _, _, if_of_eq_ifp_n⟩,
    simp [fract_lt_one, fract_nonneg, int_fract_pair.of, if_of_eq_ifp_n.symm] }
end

/-- Shows that the fractional parts of the stream are nonnegative. -/
lemma fr_nonneg {ifp_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  0 ≤ ifp_n.fr :=
(nth_stream_fr_nonneg_lt_one nth_stream_eq).left

/-- Shows that the fractional parts of the stream smaller than one. -/
lemma fr_lt_one {ifp_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  ifp_n.fr < 1 :=
(nth_stream_fr_nonneg_lt_one nth_stream_eq).right

/-- Shows that the integer parts of the stream are at least one. -/
lemma one_le_succ_nth_stream_b {ifp_succ_n : int_fract_pair K}
  (succ_nth_stream_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) :
  1 ≤ ifp_succ_n.b :=
begin
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨refl⟩⟩ :
    ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
    ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n, from
      succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq,
  change 1 ≤ ⌊ifp_n.fr⁻¹⌋,
  suffices : 1 ≤ ifp_n.fr⁻¹, by { rw_mod_cast [le_floor], assumption },
  have : 0 ≤ ifp_n.fr ∧ ifp_n.fr < 1, from nth_stream_fr_nonneg_lt_one nth_stream_eq,
  cases this with ifp_n_fract_nonneg ifp_n_fract_lt_one,
  suffices : 1 * ifp_n.fr ≤ 1, by
  { rw inv_eq_one_div,
    have : 0 < ifp_n.fr, from lt_of_le_of_ne ifp_n_fract_nonneg stream_nth_fr_ne_zero.symm,
    solve_by_elim [le_div_of_mul_le], },
  simp [(le_of_lt ifp_n_fract_lt_one)]
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
  suffices : (⌊ifp_n.fr⁻¹⌋ : K) ≤ ifp_n.fr⁻¹, by
  { cases ifp_n with _ ifp_n_fr,
    have : ifp_n_fr ≠ 0, by
      { intro h, simpa [h, int_fract_pair.stream, nth_stream_eq] using succ_nth_stream_eq },
    have : int_fract_pair.of ifp_n_fr⁻¹ = ifp_succ_n, by
    { rw with_one.coe_inj.symm,
      simpa [this, int_fract_pair.stream, nth_stream_eq] using succ_nth_stream_eq },
    rwa ←this },
  exact (floor_le ifp_n.fr⁻¹)
end

end int_fract_pair

/-
Next we translate above results about the stream of `int_fract_pair`s to the computed continued
fraction `gcf.of`.
-/

/-- Shows that the integer parts of the continued fraction are at least one. -/
lemma of_one_le_nth_part_denom {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  1 ≤ b :=
begin
  obtain ⟨gp_n,  nth_s_eq, ⟨refl⟩⟩ : ∃ gp_n, (gcf.of v).s.nth n = some gp_n ∧ gp_n.b = b, from
    obtain_s_b_of_part_denom nth_part_denom_eq,
  obtain ⟨ifp_n, succ_nth_stream_eq, ifp_n_b_eq_gp_n_b⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp_n.b, from
      int_fract_pair.obtain_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq,
  rw [←ifp_n_b_eq_gp_n_b],
  exact_mod_cast (int_fract_pair.one_le_succ_nth_stream_b succ_nth_stream_eq)
end

/--
Shows that the partial numerators `aᵢ` of the continued fraction are equal to one and the partial
denominators `bᵢ` correspond to integers.
-/
lemma of_part_num_eq_one_and_part_denom_corr_int {gp : gcf.pair K}
  (nth_s_eq : (gcf.of v).s.nth n = some gp) :
  gp.a = 1 ∧ ∃ (z : ℤ), gp.b = (z : K) :=
begin
  obtain ⟨ifp, stream_succ_nth_eq, ifp_b_eq_gp_b⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp.b,
      from int_fract_pair.obtain_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq,
  have : (gcf.of v).s.nth n = some ⟨1, ifp.b⟩, from
    nth_of_eq_some_of_succ_nth_int_fract_pair_stream stream_succ_nth_eq,
  have : some gp = some ⟨1, ifp.b⟩, by rwa nth_s_eq at this,
  have : gp = ⟨1, ifp.b⟩, by injection this,
  -- We know the shape of gp, so now we just have to split the goal and use this knowledge.
  cases gp,
  split,
  { injection this },
  { existsi ifp.b, injection this }
end

/-- Shows that the partial numerators `aᵢ` are equal to one. -/
lemma of_part_num_eq_one {a : K} (nth_part_num_eq : (gcf.of v).partial_numerators.nth n = some a) :
  a = 1 :=
begin
  obtain ⟨gp, nth_s_eq, gp_a_eq_a_n⟩ : ∃ gp, (gcf.of v).s.nth n = some gp ∧ gp.a = a, from
    obtain_s_a_of_part_num nth_part_num_eq,
  have : gp.a = 1, from (of_part_num_eq_one_and_part_denom_corr_int nth_s_eq).left,
  rwa gp_a_eq_a_n at this
end

/-- Shows that the partial denominators `bᵢ` correspond to an integer. -/
lemma of_part_denom_corr_int {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  ∃ (z : ℤ), b = (z : K) :=
begin
  obtain ⟨gp, nth_s_eq, gp_b_eq_b_n⟩ : ∃ gp, (gcf.of v).s.nth n = some gp ∧ gp.b = b, from
    obtain_s_b_of_part_denom nth_part_denom_eq,
  have : ∃ (z : ℤ), gp.b = (z : K), from (of_part_num_eq_one_and_part_denom_corr_int nth_s_eq).right,
  rwa gp_b_eq_b_n at this
end

/-
Our next goal is to show that `Bₙ₊₁ ≥ bₙ * Bₙ`. For this, we first show that the partial denominators
`Bₙ` grow quicker than the fibonacci sequence `nat.fib`.
-/

-- open `nat` as we will make use of fibonacci numbers.
open nat

lemma of_fib_le_continuants_aux_b : (n ≤ 1 ∨ ¬(gcf.of v).terminated_at (n - 2)) →
  (fib n : K) ≤ ((gcf.of v).continuants_aux n).b :=
nat.strong_induction_on n
(begin
  clear n,
  assume n IH hyp,
  cases n with n',
  case nat.zero { simp [fib_succ_succ, continuants_aux] },
  case nat.succ
  { cases n' with n'',
    { simp [fib_succ_succ, continuants_aux] }, -- case n = 1
    { let g := gcf.of v,  -- case 2 ≤ n
      have : ¬(n'' + 2 ≤ 1), by linarith,
      have not_terminated_at_n'' : ¬g.terminated_at n'', from or.resolve_left hyp this,
      obtain ⟨gp, s_ppred_nth_eq⟩ : ∃ gp, g.s.nth n'' = some gp, from
        with_one.ne_one_iff_exists.elim_left not_terminated_at_n'',
      set pconts := g.continuants_aux (n'' + 1) with pconts_eq,
      set ppconts := g.continuants_aux n'' with ppconts_eq,
      -- use the recurrence of continuants_aux
      suffices : (fib n'' : K) + fib (n'' + 1) ≤ gp.a * ppconts.b + gp.b * pconts.b, by
        simpa [fib_succ_succ, add_comm,
          (continuants_aux_recurrence s_ppred_nth_eq ppconts_eq pconts_eq)],
      -- make use of the fact that gp.a = 1
      suffices : (fib n'' : K) + fib (n'' + 1) ≤ ppconts.b + gp.b * pconts.b, by
        simpa [(of_part_num_eq_one $ part_num_eq_s_a s_ppred_nth_eq)],
      have not_terminated_at_pred_n'' : ¬g.terminated_at (n'' - 1), from
        mt (terminated_stable $ nat.sub_le n'' 1) not_terminated_at_n'',
      have not_termianted_at_ppred_n'' : ¬terminated_at g (n'' - 2), from
        mt (terminated_stable (n'' - 1).pred_le) not_terminated_at_pred_n'',
      -- use the IH to get the inequalities for `pconts` and `ppconts`
      have : (fib (n'' + 1) : K) ≤ pconts.b, from
        IH _ (nat.lt.base $ n'' + 1) (or.inr not_terminated_at_pred_n''),
      have ppred_nth_fib_le_ppconts_B : (fib n'' : K) ≤ ppconts.b, from
        IH n'' (lt_trans (nat.lt.base n'') $ nat.lt.base $ n'' + 1)
        (or.inr not_termianted_at_ppred_n''),
      suffices : (fib (n'' + 1) : K) ≤ gp.b * pconts.b,
        solve_by_elim [(add_le_add ppred_nth_fib_le_ppconts_B)],
      -- finally use the fact that 1 ≤ gp.b to solve the goal
      suffices : 1 * (fib (n'' + 1) : K) ≤ gp.b * pconts.b, by rwa [one_mul] at this,
      have one_le_gp_b : (1 : K) ≤ gp.b, from
        of_one_le_nth_part_denom (part_denom_eq_s_b s_ppred_nth_eq),
      have : (0 : K) ≤ fib (n'' + 1), by exact_mod_cast (fib (n'' + 1)).zero_le,
      have : (0 : K) ≤ gp.b, from le_trans zero_le_one one_le_gp_b,
      mono }}
end)

/-- Shows that the `n`th denominator is greater than or equal to the `n + 1`th fibonacci number, that is
`nat.fib (n + 1) ≤ Bₙ`. -/
lemma of_succ_nth_fib_le_nth_denom (hyp: n = 0 ∨ ¬(gcf.of v).terminated_at (n - 1)) :
  (fib (n + 1) : K) ≤ (gcf.of v).denominators n :=
begin
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux],
  have : (n + 1) ≤ 1 ∨ ¬(gcf.of v).terminated_at (n - 1), by
  { cases n,
    case nat.zero : { exact (or.inl $ le_refl 1) },
    case nat.succ : { exact or.inr (or.resolve_left hyp n.succ_ne_zero) }},
  exact (of_fib_le_continuants_aux_b this)
end

lemma of_le_succ_succ_nth_continuants_aux_b {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  b * ((gcf.of v).continuants_aux $ n + 1).b ≤ ((gcf.of v).continuants_aux $ n + 2).b :=
begin
  set g := gcf.of v with g_eq,
  obtain ⟨gp_n, nth_s_eq, ⟨refl⟩⟩ : ∃ gp_n, g.s.nth n = some gp_n ∧ gp_n.b = b, from
    obtain_s_b_of_part_denom nth_part_denom_eq,
  let conts := g.continuants_aux (n + 2),
  set pconts := g.continuants_aux (n + 1) with pconts_eq,
  set ppconts := g.continuants_aux n with ppconts_eq,
  -- use the recurrence of continuants_aux and the fact that gp_n.a = 1
  suffices : gp_n.b * pconts.b ≤ ppconts.b + gp_n.b * pconts.b, by
  { have : gp_n.a = 1, from of_part_num_eq_one (part_num_eq_s_a nth_s_eq),
    finish [(gcf.continuants_aux_recurrence nth_s_eq ppconts_eq pconts_eq)] },
  have : 0 ≤ ppconts.b, by
  { have not_terminated_at_pred_n : ¬g.terminated_at (n - 1), by
    { have : ¬g.terminated_at n, by { have : g.s.nth n ≠ none, by simp [nth_s_eq], exact this },
      exact (mt (terminated_stable n.pred_le) this) },
    have : (fib n : K) ≤ ppconts.b, by
    { have : ¬g.terminated_at (n - 2), from
        mt (terminated_stable (n - 1).pred_le) not_terminated_at_pred_n,
      exact (of_fib_le_continuants_aux_b $ or.inr this) },
    exact le_trans (by exact_mod_cast (fib n).zero_le) this },
  solve_by_elim [le_add_of_nonneg_of_le, le_refl]
end

/-- Shows that `Bₙ₊₁ ≥ bₙ * Bₙ`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem of_le_succ_nth_denom {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  b * (gcf.of v).denominators n ≤ (gcf.of v).denominators (n + 1) :=
begin
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux],
  exact (of_le_succ_succ_nth_continuants_aux_b nth_part_denom_eq)
end

end generalized_continued_fraction
