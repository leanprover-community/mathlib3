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
- `gcf.exists_int_eq_of_part_denom`: shows that all partial denominators `bᵢ` correspond to an
  integer.
- `gcf.one_le_of_nth_part_denom`: shows that `1 ≤ bᵢ`.
- `gcf.succ_nth_fib_le_of_nth_denom`: shows that the `n`th denominator `Bₙ` is greater than or equal
  to the `n + 1`th fibonacci number `nat.fib (n + 1)`.
- `gcf.le_of_succ_nth_denom`: shows that `Bₙ₊₁ ≥ bₙ * Bₙ`, where `bₙ` is the `n`th partial
  denominator of the continued fraction.

## References

- [*Hardy, GH and Wright, EM and Heath-Brown, Roger and Silverman, Joseph*][hardy2008introduction]
-/

namespace generalized_continued_fraction
open generalized_continued_fraction as gcf

variables {K : Type*} {v : K} {n : ℕ} [linear_ordered_field K] [floor_ring K]

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
lemma nth_stream_fr_nonneg {ifp_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  0 ≤ ifp_n.fr :=
(nth_stream_fr_nonneg_lt_one nth_stream_eq).left

/-- Shows that the fractional parts of the stream smaller than one. -/
lemma nth_stream_fr_lt_one {ifp_n : int_fract_pair K}
  (nth_stream_eq : int_fract_pair.stream v n = some ifp_n) :
  ifp_n.fr < 1 :=
(nth_stream_fr_nonneg_lt_one nth_stream_eq).right

/-- Shows that the integer parts of the stream are at least one. -/
lemma one_le_succ_nth_stream_b {ifp_succ_n : int_fract_pair K}
  (succ_nth_stream_eq : int_fract_pair.stream v (n + 1) = some ifp_succ_n) :
  1 ≤ ifp_succ_n.b :=
begin
  obtain ⟨ifp_n, nth_stream_eq, stream_nth_fr_ne_zero, ⟨_⟩⟩ :
    ∃ ifp_n, int_fract_pair.stream v n = some ifp_n ∧ ifp_n.fr ≠ 0
    ∧ int_fract_pair.of ifp_n.fr⁻¹ = ifp_succ_n, from
      succ_nth_stream_eq_some_iff.elim_left succ_nth_stream_eq,
  change 1 ≤ ⌊ifp_n.fr⁻¹⌋,
  suffices : 1 ≤ ifp_n.fr⁻¹, { rw_mod_cast [le_floor], assumption },
  suffices : ifp_n.fr ≤ 1,
  { have h : 0 < ifp_n.fr :=
      lt_of_le_of_ne (nth_stream_fr_nonneg nth_stream_eq) stream_nth_fr_ne_zero.symm,
    apply one_le_inv h this },
  simp [(le_of_lt (nth_stream_fr_lt_one nth_stream_eq))]
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

/-
Next we translate above results about the stream of `int_fract_pair`s to the computed continued
fraction `gcf.of`.
-/

/-- Shows that the integer parts of the continued fraction are at least one. -/
lemma of_one_le_nth_part_denom {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  1 ≤ b :=
begin
  obtain ⟨gp_n,  nth_s_eq, ⟨_⟩⟩ : ∃ gp_n, (gcf.of v).s.nth n = some gp_n ∧ gp_n.b = b, from
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
  obtain ⟨ifp, stream_succ_nth_eq, ifp_b_eq_gp_b⟩ :
    ∃ ifp, int_fract_pair.stream v (n + 1) = some ifp ∧ (ifp.b : K) = gp.b,
      from int_fract_pair.exists_succ_nth_stream_of_gcf_of_nth_eq_some nth_s_eq,
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

/-
One of our next goals is to show that `Bₙ₊₁ ≥ bₙ * Bₙ`. For this, we first show that the partial
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
      IH n (lt_trans (nat.lt.base n) $ nat.lt.base $ n + 1)
      (or.inr not_terminated_at_ppred_n),
    suffices : (fib (n + 1) : K) ≤ gp.b * pconts.b,
      solve_by_elim [(add_le_add ppred_nth_fib_le_ppconts_B)],
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

/- As a simple consequence, we can now derive that all denominators are nonnegative. -/

lemma zero_le_of_continuants_aux_b : 0 ≤ ((gcf.of v).continuants_aux n).b :=
begin
  let g := gcf.of v,
  induction n with n IH,
  case nat.zero: { refl },
  case nat.succ:
  { cases (decidable.em $ g.terminated_at (n - 1)) with terminated not_terminated,
    { cases n,
      { simp[zero_le_one] },
      { have : g.continuants_aux (n + 2) = g.continuants_aux (n + 1), from
          continuants_aux_stable_step_of_terminated terminated,
        simp[this, IH] } },
    { calc
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
  obtain ⟨gp_n, nth_s_eq, ⟨_⟩⟩ : ∃ gp_n, g.s.nth n = some gp_n ∧ gp_n.b = b, from
    exists_s_b_of_part_denom nth_part_denom_eq,
  let conts := g.continuants_aux (n + 2),
  set pconts := g.continuants_aux (n + 1) with pconts_eq,
  set ppconts := g.continuants_aux n with ppconts_eq,
  -- use the recurrence of continuants_aux and the fact that gp_n.a = 1
  suffices : gp_n.b * pconts.b ≤ ppconts.b + gp_n.b * pconts.b, by
  { have : gp_n.a = 1, from of_part_num_eq_one (part_num_eq_s_a nth_s_eq),
    finish [(gcf.continuants_aux_recurrence nth_s_eq ppconts_eq pconts_eq)] },
  have : 0 ≤ ppconts.b, from zero_le_of_continuants_aux_b,
  solve_by_elim [le_add_of_nonneg_of_le, le_refl]
end

/-- Shows that `Bₙ₊₁ ≥ bₙ * Bₙ`, where `bₙ` is the `n`th partial denominator and `Bₙ₊₁` and `Bₙ` are
the `n + 1`th and `n`th denominator of the continued fraction. -/
theorem le_of_succ_nth_denom {b : K}
  (nth_part_denom_eq : (gcf.of v).partial_denominators.nth n = some b) :
  b * (gcf.of v).denominators n ≤ (gcf.of v).denominators (n + 1) :=
begin
  rw [denom_eq_conts_b, nth_cont_eq_succ_nth_cont_aux],
  exact (le_of_succ_succ_nth_continuants_aux_b nth_part_denom_eq)
end

/-- Shows that the sequence of denominators is monotonically increasing, that is `Bₙ ≤ Bₙ₊₁`. -/
theorem of_denom_mono : (gcf.of v).denominators n ≤ (gcf.of v).denominators (n + 1) :=
begin
  let g := gcf.of v,
  cases (decidable.em $ g.partial_denominators.terminated_at n) with terminated not_terminated,
  { have : g.partial_denominators.nth n = none, by rwa seq.terminated_at at terminated,
    have : g.terminated_at n, from
      terminated_at_iff_part_denom_none.elim_right (by rwa seq.terminated_at at terminated),
    have : (gcf.of v).denominators (n + 1) = (gcf.of v).denominators n, from
      denominators_stable_of_terminated n.le_succ this,
    rw this },
  { obtain ⟨b, nth_part_denom_eq⟩ : ∃ b, g.partial_denominators.nth n = some b, from
      option.ne_none_iff_exists'.mp not_terminated,
    have : 1 ≤ b, from of_one_le_nth_part_denom nth_part_denom_eq,
    calc
      (gcf.of v).denominators n ≤ b * (gcf.of v).denominators n   : by simpa using
                                                                      mul_le_mul_of_nonneg_right
                                                                      this zero_le_of_denom
                            ... ≤ (gcf.of v).denominators (n + 1) : le_of_succ_nth_denom
                                                                      nth_part_denom_eq }
end

end generalized_continued_fraction
