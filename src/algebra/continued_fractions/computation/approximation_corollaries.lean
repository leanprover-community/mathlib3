/-
Copyright (c) 2021 Kevin Kappelmann. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kevin Kappelmann
-/
import algebra.continued_fractions.computation.approximations
import algebra.continued_fractions.convergents_equiv
import topology.algebra.ordered.basic
/-!
# Corollaries From Approximation Lemmas (`algebra.continued_fractions.computation.approximations`)

## Summary

We show that the generalized_continued_fraction given by `generalized_continued_fraction.of` in fact
is a (regular) continued fraction. Using the equivalence of the convergents computations
(`generalized_continued_fraction.convergents` and `generalized_continued_fraction.convergents'`) for
continued fractions (see `algebra.continued_fractions.convergents_equiv`), it follows that the
convergents computations for `generalized_continued_fraction.of` are equivalent.

Moreover, we show the convergence of the continued fractions computations, that is
`(generalized_continued_fraction.of v).convergents` indeed computes `v` in the limit.

## Main Definitions

- `continued_fraction.of` returns the (regular) continued fraction of a value.

## Main Theorems

- `generalized_continued_fraction.of_convergents_eq_convergents'` shows that the convergents
  computations for `generalized_continued_fraction.of` are equivalent.
- `generalized_continued_fraction.of_convergence` shows that
  `(generalized_continued_fraction.of v).convergents` converges to `v`.

## Tags

convergence, fractions
-/

variables {K : Type*} (v : K) [linear_ordered_field K] [floor_ring K]
open generalized_continued_fraction as gcf

lemma generalized_continued_fraction.of_is_simple_continued_fraction :
  (gcf.of v).is_simple_continued_fraction :=
(λ _ _ nth_part_num_eq, gcf.of_part_num_eq_one nth_part_num_eq)

/-- Creates the simple continued fraction of a value. -/
def simple_continued_fraction.of : simple_continued_fraction K :=
⟨gcf.of v, generalized_continued_fraction.of_is_simple_continued_fraction v⟩

lemma simple_continued_fraction.of_is_continued_fraction :
  (simple_continued_fraction.of v).is_continued_fraction :=
(λ _ denom nth_part_denom_eq,
  lt_of_lt_of_le zero_lt_one(gcf.of_one_le_nth_part_denom nth_part_denom_eq))

/-- Creates the continued fraction of a value. -/
def continued_fraction.of : continued_fraction K :=
⟨simple_continued_fraction.of v, simple_continued_fraction.of_is_continued_fraction v⟩

namespace generalized_continued_fraction

open continued_fraction as cf

lemma of_convergents_eq_convergents' : (gcf.of v).convergents = (gcf.of v).convergents' :=
@cf.convergents_eq_convergents'  _ _ (continued_fraction.of v)

section convergence
/-!
### Convergence

We next show that `(generalized_continued_fraction.of v).convergents v` converges to `v`.
-/

variable [archimedean K]
local notation `|` x `|` := abs x
open nat

theorem of_convergence_epsilon :
  ∀ (ε > (0 : K)), ∃ (N : ℕ), ∀ (n ≥ N), |v - (gcf.of v).convergents n| < ε :=
begin
  assume ε ε_pos,
  -- use the archimedean property to obtian a suitable N
  rcases (exists_nat_gt (1 / ε) : ∃ (N' : ℕ), 1 / ε < N') with ⟨N', one_div_ε_lt_N'⟩,
  let N := max N' 5, -- set minimum to 5 to have N ≤ fib N work
  existsi N,
  assume n n_ge_N,
  let g := gcf.of v,
  cases decidable.em (g.terminated_at n) with terminated_at_n not_terminated_at_n,
  { have : v = g.convergents n, from of_correctness_of_terminated_at terminated_at_n,
    have : v - g.convergents n = 0, from sub_eq_zero.elim_right this,
    rw [this],
    exact_mod_cast ε_pos },
  { let B := g.denominators n,
    let nB := g.denominators (n + 1),
    have abs_v_sub_conv_le : |v - g.convergents n| ≤ 1 / (B * nB), from
      abs_sub_convergents_le not_terminated_at_n,
    suffices : 1 / (B * nB) < ε, from lt_of_le_of_lt abs_v_sub_conv_le this,
    -- show that `0 < (B * nB)` and then multiply by `B * nB` to get rid of the division
    have nB_ineq : (fib (n + 2) : K) ≤ nB, by
    { have : ¬g.terminated_at (n + 1 - 1), from not_terminated_at_n,
      exact (succ_nth_fib_le_of_nth_denom (or.inr this)) },
    have B_ineq : (fib (n + 1) : K) ≤ B, by
    { have : ¬g.terminated_at (n - 1), from mt (terminated_stable n.pred_le) not_terminated_at_n,
      exact (succ_nth_fib_le_of_nth_denom (or.inr this)) },
    have zero_lt_B : 0 < B, by
    { have : (0 : K) < fib (n + 1), by exact_mod_cast fib_pos n.zero_lt_succ,
      exact (lt_of_lt_of_le this B_ineq) },
    have zero_lt_mul_conts : 0 < B * nB, by
    { have : 0 < nB, by
      { have : (0 : K) < fib (n + 2), by exact_mod_cast fib_pos (n + 1).zero_lt_succ,
        exact (lt_of_lt_of_le this nB_ineq) },
      solve_by_elim [mul_pos] },
    suffices : 1 < ε * (B * nB), from (div_lt_iff zero_lt_mul_conts).elim_right this,
    -- use that `N ≥ n` was obtained from the archimedean property to show the following
    have one_lt_ε_mul_N : 1 < ε * n, by
    { have one_lt_ε_mul_N' : 1 < ε * (N' : K), from (div_lt_iff' ε_pos).elim_left one_div_ε_lt_N',
      have : (N' : K) ≤ N, by exact_mod_cast (le_max_left  _ _),
      have : ε * N' ≤ ε * n, from
        (mul_le_mul_left ε_pos).elim_right (le_trans this (by exact_mod_cast n_ge_N)),
      exact (lt_of_lt_of_le one_lt_ε_mul_N' this) },
    suffices : ε * n ≤ ε * (B * nB), from lt_of_lt_of_le one_lt_ε_mul_N this,
    -- cancel `ε`
    suffices : (n : K) ≤ B * nB, from (mul_le_mul_left ε_pos).elim_right this,
    show (n : K) ≤ B * nB,
      calc (n : K)
          ≤ fib n                     : by exact_mod_cast (le_fib_self $ le_trans
                                           (le_max_right N' 5) n_ge_N)
      ... ≤ fib (n + 1)               : by exact_mod_cast fib_le_fib_succ
      ... ≤ fib (n + 1) * fib (n + 1) : by exact_mod_cast ((fib (n + 1)).le_mul_self)
      ... ≤ fib (n + 1) * fib (n + 2) : mul_le_mul_of_nonneg_left
                                          (by exact_mod_cast fib_le_fib_succ)
                                          (by exact_mod_cast (fib (n + 1)).zero_le)
      ... ≤ B * nB                    : mul_le_mul B_ineq nB_ineq
                                          (by exact_mod_cast (fib (n + 2)).zero_le)
                                          (le_of_lt zero_lt_B) }
end

local attribute [instance] preorder.topology

theorem of_convergence [order_topology K] :
  filter.tendsto ((gcf.of v).convergents) filter.at_top $ nhds v :=
by simpa [linear_ordered_add_comm_group.tendsto_nhds, abs_sub_comm] using (of_convergence_epsilon v)

end convergence

end generalized_continued_fraction
