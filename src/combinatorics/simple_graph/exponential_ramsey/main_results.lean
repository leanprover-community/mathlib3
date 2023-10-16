/-
Copyright (c) 2023 Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta
-/
import combinatorics.simple_graph.exponential_ramsey.section12

/-!
# Summary of main results

In this file we demonstrate the main result of this formalisation, using the proofs which are
given fully in other files. The purpose of this file is to show the form in which the definitions
and theorem look.
-/

namespace main_results

open simple_graph
open simple_graph.top_edge_labelling

-- This lemma characterises our definition of Ramsey numbers.
-- Since `fin k` denotes the numbers `{0, ..., k - 1}`, we can think of a function `fin k → ℕ`
-- as being a vector in `ℕ^k`, ie `n = (n₀, n₁, ..., nₖ₋₁)`. Then our definition of `R(n)` satisfies
-- `R(n) ≤ N` if and only if, for any labelling `C` of the edges of the complete graph on
-- `{0, ..., N - 1}`, there is a finite subset `m` of this graph's vertices, and a label `i` such
-- that `|m| ≥ nᵢ`, and all edges of `m` are labelled `i`.
lemma ramsey_number_le_iff {k N : ℕ} (n : fin k → ℕ) :
  ramsey_number n ≤ N ↔
    ∀ (C : (complete_graph (fin N)).edge_set → fin k),
      ∃ m : finset (fin N), ∃ i : fin k, monochromatic_of C m i ∧ n i ≤ m.card :=
ramsey_number_le_iff_fin

-- We've got a definition of Ramsey numbers, let's first make sure it satisfies some of
-- the obvious properties.
example : ∀ k, ramsey_number ![2, k] = k := by simp
example : ∀ k l, ramsey_number ![k, l] = ramsey_number ![l, k] := ramsey_number_pair_swap

-- It also satisfies the inductive bound by Erdős-Szekeres
lemma ramsey_number_inductive_bound : ∀ k l, k ≥ 2 → l ≥ 2 →
    ramsey_number ![k, l] ≤ ramsey_number ![k - 1, l] + ramsey_number ![k, l - 1] :=
λ _ _, ramsey_number_two_colour_bound_aux

-- And we can use this bound to get the standard upper bound in terms of the binomial coefficient,
-- which is written `n.choose k` in Lean.
lemma ramsey_number_binomial_bound :
  ∀ k l, ramsey_number ![k, l] ≤ (k + l - 2).choose (k - 1) :=
ramsey_number_le_choose

lemma ramsey_number_power_bound : ∀ k, ramsey_number ![k, k] ≤ 4 ^ k :=
λ _, diagonal_ramsey_le_four_pow

-- We can also verify some small values:
example : ramsey_number ![3, 3] = 6 := ramsey_number_three_three
example : ramsey_number ![3, 4] = 9 := ramsey_number_three_four
example : ramsey_number ![4, 4] = 18 := ramsey_number_four_four
-- The `![]` notation means the input to the `ramsey_number` function is a vector, and indeed gives
-- values for more than two colours too
example : ramsey_number ![3, 3, 3] = 17 := ramsey_number_three_three_three

-- We also have Erdős' lower bound on Ramsey numbers
lemma ramsey_number_lower_bound : ∀ k, 2 ≤ k → real.sqrt 2 ^ k ≤ ramsey_number ![k, k] :=
  λ _, diagonal_ramsey_lower_bound_simpler

-- Everything up to this point has been known results, which were needed for the formalisation,
-- served as a useful warm up to the main result, and hopefully demonstrate the correctness
-- of the definition of Ramsey numbers.

-- Finally, the titutar statement, giving an exponential improvement to the upper bound on Ramsey
-- numbers.
theorem exponential_ramsey_improvement : ∃ ε > 0, ∀ k, (ramsey_number ![k, k] : ℝ) ≤ (4 - ε) ^ k :=
global_bound

end main_results
