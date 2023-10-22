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

/--
Since `fin t` denotes the numbers `{0, ..., t - 1}`, we can think of a function `fin t → ℕ`
as being a vector in `ℕ^t`, ie `n = (n₀, n₁, ..., nₜ₋₁)`.
Then `is_ramsey_valid (fin N) n` means that for any labelling `C` of the edges of the complete graph
on `{0, ..., N - 1}`, there is a finite subset `m` of this graph's vertices, and a label `i` such
that `|m| ≥ nᵢ`, and all edges between vertices in `m` are labelled `i`.
In the two-colour case discussed in the blogpost, we would have `t = 2`, and `n = (k, l)`.
In Lean this is denoted by `![k, l]`, as in the examples below.
-/
lemma ramsey_valid_iff {t N : ℕ} (n : fin t → ℕ) :
  is_ramsey_valid (fin N) n =
    ∀ (C : (complete_graph (fin N)).edge_set → fin t),
      ∃ m : finset (fin N), ∃ i : fin t, monochromatic_of C m i ∧ n i ≤ m.card :=
rfl

/--
The ramsey number of the vector `n` is then just the infimum of all `N` such that
`is_ramsey_valid (fin N) n`.
-/
lemma ramsey_number_def {t : ℕ} (n : fin t → ℕ) :
  ramsey_number n = Inf {N | is_ramsey_valid (fin N) n} :=
(nat.find_eq_iff _).2 ⟨Inf_mem (ramsey_fin_exists n), λ m, nat.not_mem_of_lt_Inf⟩

-- We've got a definition of Ramsey numbers, let's first make sure it satisfies some of
-- the obvious properties.
example : ∀ k, ramsey_number ![2, k] = k := by simp
example : ∀ k l, ramsey_number ![k, l] = ramsey_number ![l, k] := ramsey_number_pair_swap

-- It also satisfies the inductive bound by Erdős-Szekeres
lemma ramsey_number_inductive_bound : ∀ k ≥ 2, ∀ l ≥ 2,
    ramsey_number ![k, l] ≤ ramsey_number ![k - 1, l] + ramsey_number ![k, l - 1] :=
λ _ h _, ramsey_number_two_colour_bound_aux h

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
lemma ramsey_number_lower_bound : ∀ k ≥ 2, real.sqrt 2 ^ k ≤ ramsey_number ![k, k] :=
  λ _, diagonal_ramsey_lower_bound_simpler

-- Everything up to this point has been known results, which were needed for the formalisation,
-- served as a useful warm up to the main result, and hopefully demonstrate the correctness
-- of the definition of Ramsey numbers.

-- Finally, the titular statement, giving an exponential improvement to the upper bound on Ramsey
-- numbers.
theorem exponential_ramsey_improvement : ∃ ε > 0, ∀ k, (ramsey_number ![k, k] : ℝ) ≤ (4 - ε) ^ k :=
global_bound

end main_results
