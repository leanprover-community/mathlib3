/-
Copyright (c) 2021 Bhavik Mehta, Thomas Bloom. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bhavik Mehta, Thomas Bloom
-/

import data.real.basic
import analysis.special_functions.log

/-!
# Title

This file should contain a formal proof of https://arxiv.org/pdf/2112.03726.pdf, but for now it
contains associated results useful for that paper.
-/

open_locale big_operators -- this lets me use ∑ and ∏ notation
open real

/-- The statement of Bloom's theorem. -/
theorem bloom :
  ∃ (C : ℝ), 0 < C ∧
    ∀ (N : ℕ), ∀ A ⊆ finset.range (N+1),
      C * log (log (log N)) * log N / log (log N) ≤ ∑ n in A, (1 / n : ℝ) →
        ∃ S ⊆ A, ∑ n in S, (1 / n : ℝ) = 1 :=
sorry
-- * sorry is used as a placeholder for things we haven't filled in yet, a finished formal proof
--   would be "sorry-free"
-- * it's easier to write all inequalities as < or ≤ for essentially technical reasons, and it's
--   not too unreadable
-- * `finset.range (N+1)` is the finite set `{0, 1, ..., N}`. Oddly enough, 1/0 is defined to be 0
--   in Lean, so it's actually safe for me to include `0` in the set (in fact equivalent).
--     * the alternative is to have division only defined when the denominator is non-zero, but
--       that turns out to be more inconvenient; instead we allow division by zero but many
--       lemmas about division insist the denominator is non-zero instead
--     * for instance, to divide by `log (log N)` above I'd need to show that it's non-zero, which
--       is obvious but still requires work. Essentially the tradeoff is that the statement doesn't
--       need these proofs, but the proof will; and it's more important for the statement to be
--       readable
-- * I had to write `(1 / n : ℝ)` rather than just `(1 / n)` because otherwise Lean tries to work
--   with `1 / n` as a natural, which means floor division. So I instead say "treat this as a real
--   number" to make the division act sensibly. I could instead talk about rationals, but for
--   the inequality part I've got a real on the LHS anyway, so it would convert to rationals and
--   then to reals, so might as well go straight to ℝ.
