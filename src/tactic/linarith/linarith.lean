

import tactic.ring
import tactic.linarith.preprocessing
import tactic.linarith.elimination
import tactic.linarith.parsing
import tactic.linarith.verification
import tactic.cancel_denoms

/-!
# Linear arithmetic

`linarith` is a tactic for discharging linear arithmetic goals using Fourier-Motzkin elimination.

`linarith` is (in principle) complete for ℚ and ℝ. It is not complete for non-dense orders, i.e. ℤ.

- @TODO: investigate storing comparisons in a list instead of a set, for possible efficiency gains
- @TODO: delay proofs of denominator normalization and nat casting until after contradiction is
  found
-/
