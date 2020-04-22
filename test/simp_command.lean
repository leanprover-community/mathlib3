import tactic.simp_command
import analysis.complex.exponential

/-!
Tests for the #simp command.
-/

#simp 5 - 5

def f (x : ℕ) := x + x - x
#simp [f] f 3

mk_simp_attribute test ""
attribute [test] f
-- You can use the optional `:` to separate
-- the simp lemmas and attributes from the expression to simplify.
#simp with test : (f 3)

attribute [simp] f
#simp f 3
#simp only [f] f 3

-- It would be really nice to be able to refer to local variables,
-- rather than having to use lambdas.
open real
#simp [exp_ne_zero] : λ x, deriv (λ x, (sin x) / (exp x)) x
