import tactic.simp_command
import analysis.complex.exponential

/-!
Tests for the #simp command.
-/

#simp 5 - 5

section arith

def f (x : ℤ) := x + (x - x)
#simp [f] f 3

mk_simp_attribute test ""
attribute [test] f
-- You can use the optional `:` to separate
-- the simp lemmas and attributes from the expression to simplify.
#simp with test : (f 3)

attribute [simp] f
#simp f 3
#simp only [f] f 3

local attribute [simp] sub_self

variables (x : ℤ)

#simp with test : (f x)
#simp f x
#simp only [f] f x
#simp only [f, sub_self] f x

end arith

section complex

open real
#simp [exp_ne_zero] : λ x, deriv (λ x, (sin x) / (exp x)) x

variables (x : ℝ)

-- You can refer to local variables, rather than having to use lambdas.
open real
#simp [exp_ne_zero] : deriv (λ x, (sin x) / (exp x)) x

end complex
