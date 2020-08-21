import data.nat.basic
import tactic.squeeze

-- Test that squeeze_simp succeeds when it closes the goal.
example : 1 = 1 :=
by { squeeze_simp }

-- Test that `squeeze_simp` succeeds when given arguments.
example {a b : ℕ} (h : a + a = b) : b + 0 = 2 * a :=
by { squeeze_simp [←h, two_mul] }
