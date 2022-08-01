import tactic.simp_command
import analysis.special_functions.trigonometric.deriv

/- Turn off trace messages only if the statements are simplified to true: -/
set_option trace.silence_simp_if_true true

/-!
Tests for the #simv command.
-/

#simv 5 - 5 = 0

section arith

def f (x : ℤ) := x + (x - x)
#simv [f] f 3 = 3

mk_simp_attribute test ""
attribute [test] f
-- You can use the optional `:` to separate
-- the simv lemmas and attributes from the expression to simplify.
#simv with test : (f 3) = 3

attribute [simp] f
#simv f 3 = 3
#simv only [f, eq_self_iff_true] f 3 = 3 + (3 - 3)

local attribute [simp] sub_self

variables (x : ℤ)

#simv with test : (f x) = x
#simv f x = x
#simv only [f, eq_self_iff_true] f x = x + (x - x)
#simv only [f, sub_self, eq_self_iff_true] f x = x + 0

end arith



section real

open real
#simv [exp_ne_zero] : (λ x, deriv (λ x, (sin x) / (exp x)) x) =
  (λ (x : ℝ), (cos x * exp x - sin x * exp x) / exp x ^ 2)

variables (x : ℝ)

-- You can refer to local variables, rather than having to use lambdas.
open real
#simv [exp_ne_zero] : deriv (λ x, (sin x) / (exp x)) x = (cos x * exp x - sin x * exp x) / exp x ^ 2

end real



section func_hyp

variables (f : ℕ → ℕ) (hf : f 3 = 0) (hg : 9 = 55)

#simv only [hg, eq_self_iff_true] : 9 = 55
#simv only [hf, add_zero, eq_self_iff_true] : 1 + f 3 = 1

end func_hyp



namespace inst

class magic_data (n : ℕ) :=
(dummy : ℕ)

axiom spell (t : ℤ) (k : ℕ) [magic_data k] : (k = 3) ↔ (k = 77)

variables (t : ℤ) (k : ℕ) [magic_data k] [ii : magic_data k] (h : k = 77 ↔ k = 8)

-- We want to be able to emulate this:
example : (t = t) ∧ (h = h) ∧ ((k = 3) ↔ (k = 8)) :=
begin
  simv [spell t, h]
end

-- Check that we can:

#simv [spell t, h, ii] : (k = 3) ↔ (k = 8)
#simv [spell t, h] : (k = 3) ↔ (k = 8)

theorem spell' (k : ℕ) [magic_data k] : (k = 3) ↔ (k = 77) := spell 1 k

attribute [simp] spell'

#simv [h, ii] : (k = 3) ↔ (k = 8)
#simv [h] : (k = 3) ↔ (k = 8)

-- Check that the `#simv` resolver can handle depth > 2 recursive inclusions

class doubly_magic_data (n : ℕ) [magic_data n] :=
(dummy : ℕ)

variables (n : ℕ) [magic_data n] [doubly_magic_data n] (h₂ : n = 77 ↔ n = 8)

@[simp] axiom spell2 (n : ℕ) [magic_data n] [doubly_magic_data n] : (n = 4) ↔ (n = 77)

example : (h₂ = h₂) ∧ ((n = 4) ↔ (n = 8)) :=
begin
  simv [h₂],
end

#simv [h₂, ii] : (n = 4) ↔ (n = 8)
#simv [h₂] : (n = 4) ↔ (n = 8)


end inst
