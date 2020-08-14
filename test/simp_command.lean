import tactic.simp_command
import analysis.special_functions.trigonometric

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



section real

open real
#simp [exp_ne_zero] : λ x, deriv (λ x, (sin x) / (exp x)) x

variables (x : ℝ)

-- You can refer to local variables, rather than having to use lambdas.
open real
#simp [exp_ne_zero] : deriv (λ x, (sin x) / (exp x)) x

end real



section func_hyp

variables (f : ℕ → ℕ) (hf : f 3 = 0) (hg : 9 = 55)

#simp only [hg] : 9
#simp only [hf, add_zero] : 1 + f 3

end func_hyp



namespace inst

class magic_data (n : ℕ) :=
(dummy : ℕ)

axiom spell (t : ℤ) (k : ℕ) [magic_data k] : (k = 3) ↔ (k = 77)

variables (t : ℤ) (k : ℕ) [magic_data k] [ii : magic_data k] (h : k = 77 ↔ k = 8)

-- We want to be able to emulate this:
example : (t = t) ∧ (h = h) ∧ ((k = 3) ↔ (k = 8)) :=
begin
  simp [spell t, h]
end

-- Check that we can:

#simp [spell t, h, ii] : (k = 3) ↔ (k = 8)
#simp [spell t, h] : (k = 3) ↔ (k = 8)

theorem spell' (k : ℕ) [magic_data k] : (k = 3) ↔ (k = 77) := spell 1 k

attribute [simp] spell'

#simp [h, ii] : (k = 3) ↔ (k = 8)
#simp [h] : (k = 3) ↔ (k = 8)

-- Check that the `#simp` resolver can handle depth > 2 recursive inclusions

class doubly_magic_data (n : ℕ) [magic_data n] :=
(dummy : ℕ)

variables (n : ℕ) [magic_data n] [doubly_magic_data n] (h₂ : n = 77 ↔ n = 8)

@[simp] axiom spell2 (n : ℕ) [magic_data n] [doubly_magic_data n] : (n = 4) ↔ (n = 77)

example : (h₂ = h₂) ∧ ((n = 4) ↔ (n = 8)) :=
begin
  simp [h₂],
end

#simp [h₂, ii] : (n = 4) ↔ (n = 8)
#simp [h₂] : (n = 4) ↔ (n = 8)


end inst
