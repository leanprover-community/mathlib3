import tactic.core

open tactic lean.parser interactive.types

run_parser do
  e ← with_input texpr "λ x:ℕ, x",
  e ← to_expr e.1,
  guard (e =ₐ `(λ x:ℕ, x)),
  emit_code_here "def foo := 1"

example : foo = 1 := rfl

-- check that `emit_code_here` terminates properly
run_parser emit_code_here "\n"
