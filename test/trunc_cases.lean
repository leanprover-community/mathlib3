import tactic.trunc_cases
import data.quot

example (t : trunc ℕ) : punit :=
begin
  trunc_cases t,
  exact (),
  -- no more goals, because `trunc_cases` used the correct recursor
end

example (t : trunc ℕ) : ℕ :=
begin
  trunc_cases t,
  guard_hyp t := ℕ, -- verify that the new hypothesis is still called `t`.
  exact 0,
  simp,
end

example {α : Type} (I : trunc (has_zero α)) (f : false) : α :=
begin
  trunc_cases I,
  exact 0, -- verify that the typeclass is immediately available
  exfalso, exact f,
end

example {α : Type} [subsingleton α] (I : trunc (has_zero α)) (f : false) : α :=
begin
  trunc_cases I,
  exact 0,
end
