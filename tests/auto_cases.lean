import data.real.basic
import tactic.auto_cases

example (x : ℝ) (h : x > 0) : true :=
begin
  success_if_fail { auto_cases },
  guard_hyp x := ℝ,
  trivial
end