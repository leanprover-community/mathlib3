import data.real.basic
import tactic.tidy

lemma foo {x : ℝ} : 0 ≤ x :=
begin
-- auto_cases,
-- work_on_goal 0 { cases x, dsimp at * },
-- work_on_goal 1 { refl },
--   tidy {trace_result := tt},
  sorry
end