import tactic.hint
import tactic.split_ifs
import tactic.finish

example : 1 = 1 :=
begin
  (do hints ← tactic.hint, guard $ "refl" ∈ hints),
  refl
end

-- `split_ifs` is designated as a `hint_tactic` in its own file
example : if 1 = 1 then true else false :=
begin
  (do hints ← tactic.hint, guard $ "split_ifs" ∈ hints),
  split_ifs; trivial
end

-- Check we don't provide any hints on `false`.
example : false ∨ true :=
begin
  success_if_fail { left, hint },
  right, trivial,
end

-- Check that tactics are sorted by the number of goals they leave.
example : 1 = 1 ∧ 2 = 2 :=
begin
  (do hints ← tactic.hint, guard $ hints.indexes_of "finish" < hints.indexes_of "fsplit"),
  finish
end

example (h : false) : false :=
begin
  (do hints ← tactic.hint, guard $ "assumption" ∈ hints),
  assumption
end

example {P Q : Prop} (p : P) (h : P → Q) : Q :=
begin
  (do hints ← tactic.hint, guard $ "solve_by_elim" ∈ hints),
  solve_by_elim,
end
