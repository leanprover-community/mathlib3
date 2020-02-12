import tactic.hint
import tactic.split_ifs

example : 1 = 1 :=
begin
  (do hints ← tactic.hint, guard $ "refl" ∈ hints),
  refl
end

-- `split_ifs` receives its @[hint] attribute in its own file
example : if 1 = 1 then true else false :=
begin
  (do hints ← tactic.hint, guard $ "split_ifs" ∈ hints),
  split_ifs; trivial
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
