import tactic.hint

example : 1 = 1 :=
begin
  (do hints ← tactic.hint, guard $ "refl" ∈ hints),
  refl
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
