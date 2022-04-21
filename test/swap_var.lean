import tactic.swap_var

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
begin
  split,
  work_on_goal 2 { swap_var P Q },
  all_goals { exact ‹P› }
end

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
begin
  split,
  work_on_goal 2 { swap_var [P Q] },
  all_goals { exact ‹P› }
end

example (P Q : Prop) (hp : P) (hq : Q) : P ∧ Q :=
begin
  split,
  work_on_goal 2 { swap_var P ↔ Q },
  all_goals { exact ‹P› }
end

example (P Q R S : Prop) (hp : P) (hq : Q) (hr : R) (hs : S) : (P ∧ R) ∧ (Q ∧ S) :=
begin
  split,
  work_on_goal 2 { swap_var [P Q, R S] },
  all_goals { exact ⟨‹P›, ‹R›⟩ }
end
