import tactic.replacer

open tactic

def_replacer sneaky

example : true :=
begin
  success_if_fail { sneaky },
  trivial
end

@[sneaky] meta def sneaky' : tactic unit := `[skip]

example : true :=
begin
  sneaky,
  guard_target true,
  trivial
end

@[sneaky] meta def sneaky'' := `[trivial]

example : true :=
begin
  sneaky
end

@[sneaky] meta def sneaky''' (old : tactic unit) := old >> `[trivial]

example : true ∧ true :=
begin
  split,
  sneaky
end

def_replacer transform : ℕ → tactic ℕ

run_cmd success_if_fail (transform 1)

@[transform] meta def transform' (n : ℕ) : tactic ℕ :=
return (n+1)

run_cmd do n ← transform 2, guard (n = 3)

@[transform] meta def transform'' (n : ℕ) : tactic ℕ :=
return (n * n)

run_cmd do n ← transform 2, guard (n = 4)

@[transform] meta def transform''' (n : ℕ) (old : tactic ℕ) : tactic ℕ :=
do n' ← old, return (n' * n')

run_cmd do n ← transform 2, guard (n = 16)
