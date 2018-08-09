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