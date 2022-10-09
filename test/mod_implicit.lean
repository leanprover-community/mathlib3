import tactic.interactive
import data.nat.basic

variables (p : ℕ → Prop) (a b : ℕ)

example (h : p (a + b)) : p (b + a) :=
begin
  rw add_comm,
  -- `guard_target` fails because the instances don't match
  success_if_fail { guard_target p (a + b) },
  guard_target_mod_implicit p (a + b),
  assumption
end

example (h : p (b + a)) : p (a + b) :=
begin
  rw add_comm at h,
  -- `guard_hyp` fails because the instances don't match
  success_if_fail { guard_hyp h : p (a + b) },
  guard_hyp_mod_implicit h : p (a + b),
  assumption
end
