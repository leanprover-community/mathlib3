import tactic.specialize

example (h : ∀ x > 0, true) : true :=
begin
  specialize' h 1 _,
  { guard_target 1 > 0,
    exact nat.zero_lt_one },
  { guard_target true,
    exact h }
end
