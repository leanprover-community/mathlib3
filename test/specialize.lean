import tactic.specialize

example (h : ∀ x > 0, true) : true :=
begin
  specialize' h 1 _,
  { guard_target 1 > 0,
    exact nat.zero_lt_one },
  { guard_hyp h : true,
    exact h }
end

example (h : ∀ x > 0, ∀ y > 0, true) : true :=
begin
  specialize' h 1 _,
  { guard_target 1 > 0,
    exact nat.zero_lt_one },
  { guard_hyp h : ∀ y > 0, true,
    exact h _ nat.zero_lt_one }
end

example (h : ∀ x > 0, ∀ y > 0, true) : true :=
begin
  specialize' h 1 _ 2 _,
  { guard_target 1 > 0,
    exact nat.zero_lt_one },
  { guard_target 2 > 0,
    exact nat.zero_lt_succ 1 },
  { guard_hyp h : true,
    exact h }
end

example (h : ∀ x > 0, ∀ y > 0, true) : true :=
begin
  suffices : ∀ x > 0, true,
  specialize' h 1 _ 2 _,
  { guard_target 1 > 0,
    exact nat.zero_lt_one },
  { guard_target 2 > 0,
    exact nat.zero_lt_succ 1 },
  { guard_hyp h : true,
    exact h },
  { guard_target ∀ x > 0, true,
    intros x hx,
    exact h x hx x hx }
end
