import tactic

example {x y : ℕ}
: x = 1 → false :=
begin
  intros a,
  wlog h : x = y,
  { guard_target x = y ∨ y = x,
    admit },
  { guard_hyp h := x = y,
    guard_hyp a := x = 1,
    admit },
end

example {x y : ℕ}
: false :=
begin
  wlog h : x ≤ y,
  { guard_hyp h := x ≤ y,
    guard_target false,
    admit },
end

example {x y z : ℕ}
: false :=
begin
  wlog h : x ≤ y + z,
  { guard_target x ≤ y + z ∨ x ≤ z + y,
    admit },
  { guard_hyp h := x ≤ y + z,
    guard_target false,
    admit },
end

example {x y z : ℕ}
: false :=
begin
  wlog : x ≤ y + z using x y,
  { guard_target x ≤ y + z ∨ y ≤ x + z,
    admit },
  { guard_hyp a := x ≤ y + z,
    guard_target false,
    admit },
end
