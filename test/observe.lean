import tactic.observe

example (a b c : ℕ) : a * (b * c) = (b * a) * c :=
begin
  observe : a * b = b * a,
  rw [← this, nat.mul_assoc],
end
