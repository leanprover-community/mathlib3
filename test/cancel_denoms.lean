import tactic.cancel_denoms
import tactic.ring

variables {α : Type} [linear_ordered_field α] (a b c d : α)

example (h : a / 5 + b / 4 < c) : 4*a + 5*b < 20*c :=
begin
  cancel_denoms at h,
  exact h
end

example (h : a > 0) : a / 5 > 0 :=
begin
  cancel_denoms,
  exact h
end

example (h : a + b = c) : a/5 + d*(b/4) = c - 4*a/5 + b*2*d/8 - b :=
begin
  cancel_denoms,
  rw ← h,
  ring,
end
