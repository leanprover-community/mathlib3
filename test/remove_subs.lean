import tactic.remove_subs

example {i l : ℕ} (i1 : 1 ≤ i) (il : i + 1 ≤ l) :
  i - 1 + (l - i - 1 + 1) + 1 = l :=
by remove_subs!

example (n m : ℕ) : nat.pred n - m = nat.pred (n - m) :=
show n - 1 - m = n - m - 1, by remove_subs!

example (n m : ℕ) : nat.pred n - m = nat.pred (n - m) :=
by remove_subs!
