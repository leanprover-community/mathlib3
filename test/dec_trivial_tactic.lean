import data.nat.basic

example (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 :=
by dec_trivial
