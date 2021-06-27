import data.nat.basic

example (n : ℕ) (h : n < 2) : n = 0 ∨ n = 1 :=
by dec_trivial!

example (n : ℕ) (h : n < 3) : true :=
begin
  let k : ℕ := n - 1,
  have : ∀ i < k, i = 0 ∨ i = 1,
  by dec_trivial!,
  trivial
end

example (b : bool) (h : b = tt) : true :=
begin
  let b₁ : bool := b,
  have : ∀ b₂ : bool, b₂ ≠ b₁ → b₂ = ff,
  by dec_trivial!,
  trivial
end

example (n : ℕ) : (0 : fin (n+1)) + 0 = 0 :=
begin
  success_if_fail { dec_trivial! },
  dec_trivial
end
