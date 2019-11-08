import tactic.back.interactive

-- set_option trace.back true

axiom ax {n k : ℕ} : n = k

@[back] axiom ax2 {m : ℤ} : m = -1

example {n : ℕ} (h : n = 1) : n = 1 :=
begin
  back,
end

example {n : ℤ} (h : n = 1) (h' : n = 3) : n = -1 :=
begin
  back,
end

example {n : ℕ} (h : n = 1) : n = 2 :=
begin
  back [ax],
end

example {n : ℕ} (h : n = 1) : n = 2 ∧ n = 1 :=
begin
  split,
  back [ax]
end

example {n : ℕ} (h : n = 1000 + 200) : n = 1 + 199 + 1000 ∧ 1000 + 200 = 1 + 199 + 1000 :=
begin
  split,
  back
end

example {n k : ℕ} (h₁ : n = 1) (h₂ : k = 2) : n = 1 ∧ k = 2 :=
begin
  split,
  back,
end
