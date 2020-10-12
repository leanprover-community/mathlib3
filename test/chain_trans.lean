
import tactic.chain_trans
import tactic.interactive

example {x y z w u v : ℕ} {a b : ℤ} (h₀ : x ≤ y) (h₁ : y < z) (h : y < u) (h₂ : z < w) (h₃ : w = u) (h₄ : u < v) : x ≤ u :=
begin
  chain_trans,
end

example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : x = y) (h₂ : y < z) : true :=
begin
  have : w < w,
  { success_if_fail_with_msg
    { chain_trans }
    "no appropriate chain of inequalities can be found between `w` and `w`",
    admit },
  triv
end

example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : x = y) (h₂ : y < z) : true :=
begin
  have : x < w,
  { success_if_fail_with_msg
    { chain_trans }
    "no appropriate chain of inequalities can be found between `x` and `w`",
    admit },
  triv
end

example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : x = y) (h₂ : y < z) : w < z :=
begin
  chain_trans,
end

example {w x y z : ℕ} {a b : ℤ} (h₀ : w ≤ x) (h₁ : x = y) (h₃ : y ≤ z) (h₂ : y < z) (h₃ : y ≤ z) : w < z :=
begin
  chain_trans,
end
