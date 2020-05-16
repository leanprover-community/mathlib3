import tactic.apply_fun
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end

example (f : ℕ → ℕ) (a b : ℕ) (monof : monotone f)  (h : a ≤ b) : f a ≤ f b :=
begin
  apply_fun f at h,
  assumption,
  assumption
end

example (a b : ℤ) (h : a = b) : a + 1 = b + 1 :=
begin
  apply_fun (λ n, n+1) at h,
  -- check that `h` was β-reduced
  guard_hyp' h := a + 1 = b + 1,
  exact h
end

example (f : ℕ → ℕ) (a b : ℕ) (monof : monotone f)  (h : a ≤ b) : f a ≤ f b :=
begin
  apply_fun f at h using monof,
  assumption
end

-- monotonicity will be proved by `mono` in the next example
example (a b : ℕ) (h : a ≤ b) : a + 1 ≤ b + 1 :=
begin
  apply_fun (λ n, n+1) at h,
  exact h
end
