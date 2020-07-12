import tactic.apply_fun
import data.matrix.basic
open function

example (X Y Z : Type) (f : X → Y) (g : Y → Z) (H : injective $ g ∘ f) :
  injective f :=
begin
  intros x x' h,
  apply_fun g at h,
  exact H h
end

example (f : ℕ → ℕ) (a b : ℕ) (monof : monotone f) (h : a ≤ b) : f a ≤ f b :=
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

example (f : ℕ → ℕ) (a b : ℕ) (monof : monotone f) (h : a ≤ b) : f a ≤ f b :=
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

example {n : Type} [fintype n] {X : Type} [semiring X]
  (f : matrix n n X → matrix n n X) (A B : matrix n n X) (h : A * B = 0) : f (A * B) = f 0 :=
begin
  apply_fun f at h,
  -- check that our β-reduction didn't mess things up:
  -- (previously `apply_fun` was producing `f (A.mul B) = f 0`)
  guard_hyp' h := f (A * B) = f 0,
  exact h,
end
