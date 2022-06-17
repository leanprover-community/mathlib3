import tactic.push_neg
import data.int.basic

example (h : ∃ p: ℕ, ¬ ∀ n : ℕ, n > p) (h' : ∃ p: ℕ, ¬ ∃ n : ℕ, n < p) : ¬ ∀ n : ℕ, n = 0 :=
begin
  push_neg at *,
  guard_target_strict ∃ (n : ℕ), n ≠ 0,
  guard_hyp_strict h : ∃ (p n : ℕ), n ≤ p,
  guard_hyp_strict h' : ∃ (p : ℕ), ∀ (n : ℕ), p ≤ n,
  use 1,
end

-- In the next example, ℤ should be ℝ in maths, but I don't want to import real numbers
-- for testing only

example (a : ℕ → ℤ) (l : ℤ) (h : ¬ ∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε) : true :=
begin
  push_neg at h,
  guard_hyp_strict h : ∃ (ε : ℤ), ε > 0 ∧ ∀ (N : ℕ), ∃ (n : ℕ), n ≥ N ∧ ε ≤ |a n - l|,
  trivial
end

example (f : ℤ → ℤ) (x₀ y₀) (h : ¬ ∀ ε > 0, ∃ δ > 0, ∀ x, |x - x₀| ≤ δ → |f x - y₀| ≤ ε) : true :=
begin
  push_neg at h,
  guard_hyp_strict h : ∃ (ε : ℤ), ε > 0 ∧ ∀ δ > 0, (∃ (x : ℤ), |x - x₀| ≤ δ ∧ ε < |f x - y₀| ),
  trivial
end

example (n) : n*n ≠ 1 → n ≠ 1 :=
begin
  contrapose,
  rw [not_not, not_not],
  intro h,
  rw [h, one_mul]
end

example (n) : n*n ≠ 1 → n ≠ 1 :=
begin
  contrapose!,
  intro h,
  rw [h, one_mul]
end

example (n) (h : n*n ≠ 1) : n ≠ 1 :=
begin
  contrapose h,
  rw not_not at *,
  rw [h, one_mul]
end

example (n) (h : n*n ≠ 1) : n ≠ 1 :=
begin
  contrapose! h,
  rw [h, one_mul]
end

example (n) (h : n*n ≠ 1) : n ≠ 1 :=
begin
  contrapose! h with newh,
  rw [newh, one_mul]
end

example : 0 = 0 :=
begin
  success_if_fail_with_msg { contrapose }
    "The goal is not an implication, and you didn't specify an assumption",
  refl
end

-- Remember that ∀ is the same as Π which is a generalization of → so we need to make sure
-- `contrapose` fails with a helpful error message in the next example.
example : ∀ x : ℕ, x = x :=
begin
  success_if_fail_with_msg { contrapose }
    "contrapose only applies to nondependent arrows between props",
  intro, refl
end

open tactic
example (X : Type) (f : X → ℕ) (h : ¬∀ x, f x = 0) (hf : false) : false :=
begin
  have h1 := h,
  -- h h1: ¬∀ (x : X), f x = 0
  push_neg at h,
  push_neg at h1,
  (do ht ← get_local `h >>= infer_type,
      h1t ← get_local `h1 >>= infer_type,
      guard (ht = h1t) ),
  exact hf
end
