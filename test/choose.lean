import tactic.interactive

/- choice -/
example (h : ∀n m : ℕ, ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i := ℕ → ℕ → ℕ,
  guard_hyp j := ℕ → ℕ → ℕ,
  guard_hyp h := ∀ (n m : ℕ), m = n + i n m ∨ m + j n m = n,
  trivial
end

example (h : ∀n m : ℕ, ∃i, ∀n:ℕ, ∃j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i := ℕ → ℕ → ℕ,
  guard_hyp j := ℕ → ℕ → ℕ → ℕ,
  guard_hyp h := ∀ (n m k : ℕ), m = k + i n m ∨ m + j n m k = k,
  trivial
end

-- Test `simp only [exists_prop]` gets applied after choosing.
-- Because of this simp, we need a non-rfl goal
example (h : ∀ n, ∃ k ≥ 0, n = k) : ∀ x : ℕ, 1 = 1 :=
begin
  choose u hu using h,
  guard_hyp hu := ∀ n, u n ≥ 0 ∧ n = u n,
  intro, refl
end
