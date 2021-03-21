import tactic.choose

/- choice -/
example (h : ∀n m : ℕ, n < m → ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i : ∀n m : ℕ, n < m → ℕ,
  guard_hyp j : ∀n m : ℕ, n < m → ℕ,
  guard_hyp h : ∀ (n m : ℕ) (h : n < m), m = n + i n m h ∨ m + j n m h = n,
  trivial
end

example (h : ∀n m : ℕ, n < m → ∃i j, m = n + i ∨ m + j = n) : true :=
begin
  choose! i j h using h,
  guard_hyp i : ℕ → ℕ → ℕ,
  guard_hyp j : ℕ → ℕ → ℕ,
  guard_hyp h : ∀ (n m : ℕ), n < m → m = n + i n m ∨ m + j n m = n,
  trivial
end

example (h : ∀n m : ℕ, ∃i, ∀n:ℕ, ∃j, m = n + i ∨ m + j = n) : true :=
begin
  choose i j h using h,
  guard_hyp i : ℕ → ℕ → ℕ,
  guard_hyp j : ℕ → ℕ → ℕ → ℕ,
  guard_hyp h : ∀ (n m k : ℕ), m = k + i n m ∨ m + j n m k = k,
  trivial
end

-- Test `simp only [exists_prop]` gets applied after choosing.
-- Because of this simp, we need a non-rfl goal
example (h : ∀ n, ∃ k ≥ 0, n = k) : ∀ x : ℕ, 1 = 1 :=
begin
  choose u hu using h,
  guard_hyp hu : ∀ n, u n ≥ 0 ∧ n = u n,
  intro, refl
end

-- test choose with conjunction
example (h : ∀ i : ℕ, ∃ j, i < j ∧ j < i+i) : true :=
begin
  choose f h h' using h,
  guard_hyp f : ℕ → ℕ,
  guard_hyp h : ∀ (i : ℕ), i < f i,
  guard_hyp h' : ∀ (i : ℕ), f i < i + i,
  trivial,
end

-- test choose with nonempty instances
universe u
example {α : Type u} (p : α → Prop) (h : ∀ i : α, p i → ∃ j : α × α, p j.1) : true :=
begin
  choose! f h using h,
  guard_hyp f : α → α × α,
  guard_hyp h : ∀ (i : α), p i → p (f i).1,
  trivial,
end
