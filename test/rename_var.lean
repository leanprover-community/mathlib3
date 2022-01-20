import tactic.rename_var

example (P : ℕ →  ℕ → Prop) (h : ∀ n, ∃ m, P n m) : true :=
begin
  rename_var n q at h,
  guard_hyp_strict h : ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_var m z at h,
  guard_hyp_strict h : ∀ (q : ℕ), ∃ (z : ℕ), P q z,
  trivial
end

example (P : ℕ →  ℕ → Prop) (h : ∀ n, ∃ m, P n m) : ∀ n, ∃ m, P n m :=
begin
  rename_var n q,
  guard_target_strict ∀ (q : ℕ), ∃ (m : ℕ), P q m,
  rename_var m l,
  guard_target_strict ∀ (q : ℕ), ∃ (l : ℕ), P q l,
  exact h
end

example (h : (λ n : ℕ, n) = id) : true :=
begin
  rename_var n m at h,
  guard_hyp_strict h : (λ (m : ℕ), m) = id,
  trivial
end
