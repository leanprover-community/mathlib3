import probability.stopping

open_locale nnreal

lemma nat.exists_of_le_supr {p : ℕ → Prop} (hp : set.finite (p ⁻¹' {true}))
  {f : ℕ → ℝ} {ε : ℝ≥0} (hn : 0 < ε) (h : ↑ε ≤ ⨆ k (h : p k), f k) :
  ∃ m, p m ∧ ↑ε ≤ f m :=
begin
  sorry,
end
