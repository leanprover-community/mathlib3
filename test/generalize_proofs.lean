import tactic.generalize_proofs

example (x : ℕ) (h : x < 2) : classical.some ⟨x, h⟩ < 2 :=
begin
  generalize_proofs a,
  guard_hyp a : ∃ x, x < 2,
  guard_target classical.some a < 2,
  exact classical.some_spec a,
end

example (a : ∃ x, x < 2) : classical.some a < 2 :=
begin
  generalize_proofs,
  guard_target classical.some a < 2,
  exact classical.some_spec a,
end

example (x : ℕ) (h : x < 2) (a : ∃ x, x < 2) : classical.some a < 2 :=
begin
  generalize_proofs,
  guard_target classical.some a < 2,
  exact classical.some_spec a,
end

example (x : ℕ) (h : x < 2) (H : classical.some ⟨x, h⟩ < 2) : classical.some ⟨x, h⟩ < 2 :=
begin
  generalize_proofs a at H ⊢,
  guard_hyp a : ∃ x, x < 2,
  guard_hyp H : classical.some a < 2,
  guard_target classical.some a < 2,
  exact H,
end
