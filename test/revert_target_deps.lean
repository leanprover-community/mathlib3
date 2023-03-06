import tactic.interactive

example (b : bool) (h : b = tt) : true :=
begin
  let b₁ : bool := b,
  /-
  This test shows that `tactic.revert_target_deps`
  will revert `b₁` because it occurse in the `have` statement below,
  but recursively also reverts `b` (and hence `h`),
  because `b` occurs in the body of the `let` statement that introduces `b₁`,
  even though `b` doesn't occur directly in the `have` statement below.
  -/
  have : ∀ b₂ : bool, b₂ ≠ b₁ → b₂ = ff,
  { revert_target_deps,
    tactic.interactive.guard_target
      ``(∀ (b : bool), b = tt → (let b₁ : bool := b in ∀ (b₂ : bool), b₂ ≠ b₁ → b₂ = ff)),
    exact dec_trivial },
  trivial
end
