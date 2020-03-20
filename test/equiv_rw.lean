import tactic.equiv_rw

-- Rewriting a hypothesis along an equivalence.
example {α β : Type} (e : α ≃ β) (f : α → ℕ) (h : ∀ b : β, f (e.symm b) = 0) (i : α) : f i = 0 :=
begin
  equiv_rw e at i,
  apply h,
end

-- Check that dependent hypotheses are reverted and reintroduced.
example {α β : Type} (e : α ≃ β) (Z : α → Type) (f : Π a, Z a → ℕ)
  (h : ∀ (b : β) (x : Z (e.symm b)), f (e.symm b) x = 0)
  (i : α) (x : Z i) : f i x = 0 :=
begin
  equiv_rw e at i,
  guard_hyp x := Z ((e.symm) i),
  exact h i x,
end

-- Rewriting the goal along an equivalence.
example {α β : Type} (e : α ≃ β) (b : β) : α :=
begin
  equiv_rw e,
  exact b,
end

-- PROJECT
-- Much more ambitiously, we could analyse whether types have been constructed functorially,
-- and perform eq_rw under functors.
-- PROJECT
-- Of course this applies in arbitrary categories, not just `Type`.
example : is_lawful_functor option := by apply_instance

example {α β : Type} (e : α ≃ β) (b : β) : option α :=
begin
  -- equiv_rw e, -- fails, but could be made to work!
  apply option.some,
  equiv_rw e,
  exact b,
end
