
import tactic.apply
import topology.instances.real
       -- algebra.pi_instances

example : ∀ n m : ℕ, n + m = m + n :=
begin
  apply' nat.rec,
  -- refine nat.rec _ _,
  { intro m, ring },
  { intros n h m,
    ring, },
end

instance : partial_order unit :=
{ le := λ _ _, ∀ (x : ℕ), x = x,
  lt := λ _ _, false,
  le_refl := λ _ _, rfl,
  le_trans := λ _ _ _ _ _ _, rfl,
  lt_iff_le_not_le := λ _ _, by simp,
  le_antisymm := λ ⟨⟩ ⟨⟩ _ _, rfl }

example : unit.star ≤ unit.star :=
begin
  have u : unit := unit.star,
  apply' le_trans,
  -- refine le_trans _ _,
  -- exact unit.star,
  do { gs ← tactic.get_goals, guard (gs.length = 3) },
  change () ≤ u,
  all_goals { cases u, refl', } ,
  -- refine le_refl _, refine le_refl _,
end

example {α β : Type*} [partial_order β] (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  transitivity',
  do { gs ← tactic.get_goals, guard (gs.length = 2) },
  exact h₀, exact h₁,
end
example : continuous (λ (x : ℝ), x + x) :=
begin
  apply' continuous.add,
  guard_target' continuous (λ (x : ℝ), x), apply @continuous_id ℝ _,
  guard_target' continuous (λ (x : ℝ), x), apply @continuous_id ℝ _,
  -- guard_target' has_continuous_add ℝ, admit,
end

example (y : ℝ) : continuous (λ (x : ℝ), x + y) :=
begin
  apply' continuous.add,
  guard_target' continuous (λ (x : ℝ), x), apply @continuous_id ℝ _,
  guard_target' continuous (λ (x : ℝ), y), apply @continuous_const ℝ _ _,
  -- guard_target' has_continuous_add ℝ, admit,
end
