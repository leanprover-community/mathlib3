
import tactic.apply
import topology.instances.real
       -- algebra.pi_instances

example : ∀ n m : ℕ, n + m = m + n :=
begin
  apply' nat.rec,
  -- refine nat.rec _ _,
  { intros n h m,
    ring, },
  { intro m, ring }
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
  apply' le_trans,
  -- refine le_trans _ _,
  -- exact unit.star,
  refl', refl'
  -- refine le_refl _, refine le_refl _,
end

example {α β : Type*} [partial_order β] (x y z : α → β) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
begin
  transitivity'; assumption
end
example : continuous (λ (x : ℝ), x + x) :=
begin
  apply' continuous.add,
  guard_target' continuous (λ (x : ℝ), x), apply @continuous_id ℝ _,
  guard_target' continuous (λ (x : ℝ), x), apply @continuous_id ℝ _,
  -- guard_target' has_continuous_add ℝ, admit,
end
