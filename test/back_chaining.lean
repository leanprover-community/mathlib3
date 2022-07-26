open tactic

variables {α : Type*}

instance : has_subset (set α) := ⟨λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t⟩
instance : has_union (set α) := ⟨λ s t, {a | a ∈ s ∨ a ∈ t}⟩
instance : has_inter (set α) := ⟨λ s t, {a | a ∈ s ∧ a ∈ t}⟩

-- TODO: write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl
theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl
theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := rfl

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
begin
  dsimp [subset_def, union_def] at *,
  intros x h,
  cases h; back_chaining_using_hs
end

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
begin
  dsimp [subset_def, inter_def] at *,
  intros x h,
  split; back_chaining_using_hs
end
