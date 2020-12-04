import group_theory.perm.sign

variables {ι : Type*} {α : ι → Type*} {β : ι → Type*} {γ : ι → Type*}

namespace equiv

@[simp] lemma sigma_congr_right_trans (σ₁ : Π i, α i ≃ β i) (σ₂ : Π i, β i ≃ γ i) :
  (sigma_congr_right σ₁).trans (sigma_congr_right σ₂) = sigma_congr_right (λ i, (σ₁ i).trans (σ₂ i)) :=
by { ext1 x, cases x, simp}

@[simp] lemma sigma_congr_right_symm (σ : Π i, α i ≃ β i) :
  (sigma_congr_right σ).symm = sigma_congr_right (λ i, (σ i).symm) :=
by { ext1 x, cases x, simp}

@[simp] lemma sigma_congr_right_refl :
  (sigma_congr_right (λ i, equiv.refl (α i))) = equiv.refl (Σ i, α i) :=
by { ext1 x, cases x, simp}

end equiv

/-- An equivalence relation between permutations of indexed sets of types that does not
care about internal permutations within a type.

For instance, this represents ways to -/
def mod_perm_within : setoid (equiv.perm (Σ i, α i)) :=
{ r := λ σ₁ σ₂, ∃ s, σ₁ = σ₂ * equiv.sigma_congr_right s,
  iseqv := ⟨
    λ σ, ⟨λ i, 1, by simp [equiv.perm.mul_def, equiv.perm.one_def]⟩,
    λ σ₁ σ₂ ⟨s, h⟩, ⟨λ i, (s i)⁻¹, by {
      rw [h, mul_assoc],
      simp [equiv.perm.mul_def, equiv.perm.inv_def]}⟩,
    λ σ₁ σ₂ σ₃ ⟨s₁₂, h₁₂⟩ ⟨s₂₃, h₂₃⟩, ⟨λ i, s₂₃ i * s₁₂ i, by {
      rw [h₁₂, h₂₃, mul_assoc],
      simp [equiv.perm.mul_def, equiv.perm.inv_def]}⟩
⟩}

open equiv
