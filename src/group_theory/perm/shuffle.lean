import group_theory.perm.sign
import data.equiv.fin

variables {ι : Type*} (α : ι → Type*)

/-- An equivalence relation between permutations of indexed sets of types that does not
care about internal permutations within a type.

For instance, this represents ways to -/
def mod_sigma_congr : setoid (equiv.perm (Σ i, α i)) :=
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

def mod_sum_congr {α β : Type*} : setoid (equiv.perm (α ⊕ β)) :=
{ r := λ σ₁ σ₂, ∃ sl sr, σ₁ = σ₂ * equiv.sum_congr sl sr,
  iseqv := ⟨
    λ σ, ⟨1, 1, by simp [equiv.perm.mul_def, equiv.perm.one_def]⟩,
    λ σ₁ σ₂ ⟨sl, sr, h⟩, ⟨sl⁻¹, sr⁻¹, by {
      rw [h, mul_assoc],
      simp [equiv.perm.mul_def, equiv.perm.inv_def]}⟩,
    λ σ₁ σ₂ σ₃ ⟨sl₁₂, sr₁₂, h₁₂⟩ ⟨sl₂₃, sr₂₃, h₂₃⟩, ⟨sl₂₃ * sl₁₂, sr₂₃ * sr₁₂, by {
      rw [h₁₂, h₂₃, mul_assoc],
      simp [equiv.perm.mul_def, equiv.perm.inv_def]}⟩
⟩}


def is_shuffle {m n} (p : fin m ⊕ fin n ≃ fin (m + n)) : Prop :=
monotone (p ∘ sum.inl) ∧ monotone (p ∘ sum.inr)

instance {m n : ℕ} : decidable_pred (@is_shuffle m n) :=
λ p, by {unfold is_shuffle monotone, apply_instance}

@[derive has_coe_to_fun]
def shuffle (m n) : Type* := {p : fin m ⊕ fin n ≃ fin (m + n) // is_shuffle p }

namespace shuffle

variables {m n : ℕ}

lemma coe_eq_val (s : shuffle m n) : ⇑s = s.val := rfl

def to_perm (s : shuffle m n) : (equiv.perm $ fin (m + n)) := sum_fin_sum_equiv.symm.trans s.val

instance : has_coe_t (shuffle m n) (equiv.perm $ fin (m + n)) := ⟨to_perm⟩


instance : fintype (shuffle m n) := subtype.fintype _

end shuffle

-- instance [∀ i, decidable_eq (α i)] [∀ i, fintype (α i)] : decidable_rel (mod_perm_within α).r :=
-- λ σ₁ σ₂, begin
--   dunfold mod_perm_within,
--   dsimp,
--   let p := ∀ i (a : α i), ((σ₂⁻¹ * σ₁) ⟨i, a⟩).fst = i,
--   haveI : decidable p := sorry,
--   by_cases p; dsimp only [p] at h,
--   apply decidable.is_true,
--   existsi _,
--   apply eq_mul_of_inv_mul_eq,
--   ext1 x,
--   cases x with i a,
--   simp only [equiv.sigma_congr_right_apply],
--   replace h := h i a,
--   apply @decidable.by_cases p _,
--   simp_rw eq_mul_iff_
--   apply decidable.exis,
-- end

open equiv

#print has_mul.mul
