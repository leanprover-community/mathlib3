/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.perm.basic
import group_theory.subgroup
import group_theory.coset
import data.fintype.basic
/-!
# Subgroups within the permutations (self-equivalences) of a type `α`

This file defines some `subgroup`s that exist within `equiv.perm α`.

Where possible, it provides `decidable` instances so that `subgroup.quotient` is computably
finite.
-/

namespace equiv
namespace perm

/-- The subgroup of permutations which do not exchange elements between `α` and `β`;
those which are of the form `sum_congr sl sr`. -/
def sum_congr_subgroup (α β : Type*) : subgroup (perm (α ⊕ β)) :=
{ carrier := λ σ, ∃ (sl : perm α) (sr : perm β), σ = sum_congr sl sr,
  one_mem' := ⟨1, 1, sum_congr_one.symm⟩,
  mul_mem' := λ σ₁ σ₂ ⟨sl₁₂, sr₁₂, h₁₂⟩ ⟨sl₂₃, sr₂₃, h₂₃⟩,
    ⟨sl₁₂ * sl₂₃, sr₁₂ * sr₂₃, h₂₃.symm ▸ h₁₂.symm ▸ sum_congr_mul sl₁₂ sr₁₂ sl₂₃ sr₂₃⟩,
  inv_mem' := λ σ₁ ⟨sl, sr, h⟩, ⟨sl⁻¹, sr⁻¹, h.symm ▸ sum_congr_inv sl sr⟩ }

instance sum_congr_subgroup.decidable_mem {α β : Type*}
  [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  decidable_pred (λ x, x ∈ sum_congr_subgroup α β) := λ x, fintype.decidable_exists_fintype

/-- The subgroup of permutations which do not exchange elements between fibers;
those which are of the form `sigma_congr_right s`. -/
def sigma_congr_right_subgroup {α : Type*} (β : α → Type*) : subgroup (perm (Σ a, β a)) :=
{ carrier := λ σ, ∃ (s : Π a, perm (β a)), σ = sigma_congr_right s,
  one_mem' := ⟨λ i, 1, sigma_congr_right_one.symm⟩,
  mul_mem' := λ σ₁ σ₂ ⟨s₁₂, h₁₂⟩ ⟨s₂₃, h₂₃⟩,
    ⟨λ i, s₁₂ i * s₂₃ i, h₂₃.symm ▸ h₁₂.symm ▸ sigma_congr_right_mul s₁₂ s₂₃⟩,
  inv_mem' := λ σ₁ ⟨s, h⟩, ⟨λ i, (s i)⁻¹, h.symm ▸ sigma_congr_right_inv s⟩ }

instance sigma_congr_right_subgroup.decidable_mem {α : Type*} {β : α → Type*}
  [decidable_eq α] [∀ a, decidable_eq (β a)] [fintype α] [∀ a, fintype (β a)] :
  decidable_pred (λ x, x ∈ sigma_congr_right_subgroup β) :=
λ x, fintype.decidable_exists_fintype

end perm
end equiv
