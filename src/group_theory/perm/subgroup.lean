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

/-- `equiv.perm.sum_congr` as a `monoid_hom`. -/
@[simps apply]
def sum_congr_hom (α β : Type*) :
  perm α × perm β →* perm (α ⊕ β) :=
{ to_fun := λ a, a.1.sum_congr a.2,
  map_one' := sum_congr_one,
  map_mul' := λ a b, (sum_congr_mul _ _ _ _).symm}

instance sum_congr_hom.left_rel_range_decidable {α β : Type*}
  [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  decidable_rel $ (quotient_group.left_rel (sum_congr_hom α β).range).r :=
λ σ₁ σ₂, fintype.decidable_exists_fintype

@[simp]
lemma sum_congr_hom.card_range {α β : Type*}
  [decidable_eq α] [decidable_eq β] [fintype α] [fintype β] :
  fintype.card (equiv.perm.sum_congr_hom α β).range
    = fintype.card (equiv.perm ιa × equiv.perm ιb) :=
fintype.card_eq.mpr ⟨(equiv.set.range (equiv.perm.sum_congr_hom ιa ιb) begin
  intros x y h,
  cases x,
  cases y,
  rw  prod.mk.inj_iff,
  replace h := λ j, _root_.congr_arg (λ e : equiv.perm _, e j) h,
  split; ext i,
  simpa [equiv.perm.sum_congr_hom_apply] using h (sum.inl i),
  simpa [equiv.perm.sum_congr_hom_apply] using h (sum.inr i),
end).symm⟩

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
