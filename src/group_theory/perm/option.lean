/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser
-/
import group_theory.perm.basic
import data.equiv.option
import data.equiv.fin
import data.fintype.basic

/-!
# Permutations of `option α`
-/
open equiv

lemma equiv_functor.map_equiv_option_injective {α β : Type*} :
  function.injective (equiv_functor.map_equiv option : α ≃ β → option α ≃ option β) :=
equiv_functor.map_equiv.injective option option.some_injective


@[simp] lemma map_equiv_option_one {α : Type*} : equiv_functor.map_equiv option (1 : perm α) = 1 :=
by {ext, simp [equiv_functor.map_equiv, equiv_functor.map] }

@[simp] lemma map_equiv_option_refl {α : Type*} :
  equiv_functor.map_equiv option (equiv.refl α) = 1 := map_equiv_option_one

@[simp] lemma map_equiv_remove_none {α : Type*} [decidable_eq α] (σ : perm (option α)) :
  equiv_functor.map_equiv option (remove_none σ) = swap none (σ none) * σ :=
begin
  ext1 x,
  have : option.map ⇑(remove_none σ) x = (swap none (σ none)) (σ x),
  { cases x,
    { simp },
    { cases h : σ (some x),
      { simp [remove_none_none _ h], },
      { have hn : σ (some x) ≠ none := by simp [h],
        have hσn : σ (some x) ≠ σ none := σ.injective.ne (by simp),
        simp [remove_none_some _ ⟨_, h⟩, ←h, swap_apply_of_ne_of_ne hn hσn] } } },
  simpa using this,
end

/-- Permutations of `option α` are equivalent to fixing an
`option α` and permuting the remaining with a `perm α`.
The fixed `option α` is swapped with `none`. -/
@[simps] def equiv.perm.decompose_option {α : Type*} [decidable_eq α] :
  perm (option α) ≃ option α × perm α :=
{ to_fun := λ σ, (σ none, remove_none σ),
  inv_fun := λ i, swap none i.1 * (equiv_functor.map_equiv option i.2),
  left_inv := λ σ, by simp,
  right_inv := λ ⟨x, σ⟩, begin
    have : remove_none (swap none x * equiv_functor.map_equiv option σ) = σ :=
      equiv_functor.map_equiv_option_injective (by simp [←mul_assoc, equiv_functor.map]),
    simp [←perm.eq_inv_iff_eq, equiv_functor.map, this],
  end }

-- TODO: move these to data/equiv/basic, when we're ready to face the build time cost
section needs_a_home

@[simp] lemma perm_congr_apply {α β : Type*} (e : α ≃ β) (p : equiv.perm α) :
  e.perm_congr p = (e.symm.trans p).trans e := rfl

@[simp] lemma perm_congr_symm {α β : Type*} (e : α ≃ β) :
  e.perm_congr.symm = e.symm.perm_congr := rfl

@[simp] lemma trans_swap_trans_symm {α β} [decidable_eq α] [decidable_eq β] (a b : β)
  (e : α ≃ β) : (e.trans (swap a b)).trans e.symm = swap (e.symm a) (e.symm b) :=
symm_trans_swap_trans a b e.symm

end needs_a_home

-- TODO: these are in gh-5614, wait for that
namespace perm

variables {α : Type*}

@[simp] lemma trans_one {α : Sort*} {β : Type*} (e : α ≃ β) : e.trans (1 : perm β) = e :=
equiv.trans_refl e

@[simp] lemma mul_refl (e : perm α) : e * equiv.refl α = e := equiv.trans_refl e

@[simp] lemma one_symm : (1 : perm α).symm = 1 := equiv.refl_symm

@[simp] lemma refl_inv : (equiv.refl α : perm α)⁻¹ = 1 := equiv.refl_symm

@[simp] lemma one_trans {α : Type*} {β : Sort*} (e : α ≃ β) : (1 : perm α).trans e = e :=
equiv.refl_trans e

@[simp] lemma refl_mul (e : perm α) : equiv.refl α * e = e := equiv.refl_trans e

@[simp] lemma inv_trans (e : perm α) : e⁻¹.trans e = 1 := equiv.symm_trans e

@[simp] lemma mul_symm (e : perm α) : e * e.symm = 1 := equiv.symm_trans e

@[simp] lemma trans_inv (e : perm α) : e.trans e⁻¹ = 1 := equiv.trans_symm e

@[simp] lemma symm_mul (e : perm α) : e.symm * e = 1 := equiv.trans_symm e

end perm

/-- The set of all permutations of `option α` can be constructed by augmenting the set of
permutations of `α` by each element of `option α` in turn. -/
lemma finset.univ_perm_option {α : Type*} [decidable_eq α] [fintype α] :
  @finset.univ (perm $ option α) _ =
    (finset.univ : finset $ option α × perm α).map equiv.perm.decompose_option.symm.to_embedding :=
(finset.univ_map_equiv_to_embedding _).symm
