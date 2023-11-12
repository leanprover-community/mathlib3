/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.fintype.perm
import group_theory.perm.sign
import logic.equiv.option

/-!
# Permutations of `option α`

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/
open equiv

@[simp] lemma equiv.option_congr_one {α : Type*} : (1 : perm α).option_congr = 1 :=
equiv.option_congr_refl

@[simp] lemma equiv.option_congr_swap {α : Type*} [decidable_eq α] (x y : α) :
  option_congr (swap x y) = swap (some x) (some y) :=
begin
  ext (_ | i),
  { simp [swap_apply_of_ne_of_ne] },
  { by_cases hx : i = x,
    simp [hx, swap_apply_of_ne_of_ne],
    by_cases hy : i = y;
    simp [hx, hy, swap_apply_of_ne_of_ne], }
end

@[simp] lemma equiv.option_congr_sign {α : Type*} [decidable_eq α] [fintype α] (e : perm α) :
  perm.sign e.option_congr = perm.sign e :=
begin
  apply perm.swap_induction_on e,
  { simp [perm.one_def] },
  { intros f x y hne h,
    simp [h, hne, perm.mul_def, ←equiv.option_congr_trans] }
end

@[simp] lemma map_equiv_remove_none {α : Type*} [decidable_eq α] (σ : perm (option α)) :
  (remove_none σ).option_congr = swap none (σ none) * σ :=
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
  inv_fun := λ i, swap none i.1 * i.2.option_congr,
  left_inv := λ σ, by simp,
  right_inv := λ ⟨x, σ⟩, begin
    have : remove_none (swap none x * σ.option_congr) = σ :=
      equiv.option_congr_injective (by simp [←mul_assoc]),
    simp [←perm.eq_inv_iff_eq, this],
  end }

lemma equiv.perm.decompose_option_symm_of_none_apply {α : Type*} [decidable_eq α]
  (e : perm α) (i : option α) :
  equiv.perm.decompose_option.symm (none, e) i = i.map e :=
by simp

lemma equiv.perm.decompose_option_symm_sign {α : Type*} [decidable_eq α] [fintype α] (e : perm α) :
  perm.sign (equiv.perm.decompose_option.symm (none, e)) = perm.sign e :=
by simp

/-- The set of all permutations of `option α` can be constructed by augmenting the set of
permutations of `α` by each element of `option α` in turn. -/
lemma finset.univ_perm_option {α : Type*} [decidable_eq α] [fintype α] :
  @finset.univ (perm $ option α) _ =
    (finset.univ : finset $ option α × perm α).map equiv.perm.decompose_option.symm.to_embedding :=
(finset.univ_map_equiv_to_embedding _).symm
