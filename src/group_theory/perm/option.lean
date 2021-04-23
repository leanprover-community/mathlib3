/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import group_theory.perm.sign
import data.equiv.option

/-!
# Permutations of `option α`
-/
open equiv

lemma equiv_functor.map_equiv_option_injective {α β : Type*} :
  function.injective (equiv_functor.map_equiv option : α ≃ β → option α ≃ option β) :=
equiv_functor.map_equiv.injective option option.some_injective

@[simp] lemma equiv_functor.option.map_none {α β : Type*} (e : α ≃ β) :
  equiv_functor.map e none = none :=
by simp [equiv_functor.map]

@[simp] lemma map_equiv_option_one {α : Type*} : equiv_functor.map_equiv option (1 : perm α) = 1 :=
by {ext, simp [equiv_functor.map_equiv, equiv_functor.map] }

@[simp] lemma map_equiv_option_refl {α : Type*} :
  equiv_functor.map_equiv option (equiv.refl α) = 1 := map_equiv_option_one

@[simp] lemma map_equiv_option_swap {α : Type*} [decidable_eq α] (x y : α) :
  equiv_functor.map_equiv option (swap x y) = swap (some x) (some y) :=
begin
  ext (_ | i),
  { simp [swap_apply_of_ne_of_ne] },
  { by_cases hx : i = x;
    by_cases hy : i = y;
    simp [hx, hy, swap_apply_of_ne_of_ne, equiv_functor.map] }
end

@[simp] lemma equiv_functor.option.sign {α : Type*} [decidable_eq α] [fintype α] (e : perm α) :
  perm.sign (equiv_functor.map_equiv option e) = perm.sign e :=
begin
  apply perm.swap_induction_on e,
  { simp [perm.one_def] },
  { intros f x y hne h,
    simp [h, hne, perm.mul_def, ←equiv_functor.map_equiv_trans] }
end

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

lemma equiv.perm.decompose_option_symm_of_none_apply {α : Type*} [decidable_eq α]
  (e : perm α) (i : option α) :
  equiv.perm.decompose_option.symm (none, e) i = i.map e :=
by simp [equiv_functor.map]

lemma equiv.perm.decompose_option_symm_sign {α : Type*} [decidable_eq α] [fintype α] (e : perm α) :
  perm.sign (equiv.perm.decompose_option.symm (none, e)) = perm.sign e :=
by simp

/-- The set of all permutations of `option α` can be constructed by augmenting the set of
permutations of `α` by each element of `option α` in turn. -/
lemma finset.univ_perm_option {α : Type*} [decidable_eq α] [fintype α] :
  @finset.univ (perm $ option α) _ =
    (finset.univ : finset $ option α × perm α).map equiv.perm.decompose_option.symm.to_embedding :=
(finset.univ_map_equiv_to_embedding _).symm
