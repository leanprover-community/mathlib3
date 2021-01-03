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

@[simp]
lemma map_equiv_remove_none {α : Type*} [decidable_eq α] [fintype α] (σ : perm (option α)) :
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

def equiv.perm.decompose_option {α : Type*} [decidable_eq α] [fintype α] :
  perm (option α) ≃ option α × perm α :=
{ to_fun := λ σ, (σ none, remove_none σ),
  inv_fun := λ i, swap none i.1 * (equiv_functor.map_equiv option i.2),
  left_inv := λ σ, by simp,
  right_inv := λ ⟨x, σ⟩, begin
    have : remove_none (swap none x * equiv_functor.map_equiv option σ) = σ :=
      equiv_functor.map_equiv_option_injective (by simp [←mul_assoc, equiv_functor.map]),
    simp [←perm.eq_inv_iff_eq, equiv_functor.map, this],
  end }

def equiv.perm.decompose_fin {n : ℕ} :
  perm (fin n.succ) ≃ fin n.succ × perm (fin n) :=
((equiv.perm_congr $ fin_succ_equiv n).trans equiv.perm.decompose_option).trans
  (equiv.prod_congr (fin_succ_equiv n).symm (equiv.refl _))

/-- The set of all permutations of `option α` can be constructed by augmenting the set of
permutations of `α` by each element of `option α` in turn. -/
lemma finset.univ_perm_option {α : Type*} [decidable_eq α] [fintype α] :
  @finset.univ (perm $ option α) _ =
    (finset.univ : finset $ option α × perm α).map equiv.perm.decompose_option.symm.to_embedding :=
(finset.univ_map_equiv_to_embedding _).symm

/-- The set of all permutations of `fin (n + 1)` can be constructed by augmenting the set of
permutations of `fin n` by each element of `fin (n + 1)` in turn. -/
lemma finset.univ_perm_fin_succ {n : ℕ} :
  @finset.univ (perm $ fin n.succ) _ = (finset.univ : finset $ fin n.succ × perm (fin n)).map
  equiv.perm.decompose_fin.symm.to_embedding :=
(finset.univ_map_equiv_to_embedding _).symm
