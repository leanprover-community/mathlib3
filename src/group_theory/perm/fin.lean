/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser
-/
import group_theory.perm.option

/-!
# Permutations of `fin n`
-/
open equiv

/-- Permutations of `fin (n + 1)` are equivalent to fixing a single
`fin (n + 1)` and permuting the remaining with a `perm (fin n)`.
The fixed `fin (n + 1)` is swapped with `0`. -/
def equiv.perm.decompose_fin {n : ℕ} :
  perm (fin n.succ) ≃ fin n.succ × perm (fin n) :=
((equiv.perm_congr $ fin_succ_equiv n).trans equiv.perm.decompose_option).trans
  (equiv.prod_congr (fin_succ_equiv n).symm (equiv.refl _))

@[simp] lemma equiv.perm.decompose_fin_symm_of_refl {n : ℕ} (p : fin (n + 1)) :
  equiv.perm.decompose_fin.symm (p, equiv.refl _) = swap 0 p :=
by simp [equiv.perm.decompose_fin]

@[simp] lemma equiv.perm.decompose_fin_symm_of_one {n : ℕ} (p : fin (n + 1)) :
  equiv.perm.decompose_fin.symm (p, 1) = swap 0 p :=
equiv.perm.decompose_fin_symm_of_refl p

/-- The set of all permutations of `fin (n + 1)` can be constructed by augmenting the set of
permutations of `fin n` by each element of `fin (n + 1)` in turn. -/
lemma finset.univ_perm_fin_succ {n : ℕ} :
  @finset.univ (perm $ fin n.succ) _ = (finset.univ : finset $ fin n.succ × perm (fin n)).map
  equiv.perm.decompose_fin.symm.to_embedding :=
(finset.univ_map_equiv_to_embedding _).symm
