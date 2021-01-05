/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Eric Wieser
-/
import group_theory.perm.option
import data.equiv.fin

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
by simp [equiv.perm.decompose_fin, equiv.perm_congr_def]

@[simp] lemma equiv.perm.decompose_fin_symm_of_one {n : ℕ} (p : fin (n + 1)) :
  equiv.perm.decompose_fin.symm (p, 1) = swap 0 p :=
equiv.perm.decompose_fin_symm_of_refl p

@[simp] lemma equiv.perm.decompose_fin_symm_apply_zero {n : ℕ}
  (p : fin (n + 1)) (e : perm (fin n)) :
  equiv.perm.decompose_fin.symm (p, e) 0 = p :=
by simp [equiv.perm.decompose_fin]

@[simp] lemma equiv.perm.decompose_fin_symm_apply_succ {n : ℕ}
  (e : perm (fin n)) (p : fin (n + 1)) (x : fin n) :
  equiv.perm.decompose_fin.symm (p, e) x.succ = swap 0 p (e x).succ :=
begin
  refine fin.cases _ _ p,
  { simp [equiv.perm.decompose_fin, equiv_functor.map] },
  { intros i,
    by_cases h : i = e x,
    { simp [h, equiv.perm.decompose_fin, equiv_functor.map] },
    { have h' : some (e x) ≠ some i := λ H, h (option.some_injective _ H).symm,
      have h'' : (e x).succ ≠ i.succ := λ H, h (fin.succ_injective _ H).symm,
      simp [h, h'', fin.succ_ne_zero, equiv.perm.decompose_fin, equiv_functor.map,
            swap_apply_of_ne_of_ne, swap_apply_of_ne_of_ne (option.some_ne_none (e x)) h'] } }
end

@[simp] lemma equiv.perm.decompose_fin_symm_apply_one {n : ℕ}
  (e : perm (fin (n + 1))) (p : fin (n + 2)) :
  equiv.perm.decompose_fin.symm (p, e) 1 = swap 0 p (e 0).succ :=
equiv.perm.decompose_fin_symm_apply_succ e p 0

@[simp] lemma equiv.perm.decompose_fin.symm_sign {n : ℕ} (p : fin (n + 1)) (e : perm (fin n)) :
  perm.sign (equiv.perm.decompose_fin.symm (p, e)) = ite (p = 0) 1 (-1) * perm.sign e :=
by { refine fin.cases _ _ p; simp [equiv.perm.decompose_fin, fin.succ_ne_zero] }

/-- The set of all permutations of `fin (n + 1)` can be constructed by augmenting the set of
permutations of `fin n` by each element of `fin (n + 1)` in turn. -/
lemma finset.univ_perm_fin_succ {n : ℕ} :
  @finset.univ (perm $ fin n.succ) _ = (finset.univ : finset $ fin n.succ × perm (fin n)).map
  equiv.perm.decompose_fin.symm.to_embedding :=
(finset.univ_map_equiv_to_embedding _).symm
