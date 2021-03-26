/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.equiv.fin
import data.zmod.basic
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

section cycle

/-! ### `cycle` section

Define the permutations `fin.cycle_all n`, the cycle `(0 1 2 ... (n - 1 : fin n))`
and `fin.cycle_range i`, the cycle `(0 1 2 ... i)`.
-/

namespace fin

open equiv.perm

/-- `fin.cycle_all` is the cycle `(0 1 2 ... fin.last n)`.

If `n` is `0` or `1`, this will be the identity permutation,
otherwise it sends `i` to `i + 1` and `fin.last n` to `0`.
-/
def cycle_all : Π (n : ℕ), perm (fin n)
| 0 := 1
| (nat.succ n) := let inst := fin.comm_ring n in by exactI equiv.add_right 1

@[simp] lemma cycle_all_zero : cycle_all 0 = 1 := rfl

@[simp] lemma cycle_all_one : cycle_all 1 = 1 :=
subsingleton.elim _ _

lemma cycle_all_succ_apply {n : ℕ} (i : fin n.succ) :
  cycle_all n.succ i = i + 1 :=
rfl

@[simp] lemma cycle_all_apply_zero {n : ℕ} : cycle_all n.succ 0 = 1 :=
by rw [cycle_all_succ_apply, zero_add]

@[simp] lemma last_add_one {n : ℕ} :
  last n + 1 = 0 :=
begin
  cases n,
  { apply subsingleton.elim },
  { ext, rw [coe_add, coe_zero, coe_last, coe_one, nat.mod_self] }
end

@[simp] lemma cycle_all_apply_last {n : ℕ} : cycle_all n.succ (last n) = 0 :=
by { ext, rw [cycle_all_succ_apply, last_add_one] }

lemma coe_cycle_all_of_ne_last {n : ℕ} {i : fin n.succ} (h : i ≠ last n) :
  (cycle_all n.succ i : ℕ) = i + 1 :=
begin
  rw cycle_all_succ_apply,
  have : (i : ℕ) < n := lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (coe_injective.ne h),
  exact coe_add_one this
end

lemma coe_cycle_all {n : ℕ} (i : fin n.succ) :
  (cycle_all n.succ i : ℕ) = if i = fin.last n then 0 else i + 1 :=
begin
  split_ifs with h,
  { simp [cycle_all_succ_apply, h] },
  exact coe_cycle_all_of_ne_last h
end

@[simp] lemma last_succ {n : ℕ} : last (n + 1) = (last n).succ :=
by { ext, simp }

lemma function.injective.map_swap {α β : Type*} [decidable_eq α] [decidable_eq β]
  {f : α → β} (hf : function.injective f) (x y z : α) :
  f (swap x y z) = swap (f x) (f y) (f z) :=
begin
  conv_rhs { rw swap_apply_def },
  split_ifs with h₁ h₂,
  { rw [hf h₁, swap_apply_left] },
  { rw [hf h₂, swap_apply_right] },
  { rw [swap_apply_of_ne_of_ne (mt (congr_arg f) h₁) (mt (congr_arg f) h₂)] },
end

lemma cycle_all_succ {n : ℕ} :
  cycle_all n.succ = decompose_fin.symm (1, cycle_all n) :=
begin
  ext i,
  cases n, { simp },
  refine fin.cases _ (λ i, _) i,
  { simp },
  rw [coe_cycle_all, decompose_fin_symm_apply_succ,
      if_congr (show i.succ = last (n + 1) ↔ i = last n, from _) rfl rfl],
  split_ifs with h,
  { simp [h] },
  { rw [fin.coe_succ, function.injective.map_swap fin.coe_injective, fin.coe_succ, coe_cycle_all,
        if_neg h, fin.coe_zero, fin.coe_one,
        swap_apply_of_ne_of_ne (nat.succ_ne_zero _) (nat.succ_succ_ne_one _)] },
  { rw [last_succ, (fin.succ_injective _).eq_iff] }
end

@[simp] lemma sign_cycle_all (n : ℕ) : (cycle_all (n + 1)).sign = (-1) ^ n :=
begin
  induction n with n ih,
  { simp },
  { rw cycle_all_succ, simp [ih, pow_succ] },
end

@[simp] lemma range_cast_le {n k : ℕ} (h : n ≤ k) :
  set.range (cast_le h) = {i | (i : ℕ) < n} :=
set.ext (λ x, ⟨λ ⟨y, hy⟩, hy ▸ y.2, λ hx, ⟨⟨x, hx⟩, fin.ext rfl⟩⟩)

@[simp] lemma range_cast_succ {n : ℕ} :
  set.range (cast_succ : fin n → fin n.succ) = {i | (i : ℕ) < n} :=
range_cast_le _

@[simp] lemma coe_set_range_cast_le_symm {n k : ℕ} (h : n ≤ k) (i : fin k) (hi) :
  ((equiv.set.range _ ((cast_le h).injective)).symm ⟨i, hi⟩ : ℕ) = i :=
begin
  rw ← coe_cast_le,
  exact congr_arg coe (equiv.set.apply_range_symm _ _ _)
end

@[simp] lemma coe_set_range_cast_succ_symm {n : ℕ} (i : fin n.succ) (hi) :
  ((equiv.set.range cast_succ (cast_succ_injective _)).symm ⟨i, hi⟩ : ℕ) = i :=
begin
  rw ← coe_cast_succ,
  exact congr_arg coe (equiv.set.apply_range_symm _ _ _)
end

@[simp] lemma equiv.set.range_of_left_inverse_symm_apply {α β : Sort*}
  (f : α → β) (f_inv hf) (x : set.range f) :
  (equiv.set.range_of_left_inverse f f_inv hf).symm x = f_inv ⟨classical.some x.2⟩ x :=
rfl

@[simp] lemma equiv.set.range_of_left_inverse'_symm_apply {α β : Sort*}
  (f : α → β) (f_inv hf) (x : set.range f) :
  (equiv.set.range_of_left_inverse' f f_inv hf).symm x = f_inv x :=
rfl

/-- `fin.cycle_range i` is the cycle `(0 1 2 ... i)`. -/
def cycle_range {n : ℕ} (i : fin n) : perm (fin n) :=
((equiv.set.range_of_left_inverse' (fin.cast_le i.2) coe (by { intros x, ext, simp }))
  .perm_congr (cycle_all (i + 1)))
  .subtype_congr 1

lemma cycle_range_of_gt {n : ℕ} {i j : fin n.succ} (h : i < j) :
  cycle_range i j = j :=
begin
  rw [cycle_range, perm.subtype_congr.apply, dif_neg, perm.one_apply, subtype.coe_mk],
  { simpa only [range_cast_le, val_eq_coe, not_lt, set.mem_set_of_eq] },
end

lemma cycle_range_of_le {n : ℕ} {i j : fin n.succ} (h : j ≤ i) :
  cycle_range i j = if j = i then 0 else j + 1 :=
begin
  have j_mod_i : (j : ℕ) % (↑i : ℕ).succ = j := nat.mod_eq_of_lt (nat.lt_succ_of_le h),
  ext,
  rw [cycle_range, perm.subtype_congr.apply, dif_pos,  perm_congr_apply,
       equiv.set.range_of_left_inverse_apply, subtype.coe_mk, coe_cast_le, coe_cycle_all],
  push_cast,
  apply if_ctx_congr,
  { simp [fin.ext_iff, equiv.set.range_of_left_inverse_symm_apply, j_mod_i] },
  { simp },
  { intro hij,
    have : (j : ℕ) < n := lt_of_lt_of_le
        (lt_of_le_of_ne h (coe_injective.ne hij))
        (nat.succ_le_succ_iff.mp i.2),
    simp [coe_add_one this, j_mod_i] },
  { simp only [range_cast_le, val_eq_coe, not_lt, set.mem_set_of_eq],
    exact nat.lt_succ_of_le h }
end

lemma cycle_range_of_lt {n : ℕ} {i j : fin n.succ} (h : j < i) :
  cycle_range i j = j + 1 :=
by rw [cycle_range_of_le h.le, if_neg h.ne]

lemma cycle_range_of_eq {n : ℕ} {i j : fin n.succ} (h : j = i) :
  cycle_range i j = 0 :=
by rw [cycle_range_of_le h.le, if_pos h]

@[simp]
lemma cycle_range_self {n : ℕ} (i : fin n.succ) :
  cycle_range i i = 0 :=
cycle_range_of_eq rfl

lemma cycle_range_apply {n : ℕ} (i j : fin n.succ) :
  cycle_range i j = if j < i then j + 1 else if j = i then 0 else j :=
begin
  split_ifs with h₁ h₂,
  { exact cycle_range_of_lt h₁ },
  { exact cycle_range_of_eq h₂ },
  { exact cycle_range_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (ne.symm h₂)) },
end

@[simp] lemma cycle_range_zero (n : ℕ) : cycle_range (0 : fin n.succ) = 1 :=
begin
  ext j,
  refine fin.cases _ (λ j, _) j,
  { simp },
  { rw [cycle_range_of_gt (fin.succ_pos j), one_apply] },
end

@[simp] lemma cycle_range_zero' {n : ℕ} (h : 0 < n) : cycle_range ⟨0, h⟩ = 1 :=
begin
  cases n with n,
  { cases h },
  exact cycle_range_zero n
end

@[simp] lemma sign_cycle_range {n : ℕ} (i : fin n) :
  perm.sign (cycle_range i) = (-1) ^ (i : ℕ) :=
by { simp only [cycle_range, sign_perm_congr, mul_one, sign_one, sign_subtype_congr],
     exact sign_cycle_all i }

end fin

end cycle
