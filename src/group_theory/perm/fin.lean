/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
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

section cycle_range

/-! ### `cycle_range` section

Define the permutation `fin.cycle_range i`, the cycle `(0 1 2 ... i)`.
The definition is slightly awkward because we need to keep track of the fact
that the cycle indeed stays within `fin n`. You're advised to use
`cycle_range_of_lt`, `cycle_range_self` and `cycle_range_of_gt` instead of
unfolding the definition.
-/

namespace fin

/-- `fin.cycle_range i` is the cycle `(0 1 2 ... i)`. -/
def cycle_range {n : ℕ} : fin n → perm (fin n)
-- We could write this as a product over `list.range`,
-- but the explicit `mk`s would become `coe`s and make the proofs a lot more annoying.
-- We could also write this as two `if`s, but it is very annoying to prove that
-- indeed results in a permutation.
| ⟨0, _⟩ := 1
| i@⟨nat.succ i', hi⟩ :=
have i' < i'.succ := nat.lt_succ_self _,
  swap ⟨0, lt_of_le_of_lt (nat.zero_le _) hi⟩ i * cycle_range ⟨i', this.trans hi⟩

@[simp] lemma cycle_range_zero' {n : ℕ} (h : 0 < n) : cycle_range ⟨0, h⟩ = 1 := rfl
@[simp] lemma cycle_range_zero {n : ℕ} : cycle_range (0 : fin n.succ) = 1 := rfl

/-- The definition of `cycle_range i.succ`, where `i` is given as a natural number.

This lemma is not really supposed to be used since it gives such an ugly right hand side,
use `cycle_range_of_lt`, `cycle_range_self` and `cycle_range_of_gt` instead.
-/
lemma cycle_range_succ_aux {n : ℕ} {i : ℕ} (hi : i + 1 < n) :
  cycle_range ⟨i + 1, hi⟩ = swap ⟨0, lt_of_le_of_lt (nat.zero_le _) hi⟩ ⟨i + 1, hi⟩ *
    cycle_range ⟨i, (nat.lt_succ_self _).trans hi⟩ := rfl

lemma cycle_range_of_gt {n : ℕ} {i j : fin n.succ} (h : i < j) :
  cycle_range i j = j :=
begin
  obtain ⟨i, hi⟩ := i,
  induction i with i ih,
  { simp },
  { have hi' := ((nat.lt_succ_self i).trans hi),
    have h' := ((nat.lt_succ_self i).trans h),
    rw [cycle_range_succ_aux, perm.mul_apply, ih hi' h', swap_apply_of_ne_of_ne],
    { rintro rfl,
      cases h' },
    { rintro rfl,
      have : i.succ ≠ i.succ := subtype.coe_injective.ne h.ne,
      contradiction } },
end

-- We do `of_le` first to get a stronger induction hypothesis,
-- then derive separate `of_lt` and `of_eq` results.
-- TODO: is there a non-awkward way to state this for `fin n` instead of `fin n.succ`?
lemma cycle_range_of_le {n : ℕ} {i j : fin n.succ} (h : j ≤ i) :
  cycle_range i j = if j = i then 0 else j + 1 :=
begin
  obtain ⟨i, hi⟩ := i,
  induction i with i ih,
  { simp [le_antisymm h (nat.zero_le j)], },

  rw [cycle_range_succ_aux, perm.mul_apply],
  -- Handle the `of_eq` and `of_lt` cases separately.
  split_ifs with heq,
  { rw [heq, cycle_range_of_gt (subtype.mk_lt_mk.mpr (nat.lt_succ_self i)),
        swap_apply_right, fin.mk_zero] },
  have h := lt_of_le_of_ne h heq,
  have j_lt_n : (j : ℕ) < n := lt_of_lt_of_le h (nat.lt_succ_iff.mp hi),
  rcases lt_or_eq_of_le (nat.lt_succ_iff.mp h) with h | rfl,
  { rw [ih _ h.le, if_neg, swap_apply_of_ne_of_ne],
    { intro hj0,
      have hj0 := congr_arg (coe : fin _ → ℕ) hj0,
      rw [fin.coe_add_one j_lt_n] at hj0,
      exact nat.succ_ne_zero _ hj0 },
    { intro hji,
      have hji := congr_arg (coe : fin _ → ℕ) hji,
      rw [fin.coe_add_one j_lt_n] at hji,
      have : (j + 1 : ℕ) ≠ i + 1 := (nat.succ_lt_succ h).ne,
      contradiction },
    { intro hji,
      have hji := congr_arg (coe : fin _ → ℕ) hji,
      exact h.ne hji } },
  { rw [ih _ (le_refl j), if_pos, fin.mk_zero, swap_apply_left, subtype.ext_iff,
        fin.coe_add_one j_lt_n, subtype.coe_mk],
    { refl },
    { ext, refl } }
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

@[simp] lemma sign_cycle_range {n : ℕ} (i : fin n) :
  perm.sign (cycle_range i) = (-1) ^ (i : ℕ) :=
begin
  obtain ⟨i, hi⟩ := i,
  induction i with i ih,
  { simp },
  { rw [cycle_range_succ_aux, monoid_hom.map_mul, ih, perm.sign_swap],
    { simp [pow_succ] },
    intro h,
    exact (nat.succ_ne_zero _).symm (congr_arg coe h) },
end

end fin

end cycle_range

section cycle_all

namespace fin

/-- `fin.cycle_all` is the cycle `(0 1 2 ... fin.last n)`. -/
def cycle_all : Π (n : ℕ), perm (fin n)
| 0 := 1
| (nat.succ n) := cycle_range (last n)

@[simp] lemma cycle_all_zero : cycle_all 0 = 1 := rfl

@[simp] lemma cycle_all_one : cycle_all 1 = 1 :=
subsingleton.elim _ _

lemma cycle_all_succ_apply {n : ℕ} (i : fin n.succ) :
  cycle_all n.succ i = if i = fin.last n then 0 else i + 1 :=
cycle_range_of_le (le_last _)

lemma coe_cycle_all {n : ℕ} (i : fin n.succ) :
  (cycle_all n.succ i : ℕ) = if i = fin.last n then 0 else i + 1 :=
begin
  rw cycle_all_succ_apply,
  split_ifs with h,
  { simp },
  have : (i : ℕ) < n := lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (coe_injective.ne h),
  exact coe_add_one this
end

lemma cycle_all_succ {n : ℕ} :
  cycle_all n.succ.succ = swap 0 (last n.succ) * cycle_range (cast_succ (last n)) :=
cycle_range_succ_aux _

@[simp] lemma sign_cycle_all {n : ℕ} : (cycle_all n.succ).sign = (-1) ^ n :=
sign_cycle_range _

end fin

end cycle_all
