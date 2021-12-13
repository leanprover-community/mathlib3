/-
Copyright (c) 2021 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import data.equiv.fin
import data.equiv.fintype
import group_theory.perm.option
import group_theory.perm.cycle_type

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
by rw [← fin.succ_zero_eq_one, equiv.perm.decompose_fin_symm_apply_succ e p 0]

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

Define the permutations `fin.cycle_range i`, the cycle `(0 1 2 ... i)`.
-/

open equiv.perm

lemma fin_rotate_succ {n : ℕ} :
  fin_rotate n.succ = decompose_fin.symm (1, fin_rotate n) :=
begin
  ext i,
  cases n, { simp },
  refine fin.cases _ (λ i, _) i,
  { simp },
  rw [coe_fin_rotate, decompose_fin_symm_apply_succ, if_congr (i.succ_eq_last_succ) rfl rfl],
  split_ifs with h,
  { simp [h] },
  { rw [fin.coe_succ, function.injective.map_swap fin.coe_injective, fin.coe_succ, coe_fin_rotate,
    if_neg h, fin.coe_zero, fin.coe_one,
    swap_apply_of_ne_of_ne (nat.succ_ne_zero _) (nat.succ_succ_ne_one _)] }
end

@[simp] lemma sign_fin_rotate (n : ℕ) : perm.sign (fin_rotate (n + 1)) = (-1) ^ n :=
begin
  induction n with n ih,
  { simp },
  { rw fin_rotate_succ, simp [ih, pow_succ] },
end

@[simp] lemma support_fin_rotate {n : ℕ} : support (fin_rotate (n + 2)) = finset.univ :=
by { ext, simp }

lemma support_fin_rotate_of_le {n : ℕ} (h : 2 ≤ n) :
  support (fin_rotate n) = finset.univ :=
begin
  obtain ⟨m, rfl⟩ := exists_add_of_le h,
  rw [add_comm, support_fin_rotate],
end

lemma is_cycle_fin_rotate {n : ℕ} : is_cycle (fin_rotate (n + 2)) :=
begin
  refine ⟨0, dec_trivial, λ x hx', ⟨x, _⟩⟩,
  clear hx',
  cases x with x hx,
  rw [coe_coe, gpow_coe_nat, fin.ext_iff, fin.coe_mk],
  induction x with x ih, { refl },
  rw [pow_succ, perm.mul_apply, coe_fin_rotate_of_ne_last, ih (lt_trans x.lt_succ_self hx)],
  rw [ne.def, fin.ext_iff, ih (lt_trans x.lt_succ_self hx), fin.coe_last],
  exact ne_of_lt (nat.lt_of_succ_lt_succ hx),
end

lemma is_cycle_fin_rotate_of_le {n : ℕ} (h : 2 ≤ n) :
  is_cycle (fin_rotate n) :=
begin
  obtain ⟨m, rfl⟩ := exists_add_of_le h,
  rw [add_comm],
  exact is_cycle_fin_rotate
end

@[simp] lemma cycle_type_fin_rotate {n : ℕ} : cycle_type (fin_rotate (n + 2)) = {n + 2} :=
begin
  rw [is_cycle_fin_rotate.cycle_type, support_fin_rotate, ← fintype.card, fintype.card_fin],
  refl,
end

lemma cycle_type_fin_rotate_of_le {n : ℕ} (h : 2 ≤ n) :
  cycle_type (fin_rotate n) = {n} :=
begin
  obtain ⟨m, rfl⟩ := exists_add_of_le h,
  rw [add_comm, cycle_type_fin_rotate]
end

namespace fin

/-- `fin.cycle_range i` is the cycle `(0 1 2 ... i)` leaving `(i+1 ... (n-1))` unchanged. -/
def cycle_range {n : ℕ} (i : fin n) : perm (fin n) :=
(fin_rotate (i + 1))
  .extend_domain (equiv.of_left_inverse' (fin.cast_le (nat.succ_le_of_lt i.is_lt)).to_embedding
    coe (by { intros x, ext, simp }))

lemma cycle_range_of_gt {n : ℕ} {i j : fin n.succ} (h : i < j) :
  cycle_range i j = j :=
begin
  rw [cycle_range, of_left_inverse'_eq_of_injective,
      ←function.embedding.to_equiv_range_eq_of_injective,
      ←via_fintype_embedding, via_fintype_embedding_apply_not_mem_range],
  simpa
end

lemma cycle_range_of_le {n : ℕ} {i j : fin n.succ} (h : j ≤ i) :
  cycle_range i j = if j = i then 0 else j + 1 :=
begin
  cases n,
  { simp },

  have : j = (fin.cast_le (nat.succ_le_of_lt i.is_lt)).to_embedding
    ⟨j, lt_of_le_of_lt h (nat.lt_succ_self i)⟩,
  { simp },

  ext,
  rw [this, cycle_range, of_left_inverse'_eq_of_injective,
      ←function.embedding.to_equiv_range_eq_of_injective,
      ←via_fintype_embedding, via_fintype_embedding_apply_image, rel_embedding.coe_fn_to_embedding,
      coe_cast_le, coe_fin_rotate],
  simp only [fin.ext_iff, coe_last, coe_mk, coe_zero, fin.eta, apply_ite coe, cast_le_mk],
  split_ifs with heq,
  { refl },
  { rw fin.coe_add_one_of_lt,
    exact lt_of_lt_of_le (lt_of_le_of_ne h (mt (congr_arg coe) heq)) (le_last i) }
end

lemma coe_cycle_range_of_le {n : ℕ} {i j : fin n.succ} (h : j ≤ i) :
  (cycle_range i j : ℕ) = if j = i then 0 else j + 1 :=
by { rw [cycle_range_of_le h],
     split_ifs with h', { refl },
     exact coe_add_one_of_lt (calc (j : ℕ) < i : fin.lt_iff_coe_lt_coe.mp (lt_of_le_of_ne h h')
                                       ... ≤ n : nat.lt_succ_iff.mp i.2) }

lemma cycle_range_of_lt {n : ℕ} {i j : fin n.succ} (h : j < i) :
  cycle_range i j = j + 1 :=
by rw [cycle_range_of_le h.le, if_neg h.ne]

lemma coe_cycle_range_of_lt {n : ℕ} {i j : fin n.succ} (h : j < i) :
  (cycle_range i j : ℕ) = j + 1 :=
by rw [coe_cycle_range_of_le h.le, if_neg h.ne]

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

@[simp] lemma cycle_range_last (n : ℕ) : cycle_range (last n) = fin_rotate (n + 1) :=
by { ext i, rw [coe_cycle_range_of_le (le_last _), coe_fin_rotate] }

@[simp] lemma cycle_range_zero' {n : ℕ} (h : 0 < n) : cycle_range ⟨0, h⟩ = 1 :=
begin
  cases n with n,
  { cases h },
  exact cycle_range_zero n
end

@[simp] lemma sign_cycle_range {n : ℕ} (i : fin n) :
  perm.sign (cycle_range i) = (-1) ^ (i : ℕ) :=
by simp [cycle_range]

@[simp] lemma succ_above_cycle_range {n : ℕ} (i j : fin n) :
  i.succ.succ_above (i.cycle_range j) = swap 0 i.succ j.succ :=
begin
  cases n,
  { rcases j with ⟨_, ⟨⟩⟩ },
  rcases lt_trichotomy j i with hlt | heq | hgt,
  { have : (j + 1).cast_succ = j.succ,
    { ext, rw [coe_cast_succ, coe_succ, fin.coe_add_one_of_lt (lt_of_lt_of_le hlt i.le_last)] },
    rw [fin.cycle_range_of_lt hlt, fin.succ_above_below, this, swap_apply_of_ne_of_ne],
    { apply fin.succ_ne_zero },
    { exact (fin.succ_injective _).ne hlt.ne },
    { rw fin.lt_iff_coe_lt_coe,
      simpa [this] using hlt } },
  { rw [heq, fin.cycle_range_self, fin.succ_above_below, swap_apply_right, fin.cast_succ_zero],
    { rw fin.cast_succ_zero, apply fin.succ_pos } },
  { rw [fin.cycle_range_of_gt hgt, fin.succ_above_above, swap_apply_of_ne_of_ne],
    { apply fin.succ_ne_zero },
    { apply (fin.succ_injective _).ne hgt.ne.symm },
    { simpa [fin.le_iff_coe_le_coe] using hgt } },
end

@[simp] lemma cycle_range_succ_above {n : ℕ} (i : fin (n + 1)) (j : fin n) :
  i.cycle_range (i.succ_above j) = j.succ :=
begin
  cases lt_or_ge j.cast_succ i with h h,
  { rw [fin.succ_above_below _ _ h, fin.cycle_range_of_lt h, fin.coe_succ_eq_succ] },
  { rw [fin.succ_above_above _ _ h, fin.cycle_range_of_gt (fin.le_cast_succ_iff.mp h)] }
end

@[simp] lemma cycle_range_symm_zero {n : ℕ} (i : fin (n + 1)) :
  i.cycle_range.symm 0 = i :=
i.cycle_range.injective (by simp)

@[simp] lemma cycle_range_symm_succ {n : ℕ} (i : fin (n + 1)) (j : fin n) :
  i.cycle_range.symm j.succ = i.succ_above j :=
i.cycle_range.injective (by simp)

lemma is_cycle_cycle_range {n : ℕ} {i : fin (n + 1)} (h0 : i ≠ 0) : is_cycle (cycle_range i) :=
begin
  cases i with i hi,
  cases i,
  { exact (h0 rfl).elim },
  exact is_cycle_fin_rotate.extend_domain _,
end

@[simp] lemma cycle_type_cycle_range {n : ℕ} {i : fin (n + 1)} (h0 : i ≠ 0) :
  cycle_type (cycle_range i) = {i + 1} :=
begin
  cases i with i hi,
  cases i,
  { exact (h0 rfl).elim },
  rw [cycle_range, cycle_type_extend_domain],
  exact cycle_type_fin_rotate,
end

lemma is_three_cycle_cycle_range_two {n : ℕ} :
  is_three_cycle (cycle_range 2 : perm (fin (n + 3))) :=
begin
  rw [is_three_cycle, cycle_type_cycle_range];
  dec_trivial
end

end fin

end cycle_range
