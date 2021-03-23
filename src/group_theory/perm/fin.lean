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

/-- `fin.cycle_all` is the cycle `(0 1 2 ... fin.last n)`. -/
def cycle_all : Π (n : ℕ), perm (fin n)
| 0 := 1
| (nat.succ n) :=
{ to_fun := λ i, if hi : i = fin.last n then 0 else
    ⟨i + 1, nat.succ_lt_succ (lt_of_le_of_ne (nat.lt_succ_iff.mp i.2) (coe_injective.ne hi))⟩,
  inv_fun := λ i, if i = 0 then fin.last n else
    ⟨i - 1, lt_of_le_of_lt (nat.sub_le _ _) i.2⟩,
  left_inv := λ i, begin
    simp only,
    split_ifs with h₁ h₂,
    { rw h₁ },
    { cases h₂ },
    { simp },
  end,
  right_inv := λ i, begin
    simp only,
    split_ifs with h₁,
    { simp only at h₁,
      split_ifs at h₁ with h₂,
      { rw h₂ },
      { -- We have n = i - 1 ≤ i < n.succ so we want to conclude i = n = 0.
        -- TODO: this is a bit awkward, can we make it easier?
        have i_lt_n : (i : ℕ) < n.succ := i.2,
        cases i with i hi,
        have eq_n : i - 1 = n := congr_arg coe h₁,
        rw [coe_mk, ← eq_n] at i_lt_n,
        cases i,
        { refl },
        { simpa using i_lt_n } } },
    { simp only [if_pos h] at h₁,
      cases h₁ rfl },
    { ext,
      simpa only [coe_mk]
        using nat.sub_add_cancel (nat.succ_le_of_lt
          (nat.pos_of_ne_zero (coe_injective.ne h))) }
  end }

@[simp] lemma cycle_all_zero : cycle_all 0 = 1 := rfl

lemma cycle_all_succ_apply {n : ℕ} (i : fin n.succ) :
  cycle_all n.succ i = if i = fin.last n then 0 else i + 1 :=
begin
  simp only [cycle_all, coe_fn_mk],
  split_ifs with h₁ h₂ h₂,
  { simp },
  { ext,
    have : (i : ℕ) < n := lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (coe_injective.ne h₁),
    rw [coe_mk, coe_add_one this] },
end

lemma coe_cycle_all {n : ℕ} (i : fin n.succ) :
  (cycle_all n.succ i : ℕ) = if i = fin.last n then 0 else i + 1 :=
begin
  rw cycle_all_succ_apply,
  split_ifs with h,
  { simp },
  have : (i : ℕ) < n := lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (coe_injective.ne h),
  exact coe_add_one this
end

@[simp] lemma cycle_all_one : cycle_all 1 = 1 :=
subsingleton.elim _ _

-- I'm surprised this is missing - added in #6817
instance decidable_fintype_range {α ι : Type*} [fintype ι] (f : ι → α) [decidable_eq α] :
  decidable_pred (λ (x : α), x ∈ set.range f) :=
λ x, begin
  unfold set.range,
  dsimp [set.mem_set_of_eq],
  apply_instance,
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

lemma cycle_all_succ {n : ℕ} : cycle_all n.succ =
  swap 0 (fin.last n) *
    perm.subtype_congr ((equiv.set.range _ (fin.cast_succ_injective _)).perm_congr (cycle_all n)) 1 :=
begin
  cases n with n,
  { exact subsingleton.elim _ _ },
  { ext i,
    rw cycle_all_succ_apply,
    split_ifs with h₁; rw [perm.coe_mul, function.comp_app, perm.subtype_congr.apply],
    { rw [h₁, dif_neg, perm.one_apply, subtype.coe_mk, swap_apply_right],
      simp [range_cast_succ] },
    { have i_lt_succ_n : (i : ℕ) < n.succ :=
        lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (coe_injective.ne h₁),
      have : i ∈ set.range (cast_succ : fin n.succ → fin n.succ.succ),
      { simpa using i_lt_succ_n },
      rw [dif_pos this, perm_congr_apply, equiv.set.range_apply, cycle_all_succ_apply],
      split_ifs with h₂,
      { have := (equiv.set.apply_range_symm _ _ _).symm.trans (congr_arg cast_succ h₂),
        rw subtype.coe_mk at this,
        rw [subtype.coe_mk, cast_succ_zero, swap_apply_left, coe_last, coe_add_one i_lt_succ_n, this],
        simp },
      { have i_lt_n : (i : ℕ) < n,
        { refine lt_of_le_of_ne (nat.succ_le_succ_iff.mp i_lt_succ_n) _,
          have h₂ := coe_injective.ne h₂,
          rwa coe_set_range_cast_succ_symm at h₂ },
        have : cast_succ ((equiv.set.range cast_succ _).symm ⟨i, this⟩ + 1) = i + 1,
        { ext,
          rw [coe_cast_succ, coe_add_one, coe_add_one i_lt_succ_n, coe_set_range_cast_succ_symm],
          { rwa coe_set_range_cast_succ_symm } },
        rw [subtype.coe_mk, this, swap_apply_of_ne_of_ne],
        { intro h,
          have h := congr_arg coe h,
          rw coe_add_one i_lt_succ_n at h,
          cases h },
        { apply ne_of_lt,
          rw [fin.lt_iff_coe_lt_coe, coe_add_one i_lt_succ_n, coe_last],
          exact nat.succ_lt_succ i_lt_n } } } },
end

@[simp] lemma sign_cycle_all {n : ℕ} : (cycle_all n.succ).sign = (-1) ^ n :=
begin
  induction n with n ih,
  { simp [cycle_all_succ] },
  { rw cycle_all_succ, -- only rewrite once!
    simp only [ih, mul_one, perm.sign_swap', one_mul, perm.sign_mul, perm.sign_one,
      perm.sign_perm_congr, units.neg_mul, ite_mul, perm.sign_subtype_congr],
    rw [if_neg, pow_succ, units.neg_mul, one_mul],
    intros h,
    have := congr_arg (coe : _ → ℕ) h,
    cases h },
end

/-- `fin.cycle_range i` is the cycle `(0 1 2 ... i)`. -/
noncomputable def cycle_range {n : ℕ} (i : fin n) : perm (fin n) :=
perm.subtype_congr ((equiv.set.range _ (cast_le i.2).injective).perm_congr (cycle_all (i + 1))) 1

lemma cycle_range_def {n : ℕ} (i : fin n) :
  cycle_range i =
    perm.subtype_congr ((equiv.set.range _ (cast_le i.2).injective).perm_congr (cycle_all (i + 1))) 1 :=
rfl

lemma cycle_range_of_gt {n : ℕ} {i j : fin n.succ} (h : i < j) :
  cycle_range i j = j :=
begin
  rw [cycle_range, perm.subtype_congr.apply, dif_neg, perm.one_apply, subtype.coe_mk],
  { simpa only [range_cast_le, val_eq_coe, not_lt, set.mem_set_of_eq] },
end

lemma cycle_range_of_le {n : ℕ} {i j : fin n.succ} (h : j ≤ i) :
  cycle_range i j = if j = i then 0 else j + 1 :=
begin
  ext,
  rw [cycle_range, perm.subtype_congr.apply, dif_pos, perm_congr_apply, equiv.set.range_apply,
      subtype.coe_mk, coe_cast_le, coe_cycle_all],
  push_cast,
  apply if_ctx_congr,
  { simp [fin.ext_iff] },
  { simp },
  { intro hij,
    have : (j : ℕ) < n := lt_of_lt_of_le
      (lt_of_le_of_ne h (coe_injective.ne hij))
      (nat.succ_le_succ_iff.mp i.2),
    simp [coe_add_one this] },
  { simp only [range_cast_le, val_eq_coe, not_lt, set.mem_set_of_eq],
    exact nat.lt_succ_of_le h },
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

@[simp]
lemma cycle_range_zero {n : ℕ} : cycle_range (0 : fin n.succ) = 1 :=
begin
  ext j,
  refine fin.cases _ (λ j, _) j,
  { simp },
  { simp [cycle_range_of_gt (fin.succ_pos _)] },
end

@[simp]
lemma cycle_range_zero' {n : ℕ} (h : 0 < n) : cycle_range ⟨0, h⟩ = 1 :=
begin
  cases n,
  { cases h },
  exact cycle_range_zero
end

lemma cycle_range_apply {n : ℕ} (i j : fin n.succ) :
  cycle_range i j = if j < i then j + 1 else if j = i then 0 else j :=
begin
  split_ifs with h₁ h₂,
  { exact cycle_range_of_lt h₁ },
  { exact cycle_range_of_eq h₂ },
  { exact cycle_range_of_gt (lt_of_le_of_ne (le_of_not_gt h₁) (ne.symm h₂)) },
end

lemma cycle_range_succ {n : ℕ} (i : fin n) :
  cycle_range i.succ = swap 0 i.succ * cycle_range (cast_succ i) :=
begin
  ext j,
  rw [perm.mul_apply, cycle_range_apply],
  split_ifs with h₁ h₂,
  { rw cycle_range_of_le,
    split_ifs with h₂,
    { simp [h₂] },
    { have : (j : ℕ) < n,
      { refine lt_of_lt_of_le (fin.lt_iff_coe_lt_coe.mp h₁) _,
        rw coe_succ,
        exact i.2 },
      rw swap_apply_of_ne_of_ne;
        rw [ne.def, fin.ext_iff, coe_add_one this],
      { rintros ⟨⟩ },
      { rw coe_succ,
        exact nat.succ_injective.ne (fin.coe_injective.ne h₂) } },
    { rw [fin.lt_iff_coe_lt_coe, fin.coe_succ] at h₁,
      exact nat.lt_succ_iff.mp h₁ } },
  { rw [h₂, cycle_range_of_gt (cast_succ_lt_succ i), swap_apply_right] },
  { have : i.succ ≤ j := le_of_not_gt h₁,
    rw [cycle_range_of_gt (lt_of_lt_of_le (cast_succ_lt_succ i) this), swap_apply_of_ne_of_ne _ h₂],
    { rintro rfl, have := i.succ_pos, contradiction } },
end

@[simp] lemma sign_cycle_range {n : ℕ} (i : fin n) :
  perm.sign (cycle_range i) = (-1) ^ (i : ℕ) :=
begin
  cases n,
  { rcases i with ⟨_, ⟨⟩⟩ },
  refine fin.induction _ (λ i ih, _) i,
  { simp },
  { rw [cycle_range_succ, monoid_hom.map_mul, ih, perm.sign_swap],
    { simp [pow_succ] },
    exact i.succ_pos.ne },
end

end fin

end cycle_range
