/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kenny Lau
-/
import data.fin
import data.equiv.basic
import tactic.norm_num

/-!
# Equivalences for `fin n`
-/

universe variables u

variables {m n : ℕ}

/-- Equivalence between `fin 0` and `empty`. -/
def fin_zero_equiv : fin 0 ≃ empty :=
equiv.equiv_empty _

/-- Equivalence between `fin 0` and `pempty`. -/
def fin_zero_equiv' : fin 0 ≃ pempty.{u} :=
equiv.equiv_pempty _

/-- Equivalence between `fin 1` and `unit`. -/
def fin_one_equiv : fin 1 ≃ unit :=
equiv_punit_of_unique

/-- Equivalence between `fin 2` and `bool`. -/
def fin_two_equiv : fin 2 ≃ bool :=
⟨@fin.cases 1 (λ_, bool) ff (λ_, tt),
  λb, cond b 1 0,
  begin
    refine fin.cases _ _, by norm_num,
    refine fin.cases _ _, by norm_num,
    exact λi, fin_zero_elim i
  end,
  begin
    rintro ⟨_|_⟩,
    { refl },
    { rw ← fin.succ_zero_eq_one, refl }
  end⟩

/-- The 'identity' equivalence between `fin n` and `fin m` when `n = m`. -/
def fin_congr {n m : ℕ} (h : n = m) : fin n ≃ fin m :=
equiv.subtype_equiv_right (λ x, by subst h)

@[simp] lemma fin_congr_apply_mk {n m : ℕ} (h : n = m) (k : ℕ) (w : k < n) :
  fin_congr h ⟨k, w⟩ = ⟨k, by { subst h, exact w }⟩ :=
rfl

@[simp] lemma fin_congr_symm {n m : ℕ} (h : n = m) :
  (fin_congr h).symm = fin_congr h.symm := rfl

@[simp] lemma fin_congr_apply_coe {n m : ℕ} (h : n = m) (k : fin n) :
  (fin_congr h k : ℕ) = k :=
by { cases k, refl, }

lemma fin_congr_symm_apply_coe {n m : ℕ} (h : n = m) (k : fin m) :
  ((fin_congr h).symm k : ℕ) = k :=
by { cases k, refl, }

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `fin.pred_above` that produces `option (fin n)` instead of
mapping both `i.cast_succ` and `i.succ` to `i`. -/
def fin_succ_equiv' {n : ℕ} (i : fin n) :
  fin (n + 1) ≃ option (fin n) :=
{ to_fun := λ x, if x = i.cast_succ then none else some (i.pred_above x),
  inv_fun := λ x, x.cases_on' i.cast_succ (fin.succ_above i.cast_succ),
  left_inv := λ x, if h : x = i.cast_succ then by simp [h]
                   else by simp [h, fin.succ_above_ne],
  right_inv := λ x, by { cases x; simp [fin.succ_above_ne] }}

@[simp] lemma fin_succ_equiv'_at {n : ℕ} (i : fin (n + 1)) :
  (fin_succ_equiv' i) i.cast_succ = none := by simp [fin_succ_equiv']

lemma fin_succ_equiv'_below {n : ℕ} {i m : fin (n + 1)} (h : m < i) :
  (fin_succ_equiv' i) m.cast_succ = some m :=
begin
  have : m.cast_succ ≤ i.cast_succ := h.le,
  simp [fin_succ_equiv', h.ne, fin.pred_above_below, this]
end

lemma fin_succ_equiv'_above {n : ℕ} {i m : fin (n + 1)} (h : i ≤ m) :
  (fin_succ_equiv' i) m.succ = some m :=
begin
  have : i.cast_succ < m.succ,
    { refine (lt_of_le_of_lt _ m.cast_succ_lt_succ), exact h },
  simp [fin_succ_equiv', this, fin.pred_above_above, ne_of_gt]
end

@[simp] lemma fin_succ_equiv'_symm_none {n : ℕ} (i : fin (n + 1)) :
  (fin_succ_equiv' i).symm none = i.cast_succ := rfl

lemma fin_succ_equiv_symm'_some_below {n : ℕ} {i m : fin (n + 1)} (h : m < i) :
  (fin_succ_equiv' i).symm (some m) = m.cast_succ :=
by simp [fin_succ_equiv', ne_of_gt h, fin.succ_above, not_le_of_gt h]

lemma fin_succ_equiv_symm'_some_above {n : ℕ} {i m : fin (n + 1)} (h : i ≤ m) :
  (fin_succ_equiv' i).symm (some m) = m.succ :=
by simp [fin_succ_equiv', fin.succ_above, h.not_lt]

lemma fin_succ_equiv_symm'_coe_below {n : ℕ} {i m : fin (n + 1)} (h : m < i) :
  (fin_succ_equiv' i).symm m = m.cast_succ :=
by { convert fin_succ_equiv_symm'_some_below h; simp }

lemma fin_succ_equiv_symm'_coe_above {n : ℕ} {i m : fin (n + 1)} (h : i ≤ m) :
  (fin_succ_equiv' i).symm m = m.succ :=
by { convert fin_succ_equiv_symm'_some_above h; simp }

/-- Equivalence between `fin (n + 1)` and `option (fin n)`.
This is a version of `fin.pred` that produces `option (fin n)` instead of
requiring a proof that the input is not `0`. -/
-- TODO: make the `n = 0` case neater
def fin_succ_equiv (n : ℕ) : fin (n + 1) ≃ option (fin n) :=
nat.cases_on n
{ to_fun := λ _, none,
  inv_fun := λ _, 0,
  left_inv := λ _, by simp,
  right_inv := λ x, by { cases x, simp, exact x.elim0 } }
(λ _, fin_succ_equiv' 0)

@[simp] lemma fin_succ_equiv_zero {n : ℕ} :
  (fin_succ_equiv n) 0 = none :=
by cases n; refl

@[simp] lemma fin_succ_equiv_succ {n : ℕ} (m : fin n):
  (fin_succ_equiv n) m.succ = some m :=
begin
  cases n, { exact m.elim0 },
  convert fin_succ_equiv'_above m.zero_le
end

@[simp] lemma fin_succ_equiv_symm_none {n : ℕ} :
  (fin_succ_equiv n).symm none = 0 :=
by cases n; refl

@[simp] lemma fin_succ_equiv_symm_some {n : ℕ} (m : fin n) :
  (fin_succ_equiv n).symm (some m) = m.succ :=
begin
  cases n, { exact m.elim0 },
  convert fin_succ_equiv_symm'_some_above m.zero_le
end

@[simp] lemma fin_succ_equiv_symm_coe {n : ℕ} (m : fin n) :
  (fin_succ_equiv n).symm m = m.succ :=
fin_succ_equiv_symm_some m

/-- The equiv version of `fin.pred_above_zero`. -/
lemma fin_succ_equiv'_zero {n : ℕ} :
  fin_succ_equiv' (0 : fin (n + 1)) = fin_succ_equiv (n + 1) := rfl

/-- Equivalence between `fin m ⊕ fin n` and `fin (m + n)` -/
def fin_sum_fin_equiv : fin m ⊕ fin n ≃ fin (m + n) :=
{ to_fun := λ x, sum.rec_on x
    (λ y, ⟨y.1, nat.lt_of_lt_of_le y.2 $ nat.le_add_right m n⟩)
    (λ y, ⟨m + y.1, nat.add_lt_add_left y.2 m⟩),
  inv_fun := λ x, if H : x.1 < m
    then sum.inl ⟨x.1, H⟩
    else sum.inr ⟨x.1 - m, nat.lt_of_add_lt_add_left $
      show m + (x.1 - m) < m + n,
      from (nat.add_sub_of_le $ le_of_not_gt H).symm ▸ x.2⟩,
  left_inv := λ x, begin
    cases x with y y,
    { simp [fin.ext_iff, y.is_lt], },
    { have H : ¬m + y.val < m := not_lt_of_ge (nat.le_add_right _ _),
      simp [H, nat.add_sub_cancel_left, fin.ext_iff] }
  end,
  right_inv := λ x, begin
    by_cases H : (x:ℕ) < m,
    { dsimp, rw [dif_pos H], simp },
    { dsimp, rw [dif_neg H], simp [fin.ext_iff, nat.add_sub_of_le (le_of_not_gt H)] }
  end }

@[simp] lemma fin_sum_fin_equiv_apply_left (x : fin m) :
  @fin_sum_fin_equiv m n (sum.inl x) = ⟨x.1, nat.lt_of_lt_of_le x.2 $ nat.le_add_right m n⟩ :=
rfl

@[simp] lemma fin_sum_fin_equiv_apply_right (x : fin n) :
  @fin_sum_fin_equiv m n (sum.inr x) = ⟨m + x.1, nat.add_lt_add_left x.2 m⟩ :=
rfl

@[simp] lemma fin_sum_fin_equiv_symm_apply_left (x : fin (m + n)) (h : ↑x < m) :
  fin_sum_fin_equiv.symm x = sum.inl ⟨x.1, h⟩ :=
by simp [fin_sum_fin_equiv, dif_pos h]

@[simp] lemma fin_sum_fin_equiv_symm_apply_right (x : fin (m + n)) (h : m ≤ ↑x) :
  fin_sum_fin_equiv.symm x = sum.inr ⟨x.1 - m, nat.lt_of_add_lt_add_left $
      show m + (x.1 - m) < m + n, from (nat.add_sub_of_le $ h).symm ▸ x.2⟩ :=
by simp [fin_sum_fin_equiv, dif_neg (not_lt.mpr h)]

/-- The equivalence between `fin (m + n)` and `fin (n + m)` which rotates by `n`. -/
def fin_add_flip : fin (m + n) ≃ fin (n + m) :=
(fin_sum_fin_equiv.symm.trans (equiv.sum_comm _ _)).trans fin_sum_fin_equiv

@[simp] lemma fin_add_flip_apply_left {k : ℕ} (h : k < m)
  (hk : k < m + n := nat.lt_add_right k m n h)
  (hnk : n + k < n + m := add_lt_add_left h n) :
  fin_add_flip (⟨k, hk⟩ : fin (m + n)) = ⟨n + k, hnk⟩ :=
begin
  dsimp [fin_add_flip, fin_sum_fin_equiv],
  rw [dif_pos h],
  refl,
end

@[simp] lemma fin_add_flip_apply_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m + n) :
  fin_add_flip (⟨k, h₂⟩ : fin (m + n)) =
    ⟨k - m, lt_of_le_of_lt (nat.sub_le _ _) (by { convert h₂ using 1, simp [add_comm] })⟩ :=
begin
  dsimp [fin_add_flip, fin_sum_fin_equiv],
  rw [dif_neg (not_lt.mpr h₁)],
  refl,
end

/-- Rotate `fin n` one step to the right. -/
def fin_rotate : Π n, equiv.perm (fin n)
| 0 := equiv.refl _
| (n+1) := fin_add_flip.trans (fin_congr (add_comm _ _))

lemma fin_rotate_of_lt {k : ℕ} (h : k < n) :
  fin_rotate (n+1) ⟨k, lt_of_lt_of_le h (nat.le_succ _)⟩ = ⟨k + 1, nat.succ_lt_succ h⟩ :=
begin
  dsimp [fin_rotate],
  simp [h, add_comm],
end

lemma fin_rotate_last' : fin_rotate (n+1) ⟨n, lt_add_one _⟩ = ⟨0, nat.zero_lt_succ _⟩ :=
begin
  dsimp [fin_rotate],
  rw fin_add_flip_apply_right,
  simp,
end

lemma fin_rotate_last : fin_rotate (n+1) (fin.last _) = 0 :=
fin_rotate_last'

lemma fin.snoc_eq_cons_rotate {α : Type*} (v : fin n → α) (a : α) :
  @fin.snoc _ (λ _, α) v a = (λ i, @fin.cons _ (λ _, α) a v (fin_rotate _ i)) :=
begin
  ext ⟨i, h⟩,
  by_cases h' : i < n,
  { rw [fin_rotate_of_lt h', fin.snoc, fin.cons, dif_pos h'],
    refl, },
  { have h'' : n = i,
    { simp only [not_lt] at h', exact (nat.eq_of_le_of_lt_succ h' h).symm, },
    subst h'',
    rw [fin_rotate_last', fin.snoc, fin.cons, dif_neg (lt_irrefl _)],
    refl, }
end

@[simp] lemma fin_rotate_zero : fin_rotate 0 = equiv.refl _ := rfl

@[simp] lemma fin_rotate_one : fin_rotate 1 = equiv.refl _ :=
subsingleton.elim _ _

@[simp] lemma fin_rotate_succ_apply {n : ℕ} (i : fin n.succ) :
  fin_rotate n.succ i = i + 1 :=
begin
  cases n,
  { simp },
  rcases i.le_last.eq_or_lt with rfl|h,
  { simp [fin_rotate_last] },
  { cases i,
    simp only [fin.lt_iff_coe_lt_coe, fin.coe_last, fin.coe_mk] at h,
    simp [fin_rotate_of_lt h, fin.eq_iff_veq, fin.add_def, nat.mod_eq_of_lt (nat.succ_lt_succ h)] },
end

@[simp] lemma fin_rotate_apply_zero {n : ℕ} : fin_rotate n.succ 0 = 1 :=
by rw [fin_rotate_succ_apply, zero_add]

lemma coe_fin_rotate_of_ne_last {n : ℕ} {i : fin n.succ} (h : i ≠ fin.last n) :
  (fin_rotate n.succ i : ℕ) = i + 1 :=
begin
  rw fin_rotate_succ_apply,
  have : (i : ℕ) < n := lt_of_le_of_ne (nat.succ_le_succ_iff.mp i.2) (fin.coe_injective.ne h),
  exact fin.coe_add_one_of_lt this
end

lemma coe_fin_rotate {n : ℕ} (i : fin n.succ) :
  (fin_rotate n.succ i : ℕ) = if i = fin.last n then 0 else i + 1 :=
by rw [fin_rotate_succ_apply, fin.coe_add_one i]

/-- Equivalence between `fin m × fin n` and `fin (m * n)` -/
def fin_prod_fin_equiv : fin m × fin n ≃ fin (m * n) :=
{ to_fun := λ x, ⟨x.2.1 + n * x.1.1,
    calc x.2.1 + n * x.1.1 + 1
        = x.1.1 * n + x.2.1 + 1 : by ac_refl
    ... ≤ x.1.1 * n + n : nat.add_le_add_left x.2.2 _
    ... = (x.1.1 + 1) * n : eq.symm $ nat.succ_mul _ _
    ... ≤ m * n : nat.mul_le_mul_right _ x.1.2⟩,
  inv_fun := λ x,
    have H : 0 < n, from nat.pos_of_ne_zero $ λ H, nat.not_lt_zero x.1 $ by subst H; from x.2,
    (⟨x.1 / n, (nat.div_lt_iff_lt_mul _ _ H).2 x.2⟩,
     ⟨x.1 % n, nat.mod_lt _ H⟩),
  left_inv := λ ⟨x, y⟩,
    have H : 0 < n, from nat.pos_of_ne_zero $ λ H, nat.not_lt_zero y.1 $ H ▸ y.2,
    prod.ext
      (fin.eq_of_veq $ calc
              (y.1 + n * x.1) / n
            = y.1 / n + x.1 : nat.add_mul_div_left _ _ H
        ... = 0 + x.1 : by rw nat.div_eq_of_lt y.2
        ... = x.1 : nat.zero_add x.1)
      (fin.eq_of_veq $ calc
              (y.1 + n * x.1) % n
            = y.1 % n : nat.add_mul_mod_self_left _ _ _
        ... = y.1 : nat.mod_eq_of_lt y.2),
  right_inv := λ x, fin.eq_of_veq $ nat.mod_add_div _ _ }

/-- Promote a `fin n` into a larger `fin m`, as a subtype where the underlying
values are retained. This is the `order_iso` version of `fin.cast_le`. -/
@[simps apply symm_apply]
def fin.cast_le_order_iso {n m : ℕ} (h : n ≤ m) : fin n ≃o {i : fin m // (i : ℕ) < n} :=
{ to_fun := λ i, ⟨fin.cast_le h i, by simpa using i.is_lt⟩,
  inv_fun := λ i, ⟨i, i.prop⟩,
  left_inv := λ _, by simp,
  right_inv := λ _, by simp,
  map_rel_iff' := λ _ _, by simp }

/-- `fin 0` is a subsingleton. -/
instance subsingleton_fin_zero : subsingleton (fin 0) :=
fin_zero_equiv.subsingleton

/-- `fin 1` is a subsingleton. -/
instance subsingleton_fin_one : subsingleton (fin 1) :=
fin_one_equiv.subsingleton
