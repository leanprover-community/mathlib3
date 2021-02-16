/-
Copyright (c) 2018 Kenny Lau. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kenny Lau
-/
import data.fin
import data.equiv.basic

/-!
# Equivalences for `fin n`
-/

universe variables u

variables {m n : ℕ}

/-- Equivalence between `fin 0` and `empty`. -/
def fin_zero_equiv : fin 0 ≃ empty :=
⟨fin_zero_elim, empty.elim, assume a, fin_zero_elim a, assume a, empty.elim a⟩

/-- Equivalence between `fin 0` and `pempty`. -/
def fin_zero_equiv' : fin 0 ≃ pempty.{u} :=
equiv.equiv_pempty fin.elim0

/-- Equivalence between `fin 1` and `punit`. -/
def fin_one_equiv : fin 1 ≃ punit :=
⟨λ_, (), λ_, 0, fin.cases rfl (λa, fin_zero_elim a), assume ⟨⟩, rfl⟩

/-- Equivalence between `fin 2` and `bool`. -/
def fin_two_equiv : fin 2 ≃ bool :=
⟨@fin.cases 1 (λ_, bool) ff (λ_, tt),
  λb, cond b 1 0,
  begin
    refine fin.cases _ _, refl,
    refine fin.cases _ _, refl,
    exact λi, fin_zero_elim i
  end,
  assume b, match b with tt := rfl | ff := rfl end⟩

/-- Equivalence between `fin n.succ` and `option (fin n)`.
This is a version of `fin.pred` that produces `option (fin n)` instead of
requiring a proof that the input is not `0`. -/
def fin_succ_equiv (n : ℕ) : fin n.succ ≃ option (fin n) :=
⟨λ x, fin.cases none some x, λ x, option.rec_on x 0 fin.succ,
  λ x, fin.cases rfl (λ i, show (option.rec_on (fin.cases none some (fin.succ i) : option (fin n))
    0 fin.succ : fin n.succ) = _, by rw fin.cases_succ) x,
  by rintro ⟨none | x⟩; [refl, exact fin.cases_succ _]⟩

@[simp] lemma fin_succ_equiv_zero {n : ℕ} :
  (fin_succ_equiv n) 0 = none := rfl

@[simp] lemma fin_succ_equiv_succ {n : ℕ} (m : fin n):
  (fin_succ_equiv n) m.succ = some m := by simp [fin_succ_equiv]

@[simp] lemma fin_succ_equiv_symm_none {n : ℕ} :
  (fin_succ_equiv n).symm none = 0 := rfl

@[simp] lemma fin_succ_equiv_symm_some {n : ℕ} (m : fin n) :
  (fin_succ_equiv n).symm (some m) = m.succ := rfl

/-- An equivalence that removes `i` and maps it to `none`.
This is a version of `fin.pred_above` that produces `option (fin n)` instead of
requiring a proof that the input is not `i`. -/
def fin_succ_equiv' {n : ℕ} (i : fin n.succ) :
  fin n.succ ≃ option (fin n) :=
{ to_fun := λ x, if h : x = i then none else some (i.pred_above x h),
  inv_fun := λ x, x.cases_on' i (fin.succ_above i),
  left_inv := λ x, if h : x = i then by simp [h] else by simp [h, fin.succ_above_ne],
  right_inv := λ x, by { cases x, simp, simp [fin.succ_above_ne], }}
@[simp] lemma fin_succ_equiv'_at {n : ℕ} (i : fin (n + 1)) :
  (fin_succ_equiv' i) i = none := by simp [fin_succ_equiv']

lemma fin_succ_equiv'_below {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : m.cast_succ < i) :
  (fin_succ_equiv' i) m.cast_succ = some m :=
by simp [fin_succ_equiv', ne_of_lt h, fin.pred_above, h]

lemma fin_succ_equiv'_above {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : i < m.succ) :
  (fin_succ_equiv' i) m.succ = some m :=
by simp [fin_succ_equiv', ne_of_gt h, fin.pred_above, not_lt_of_gt h]

@[simp] lemma fin_succ_equiv'_symm_none {n : ℕ} (i : fin (n + 1)) :
  (fin_succ_equiv' i).symm none = i := rfl

lemma fin_succ_equiv_symm'_some_below {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : m.cast_succ < i) :
  (fin_succ_equiv' i).symm (some m) = m.cast_succ :=
by simp [fin_succ_equiv', ne_of_gt h, fin.succ_above, not_le_of_gt h]

lemma fin_succ_equiv_symm'_some_above {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : i < m.succ) :
  (fin_succ_equiv' i).symm (some m) = m.succ :=
begin
  have : ¬ m.cast_succ < i := by simpa [fin.lt_iff_coe_lt_coe, nat.lt_succ_iff] using h,
  simp [fin_succ_equiv', ne_of_lt h, fin.succ_above, not_le_of_lt h, this]
end
/-- The equiv version of `fin.pred_above_zero`. -/
lemma fin_succ_equiv'_zero {n : ℕ} :
  fin_succ_equiv' (0 : fin (n + 1)) = fin_succ_equiv' n :=
begin
  ext1 x,
  simp only [fin_succ_equiv', fin_succ_equiv, equiv.coe_fn_mk,
             fin.pred_above_zero, fin.succ_above_zero],
  split_ifs,
  { rw h, refl },
  { conv_rhs { rw ←x.succ_pred h },
    rw fin.cases_succ, }
end

/-- Equivalence between `fin m ⊕ fin n` and `fin (m + n)` -/
def sum_fin_sum_equiv : fin m ⊕ fin n ≃ fin (m + n) :=
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

/-- `fin 0` is a subsingleton. -/
instance subsingleton_fin_zero : subsingleton (fin 0) :=
fin_zero_equiv.subsingleton

/-- `fin 1` is a subsingleton. -/
instance subsingleton_fin_one : subsingleton (fin 1) :=
fin_one_equiv.subsingleton
