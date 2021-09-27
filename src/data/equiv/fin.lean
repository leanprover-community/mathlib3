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
(fin.cast h).to_equiv

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
def fin_succ_equiv' {n : ℕ} (i : fin (n + 1)) :
  fin (n + 1) ≃ option (fin n) :=
{ to_fun := i.insert_nth none some,
  inv_fun := λ x, x.cases_on' i (fin.succ_above i),
  left_inv := λ x, fin.succ_above_cases i (by simp) (λ j, by simp) x,
  right_inv := λ x, by cases x; dsimp; simp }

@[simp] lemma fin_succ_equiv'_at {n : ℕ} (i : fin (n + 1)) :
  (fin_succ_equiv' i) i = none := by simp [fin_succ_equiv']

@[simp] lemma fin_succ_equiv'_succ_above {n : ℕ} (i : fin (n + 1)) (j : fin n) :
  fin_succ_equiv' i (i.succ_above j) = some j :=
@fin.insert_nth_apply_succ_above n (λ _, option (fin n)) i _ _ _

lemma fin_succ_equiv'_below {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : m.cast_succ < i) :
  (fin_succ_equiv' i) m.cast_succ = some m :=
by rw [← fin.succ_above_below _ _ h, fin_succ_equiv'_succ_above]

lemma fin_succ_equiv'_above {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : i ≤ m.cast_succ) :
  (fin_succ_equiv' i) m.succ = some m :=
by rw [← fin.succ_above_above _ _ h, fin_succ_equiv'_succ_above]

@[simp] lemma fin_succ_equiv'_symm_none {n : ℕ} (i : fin (n + 1)) :
  (fin_succ_equiv' i).symm none = i := rfl

@[simp] lemma fin_succ_equiv'_symm_some {n : ℕ} (i : fin (n + 1)) (j : fin n) :
  (fin_succ_equiv' i).symm (some j) = i.succ_above j :=
rfl

lemma fin_succ_equiv'_symm_some_below {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : m.cast_succ < i) :
  (fin_succ_equiv' i).symm (some m) = m.cast_succ :=
fin.succ_above_below i m h

lemma fin_succ_equiv'_symm_some_above {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : i ≤ m.cast_succ) :
  (fin_succ_equiv' i).symm (some m) = m.succ :=
fin.succ_above_above i m h

lemma fin_succ_equiv'_symm_coe_below {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : m.cast_succ < i) :
  (fin_succ_equiv' i).symm m = m.cast_succ :=
fin_succ_equiv'_symm_some_below h

lemma fin_succ_equiv'_symm_coe_above {n : ℕ} {i : fin (n + 1)} {m : fin n} (h : i ≤ m.cast_succ) :
  (fin_succ_equiv' i).symm m = m.succ :=
fin_succ_equiv'_symm_some_above h

/-- Equivalence between `fin (n + 1)` and `option (fin n)`.
This is a version of `fin.pred` that produces `option (fin n)` instead of
requiring a proof that the input is not `0`. -/
def fin_succ_equiv (n : ℕ) : fin (n + 1) ≃ option (fin n) :=
fin_succ_equiv' 0

@[simp] lemma fin_succ_equiv_zero {n : ℕ} :
  (fin_succ_equiv n) 0 = none :=
by cases n; refl

@[simp] lemma fin_succ_equiv_succ {n : ℕ} (m : fin n):
  (fin_succ_equiv n) m.succ = some m :=
fin_succ_equiv'_above (fin.zero_le _)

@[simp] lemma fin_succ_equiv_symm_none {n : ℕ} :
  (fin_succ_equiv n).symm none = 0 :=
fin_succ_equiv'_symm_none _

@[simp] lemma fin_succ_equiv_symm_some {n : ℕ} (m : fin n) :
  (fin_succ_equiv n).symm (some m) = m.succ :=
congr_fun fin.succ_above_zero m

@[simp] lemma fin_succ_equiv_symm_coe {n : ℕ} (m : fin n) :
  (fin_succ_equiv n).symm m = m.succ :=
fin_succ_equiv_symm_some m

/-- The equiv version of `fin.pred_above_zero`. -/
lemma fin_succ_equiv'_zero {n : ℕ} :
  fin_succ_equiv' (0 : fin (n + 1)) = fin_succ_equiv n := rfl

/-- `equiv` between `fin (n + 1)` and `option (fin n)` sending `fin.last n` to `none` -/
def fin_succ_equiv_last {n : ℕ} : fin (n + 1) ≃ option (fin n) :=
fin_succ_equiv' (fin.last n)

@[simp] lemma fin_succ_equiv_last_cast_succ {n : ℕ} (i : fin n) :
  fin_succ_equiv_last i.cast_succ = some i :=
fin_succ_equiv'_below i.2

@[simp] lemma fin_succ_equiv_last_last {n : ℕ} :
  fin_succ_equiv_last (fin.last n) = none :=
by simp [fin_succ_equiv_last]

@[simp] lemma fin_succ_equiv_last_symm_some {n : ℕ} (i : fin n) :
  fin_succ_equiv_last.symm (some i) = i.cast_succ :=
fin_succ_equiv'_symm_some_below i.2

@[simp] lemma fin_succ_equiv_last_symm_coe {n : ℕ} (i : fin n) :
  fin_succ_equiv_last.symm ↑i = i.cast_succ :=
fin_succ_equiv'_symm_some_below i.2

@[simp] lemma fin_succ_equiv_last_symm_none {n : ℕ}  :
  fin_succ_equiv_last.symm none = fin.last n :=
fin_succ_equiv'_symm_none _

/-- Equivalence between `fin m ⊕ fin n` and `fin (m + n)` -/
def fin_sum_fin_equiv : fin m ⊕ fin n ≃ fin (m + n) :=
{ to_fun := sum.elim (fin.cast_add n) (fin.nat_add m),
  inv_fun := λ i, @fin.add_cases m n (λ _, fin m ⊕ fin n) sum.inl sum.inr i,
  left_inv := λ x, by { cases x with y y; dsimp; simp },
  right_inv := λ x, by refine fin.add_cases (λ i, _) (λ i, _) x; simp }

@[simp] lemma fin_sum_fin_equiv_apply_left (i : fin m) :
  (fin_sum_fin_equiv (sum.inl i) : fin (m + n)) = fin.cast_add n i := rfl

@[simp] lemma fin_sum_fin_equiv_apply_right (i : fin n) :
  (fin_sum_fin_equiv (sum.inr i) : fin (m + n)) = fin.nat_add m i := rfl

@[simp] lemma fin_sum_fin_equiv_symm_apply_cast_add (x : fin m) :
  fin_sum_fin_equiv.symm (fin.cast_add n x) = sum.inl x :=
fin_sum_fin_equiv.symm_apply_apply (sum.inl x)

@[simp] lemma fin_sum_fin_equiv_symm_apply_nat_add (x : fin n) :
  fin_sum_fin_equiv.symm (fin.nat_add m x) = sum.inr x :=
fin_sum_fin_equiv.symm_apply_apply (sum.inr x)

/-- The equivalence between `fin (m + n)` and `fin (n + m)` which rotates by `n`. -/
def fin_add_flip : fin (m + n) ≃ fin (n + m) :=
(fin_sum_fin_equiv.symm.trans (equiv.sum_comm _ _)).trans fin_sum_fin_equiv

@[simp] lemma fin_add_flip_apply_cast_add (k : fin m) (n : ℕ) :
  fin_add_flip (fin.cast_add n k) = fin.nat_add n k :=
by simp [fin_add_flip]

@[simp] lemma fin_add_flip_apply_nat_add (k : fin n) (m : ℕ) :
  fin_add_flip (fin.nat_add m k) = fin.cast_add m k :=
by simp [fin_add_flip]

@[simp] lemma fin_add_flip_apply_mk_left {k : ℕ} (h : k < m)
  (hk : k < m + n := nat.lt_add_right k m n h)
  (hnk : n + k < n + m := add_lt_add_left h n) :
  fin_add_flip (⟨k, hk⟩ : fin (m + n)) = ⟨n + k, hnk⟩ :=
by convert fin_add_flip_apply_cast_add ⟨k, h⟩ n

@[simp] lemma fin_add_flip_apply_mk_right {k : ℕ} (h₁ : m ≤ k) (h₂ : k < m + n) :
  fin_add_flip (⟨k, h₂⟩ : fin (m + n)) = ⟨k - m, sub_le_self'.trans_lt $ add_comm m n ▸ h₂⟩ :=
begin
  convert fin_add_flip_apply_nat_add ⟨k - m, (sub_lt_iff_right h₁).2 _⟩ m,
  { simp [nat.add_sub_cancel' h₁] },
  { rwa add_comm }
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
  rw fin_add_flip_apply_mk_right,
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
