/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import linear_algebra.matrix.determinant
import linear_algebra.matrix.trace
import tactic.field_simp

/-
# Transvections

Operations on lines and columns

-/

universes u₁ u₂


@[simp] lemma option.to_list_some {α : Type*} (a : α) :
  (a : option α).to_list = [a] :=
rfl

@[simp] lemma option.to_list_none (α : Type*) : (none : option α).to_list = [] :=
rfl


namespace matrix
open_locale matrix

variables (n p q l : Type*) (R : Type u₂)
variables [fintype n] [fintype l] [fintype p] [fintype q]
variables [decidable_eq n] [decidable_eq p] [decidable_eq q] [decidable_eq l]
variables [comm_ring R]

section elementary_basis

variables {n} (i j : n)

/-- It is useful to define these matrices for explicit calculations in sl n R. -/
@[reducible] definition E : matrix n n R := λ i' j', if i = i' ∧ j = j' then 1 else 0

@[simp] lemma E_apply_one : E R i j i j = 1 := if_pos (and.intro rfl rfl)

@[simp] lemma E_apply_zero (i' j' : n) (h : ¬(i = i' ∧ j = j')) : E R i j i' j' = 0 := if_neg h

@[simp] lemma E_diag_zero (h : j ≠ i) : matrix.diag n R R (E R i j) = 0 :=
funext $ λ k, if_neg $ λ ⟨e₁, e₂⟩, h (e₂.trans e₁.symm)

lemma E_trace_zero (h : j ≠ i) : matrix.trace n R R (E R i j) = 0 := by simp [h]

@[simp] lemma E_mul_apply (b : n) (M : matrix n n R) :
  (E R i j ⬝ M) i b = M j b :=
by simp [matrix.mul_apply]

@[simp] lemma mul_E_apply (a : n) (M : matrix n n R) :
  (M ⬝ E R i j) a j = M a i :=
by simp [matrix.mul_apply]

@[simp] lemma E_mul_apply_of_ne (a b : n) (h : a ≠ i) (M : matrix n n R) :
  (E R i j ⬝ M) a b = 0 :=
by simp [matrix.mul_apply, h.symm]

@[simp] lemma mul_E_apply_of_ne (a b : n) (hbj : b ≠ j) (M : matrix n n R) :
  (M ⬝ E R i j) a b = 0 :=
by simp [matrix.mul_apply, hbj.symm]

@[simp] lemma E_mul_E (k : n) : E R i j ⬝ E R j k = E R i k :=
begin
  ext a b,
  simp only [matrix.mul_apply, boole_mul],
  by_cases h₁ : i = a; by_cases h₂ : k = b;
  simp [h₁, h₂],
end

@[simp] lemma E_mul_E_of_ne {k l : n} (h : j ≠ k) : E R i j ⬝ E R k l = 0 :=
begin
  ext a b,
  simp only [matrix.mul_apply, dmatrix.zero_apply, boole_mul],
  by_cases h₁ : i = a;
  simp [h₁, h, h.symm],
end

end elementary_basis

section transvection
variables {R n} (i j : n)

def transvection (c : R) : matrix n n R := 1 + c • E R i j

lemma transvection_mul_transvection (h : i ≠ j) (c d : R) :
  transvection i j c ⬝ transvection i j d = transvection i j (c + d) :=
by simp [transvection, matrix.add_mul, matrix.mul_add, h, h.symm, add_smul, add_assoc]

@[simp] lemma transvection_mul_apply (b : n) (c : R) (M : matrix n n R) :
  (transvection i j c ⬝ M) i b = M i b + c * M j b :=
by simp [transvection, matrix.add_mul]

@[simp] lemma mul_transvection_apply (a : n) (c : R) (M : matrix n n R) :
  (M ⬝ transvection i j c) a j = M a j + c * M a i :=
by simp [transvection, matrix.mul_add]

@[simp] lemma transvection_mul_apply_of_ne (a b : n) (ha : a ≠ i) (c : R) (M : matrix n n R) :
  (transvection i j c ⬝ M) a b = M a b :=
by simp [transvection, matrix.add_mul, ha]

@[simp] lemma mul_transvection_apply_of_ne (a b : n) (hb : b ≠ j) (c : R) (M : matrix n n R) :
  (M ⬝ transvection i j c) a b = M a b :=
by simp [transvection, matrix.mul_add, hb]

end transvection

section pivot

variables {R} {𝕜 : Type* } [field 𝕜] {r : ℕ} (M : matrix (fin r.succ) (fin r.succ) 𝕜)

open fin

def is_last_diag (M : matrix (fin r.succ) (fin r.succ) R) :=
∀ (i : fin r), (M (cast_succ i) (last r) = 0 ∧ M (last r) (cast_succ i) = 0)

def Lcol : list (matrix (fin r.succ) (fin r.succ) 𝕜) :=
list.of_fn $ λ i : fin r, transvection (cast_succ i) (last r) $
  -M (cast_succ i) (last r) / M (last r) (last r)

def Lrow : list (matrix (fin r.succ) (fin r.succ) 𝕜) :=
list.of_fn $ λ i : fin r, transvection (last r) (cast_succ i) $
  -M (last r) (cast_succ i) / M (last r) (last r)

lemma Lcol_mul_last_row_drop (i : fin r.succ) {k : ℕ} (hk : k ≤ r) :
  (((Lcol M).drop k).prod ⬝ M) (last r) i = M (last r) i :=
begin
  apply nat.decreasing_induction' _ hk,
  { simp only [Lcol, list.length_of_fn, matrix.one_mul, list.drop_eq_nil_of_le, list.prod_nil], },
  { assume n hn hk IH,
    have hn' : n < (Lcol M).length, by simpa [Lcol] using hn,
    rw ← list.cons_nth_le_drop_succ hn',
    have D : last r ≠ ⟨n, hn.step⟩ := ne_of_gt hn,
    simpa [Lcol, matrix.mul_assoc, D] }
end

lemma Lcol_mul_last_row (i : fin r.succ) : ((Lcol M).prod ⬝ M) (last r) i = M (last r) i :=
by simpa using Lcol_mul_last_row_drop M i (zero_le _)

lemma mul_Lrow_last_col_take (i : fin r.succ) {k : ℕ} (hk : k ≤ r) :
  (M ⬝ ((Lrow M).take k).prod) i (last r) = M i (last r) :=
begin
  induction k with k IH,
  { simp only [matrix.mul_one, list.take_zero, list.prod_nil], },
  { have hkr : k < r := hk,
    have D : last r ≠ ⟨k, hkr.step⟩ := ne_of_gt hk,
    have : (Lrow M).nth k = transvection (last r) ⟨k, hkr.step⟩ (
      -M (last r) ⟨k, hkr.step⟩ / M (last r) (last r)),
    { simp only [Lrow, list.of_fn_nth_val, hkr, dif_pos, cast_succ_mk, list.nth_of_fn], refl },
    simp only [list.take_succ, ← matrix.mul_assoc, this, list.prod_append, matrix.mul_one,
      matrix.mul_eq_mul, list.prod_cons, list.prod_nil, option.to_list_some],
    rwa [mul_transvection_apply_of_ne, IH hkr.le] }
end

lemma mul_Lrow_last_col (i : fin r.succ) :
  (M ⬝ (Lrow M).prod) i (last r) = M i (last r) :=
begin
  have A : (Lrow M).length = r, by simp [Lrow],
  rw [← list.take_length (Lrow M), A],
  simpa using mul_Lrow_last_col_take M i le_rfl,
end

lemma Lcol_mul_last_col (hM : M (last r) (last r) ≠ 0) (i : fin r) :
  ((Lcol M).prod ⬝ M) (cast_succ i) (last r) = 0 :=
begin
  suffices H : ∀ (k : ℕ), k ≤ r → (((Lcol M).drop k).prod ⬝ M) (cast_succ i) (last r) =
    if k ≤ i then 0 else M (cast_succ i) (last r),
      by simpa only [if_true, list.drop.equations._eqn_1] using H 0 (zero_le _),
  assume k hk,
  apply nat.decreasing_induction' _ hk,
  { simp only [Lcol, list.length_of_fn, matrix.one_mul, list.drop_eq_nil_of_le, list.prod_nil],
    rw if_neg,
    simpa only [not_le] using i.2 },
  { assume n hn hk IH,
    have hn' : n < (Lcol M).length, by simpa [Lcol] using hn,
    rw ← list.cons_nth_le_drop_succ hn',
    have A : (Lcol M).nth_le n hn' = transvection ⟨n, hn.step⟩ (last r)
      (-M ⟨n, hn.step⟩ (last r) / M (last r) (last r)), by simp [Lcol],
    simp only [matrix.mul_assoc, A, matrix.mul_eq_mul, list.prod_cons],
    by_cases h : cast_succ i = ⟨n, hn.step⟩,
    { have hni : n = i,
      { cases i, simp only [subtype.mk_eq_mk, cast_succ_mk] at h, simp [h] },
      rw [h] at ⊢ IH,
      rw [transvection_mul_apply, IH, Lcol_mul_last_row_drop _ _ hn, ← hni],
      field_simp [hM] },
    { have hni : n ≠ i,
      { rintros rfl, cases i, simpa using h },
      simp only [h, transvection_mul_apply_of_ne, ne.def, not_false_iff],
      rw IH,
      rcases le_or_lt (n+1) i with hi|hi,
      { simp only [hi, n.le_succ.trans hi, if_true] },
      { rw [if_neg, if_neg],
        { simpa only [hni.symm, not_le, or_false] using nat.lt_succ_iff_lt_or_eq.1 hi },
        { simpa only [not_le] using hi } } } }
end

lemma mul_Lrow_last_row (hM : M (last r) (last r) ≠ 0) (i : fin r) :
  (M ⬝ (Lrow M).prod) (last r) (cast_succ i) = 0 :=
begin
  suffices H : ∀ (k : ℕ), k ≤ r → (M ⬝ ((Lrow M).take k).prod) (last r) (cast_succ i) =
    if k ≤ i then M (last r) (cast_succ i) else 0,
  { have A : (Lrow M).length = r, by simp [Lrow],
    rw [← list.take_length (Lrow M), A],
    have : ¬ (r ≤ i), by simpa using i.2,
    simpa only [this, ite_eq_right_iff] using H r le_rfl },
  assume k hk,
  induction k with n IH,
  { simp only [if_true, matrix.mul_one, list.take_zero, zero_le', list.prod_nil] },
  { have hnr : n < r := hk,
    have D : last r ≠ ⟨n, hnr.step⟩ := ne_of_gt hk,
    have A : (Lrow M).nth n = transvection (last r) ⟨n, hnr.step⟩
      (-M (last r) ⟨n, hnr.step⟩ / M (last r) (last r)),
    { simp only [Lrow, list.of_fn_nth_val, hnr, dif_pos, cast_succ_mk, list.nth_of_fn], refl },
    simp only [list.take_succ, A, ← matrix.mul_assoc, list.prod_append, matrix.mul_one,
      matrix.mul_eq_mul, list.prod_cons, list.prod_nil, option.to_list_some],
    by_cases h : cast_succ i = ⟨n, hnr.step⟩,
    { have hni : n = i,
      { cases i, simp only [subtype.mk_eq_mk, cast_succ_mk] at h, simp only [h, coe_mk] },
      have : ¬ (n.succ ≤ i), by simp only [← hni, n.lt_succ_self, not_le],
      simp only [←h, mul_transvection_apply, list.take, mul_Lrow_last_col_take _ _ hnr.le,
        IH hnr.le, hni.le, this, mul_transvection_apply, if_true, list.take, if_false],
      field_simp [hM] },
    { have hni : n ≠ i,
      { rintros rfl, cases i, simpa using h },
      simp only [h, IH hnr.le, ne.def, mul_transvection_apply_of_ne, not_false_iff],
      rcases le_or_lt (n+1) i with hi|hi,
      { simp only [hi, n.le_succ.trans hi, if_true] },
      { rw [if_neg, if_neg],
        { simpa only [not_le] using hi },
        { simpa only [hni.symm, not_le, or_false] using nat.lt_succ_iff_lt_or_eq.1 hi } } } }
end

lemma Lcol_mul_Lrow_last_col (hM : M (last r) (last r) ≠ 0) (i : fin r) :
  ((Lcol M).prod ⬝ M ⬝ (Lrow M).prod) (last r) (cast_succ i) = 0 :=
begin
  have : Lrow M = Lrow ((Lcol M).prod ⬝ M), by simp [Lrow, Lcol_mul_last_row],
  rw this,
  apply mul_Lrow_last_row,
  simpa [Lcol_mul_last_row] using hM
end

lemma Lcol_mul_Lrow_last_row (hM : M (last r) (last r) ≠ 0) (i : fin r) :
  ((Lcol M).prod ⬝ M ⬝ (Lrow M).prod) (cast_succ i) (last r) = 0 :=
begin
  have : Lcol M = Lcol (M ⬝ (Lrow M).prod), by simp [Lcol, mul_Lrow_last_col],
  rw [this, matrix.mul_assoc],
  apply Lcol_mul_last_col,
  simpa [mul_Lrow_last_col] using hM
end

lemma is_last_diag_Lcol_mul_Lrow (hM : M (last r) (last r) ≠ 0) :
  is_last_diag ((Lcol M).prod ⬝ M ⬝ (Lrow M).prod) :=
λ i, ⟨Lcol_mul_Lrow_last_row M hM i, Lcol_mul_Lrow_last_col M hM i⟩

lemma exists_is_last_diag_transvec_self_transvec (M : matrix (fin r.succ) (fin r.succ) R) :
  ∃ (L L' : list (matrix (fin r.succ) (fin r.succ) R)),
  is_last_diag (L.prod ⬝ M ⬝ L'.prod) :=
begin
  by_cases H : is_last_diag M, { refine ⟨list.nil, list.nil, by simpa using H⟩ },
  by_cases h : ∃ (i : fin r.succ), (i : ℕ) < r ∧ M i (fin.last r) ≠ 0,
  { rcases h with ⟨i, i_lt, hi⟩,

  }
end

end pivot

end matrix
