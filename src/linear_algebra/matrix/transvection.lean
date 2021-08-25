/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import linear_algebra.matrix.determinant
import linear_algebra.matrix.trace
import linear_algebra.matrix.reindex
import tactic.field_simp

/-!
# Transvections

Operations on lines and columns

-/

universes u₁ u₂

section
/- For another file -/

variables {l m n o : Type*} [fintype l] [fintype m] [fintype n] [fintype o]
variables {m' : o → Type*} [∀ i, fintype (m' i)]
variables {n' : o → Type*} [∀ i, fintype (n' i)]
variables {R : Type*} {S : Type*} {α : Type*} {β : Type*}

open_locale matrix

namespace matrix

section block_matrices

variable [has_zero α]

/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
def is_two_block_diagonal (A : matrix (n ⊕ o) (l ⊕ m) α) : Prop :=
to_blocks₁₂ A = 0 ∧ to_blocks₂₁ A = 0

end block_matrices

end matrix

end

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

variables (R n)

structure transvection_struct :=
(i j : n)
(hij : i ≠ j)
(c : R)

variables {R n}

def transvection_struct.to_matrix (t : transvection_struct n R) : matrix n n R :=
transvection t.i t.j t.c

@[simp] lemma transvection_struct.to_matrix_mk (i j : n) (hij : i ≠ j) (c : R) :
  transvection_struct.to_matrix ⟨i, j, hij, c⟩ = transvection i j c := rfl

variable (p)

open sum

def transvection_struct.sum_inl (t : transvection_struct n R) : transvection_struct (n ⊕ p) R :=
{ i := inl t.i,
  j := inl t.j,
  hij := by simp [t.hij],
  c := t.c }

lemma transvection_struct.to_matrix_sum_inl (t : transvection_struct n R) :
  (t.sum_inl p).to_matrix = from_blocks t.to_matrix 0 0 1 :=
begin
  cases t,
  ext a b,
  cases a; cases b,
  { by_cases h : a = b;
    simp [transvection_struct.sum_inl, transvection, h] },
  { simp [transvection_struct.sum_inl, transvection] },
  { simp [transvection_struct.sum_inl, transvection] },
  { by_cases h : a = b;
    simp [transvection_struct.sum_inl, transvection, h] },
end

end transvection

section pivot

variables {R} {𝕜 : Type*} [field 𝕜] {r : ℕ} (M : matrix ((fin r) ⊕ unit) ((fin r) ⊕ unit) 𝕜)

open sum unit fin transvection_struct

def Lcol : list (matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜) :=
list.of_fn $ λ i : fin r, transvection (inl i) (inr star) $
  -M (inl i) (inr star) / M (inr star) (inr star)

def Lrow : list (matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜) :=
list.of_fn $ λ i : fin r, transvection (inr star) (inl i) $
  -M (inr star) (inl i) / M (inr star) (inr star)

lemma Lcol_mul_last_row_drop (i : fin r ⊕ unit) {k : ℕ} (hk : k ≤ r) :
  (((Lcol M).drop k).prod ⬝ M) (inr star) i = M (inr star) i :=
begin
  apply nat.decreasing_induction' _ hk,
  { simp only [Lcol, list.length_of_fn, matrix.one_mul, list.drop_eq_nil_of_le, list.prod_nil], },
  { assume n hn hk IH,
    have hn' : n < (Lcol M).length, by simpa [Lcol] using hn,
    rw ← list.cons_nth_le_drop_succ hn',
    simpa [Lcol, matrix.mul_assoc] }
end

lemma Lcol_mul_last_row (i : fin r ⊕ unit) : ((Lcol M).prod ⬝ M) (inr star) i = M (inr star) i :=
by simpa using Lcol_mul_last_row_drop M i (zero_le _)

lemma mul_Lrow_last_col_take (i : fin r ⊕ unit) {k : ℕ} (hk : k ≤ r) :
  (M ⬝ ((Lrow M).take k).prod) i (inr star) = M i (inr star) :=
begin
  induction k with k IH,
  { simp only [matrix.mul_one, list.take_zero, list.prod_nil], },
  { have hkr : k < r := hk,
    let k' : fin r := ⟨k, hkr⟩,
    have : (Lrow M).nth k = ↑(transvection (inr unit.star) (inl k')
      (-M (inr unit.star) (inl k') / M (inr unit.star) (inr unit.star))),
    { simp only [Lrow, list.of_fn_nth_val, hkr, dif_pos, list.nth_of_fn], refl },
    simp only [list.take_succ, ← matrix.mul_assoc, this, list.prod_append, matrix.mul_one,
      matrix.mul_eq_mul, list.prod_cons, list.prod_nil, option.to_list_some],
    rw [mul_transvection_apply_of_ne, IH hkr.le],
    simp only [ne.def, not_false_iff], }
end

lemma mul_Lrow_last_col (i : fin r ⊕ unit) :
  (M ⬝ (Lrow M).prod) i (inr star) = M i (inr star) :=
begin
  have A : (Lrow M).length = r, by simp [Lrow],
  rw [← list.take_length (Lrow M), A],
  simpa using mul_Lrow_last_col_take M i le_rfl,
end

lemma Lcol_mul_last_col (hM : M (inr star) (inr star) ≠ 0) (i : fin r) :
  ((Lcol M).prod ⬝ M) (inl i) (inr star) = 0 :=
begin
  suffices H : ∀ (k : ℕ), k ≤ r → (((Lcol M).drop k).prod ⬝ M) (inl i) (inr star) =
    if k ≤ i then 0 else M (inl i) (inr star),
      by simpa only [if_true, list.drop.equations._eqn_1] using H 0 (zero_le _),
  assume k hk,
  apply nat.decreasing_induction' _ hk,
  { simp only [Lcol, list.length_of_fn, matrix.one_mul, list.drop_eq_nil_of_le, list.prod_nil],
    rw if_neg,
    simpa only [not_le] using i.2 },
  { assume n hn hk IH,
    have hn' : n < (Lcol M).length, by simpa [Lcol] using hn,
    let n' : fin r := ⟨n, hn⟩,
    rw ← list.cons_nth_le_drop_succ hn',
    have A : (Lcol M).nth_le n hn' = transvection (inl n') (inr star)
      (-M (inl n') (inr star) / M (inr star) (inr star)), by simp [Lcol],
    simp only [matrix.mul_assoc, A, matrix.mul_eq_mul, list.prod_cons],
    by_cases h : n' = i,
    { have hni : n = i,
      { cases i, simp only [subtype.mk_eq_mk] at h, simp [h] },
      rw [h, transvection_mul_apply, IH, Lcol_mul_last_row_drop _ _ hn, ← hni],
      field_simp [hM] },
    { have hni : n ≠ i,
      { rintros rfl, cases i, simpa using h },
      simp only [transvection_mul_apply_of_ne, ne.def, not_false_iff, ne.symm h],
      rw IH,
      rcases le_or_lt (n+1) i with hi|hi,
      { simp only [hi, n.le_succ.trans hi, if_true] },
      { rw [if_neg, if_neg],
        { simpa only [hni.symm, not_le, or_false] using nat.lt_succ_iff_lt_or_eq.1 hi },
        { simpa only [not_le] using hi } } } }
end

lemma mul_Lrow_last_row (hM : M (inr star) (inr star) ≠ 0) (i : fin r) :
  (M ⬝ (Lrow M).prod) (inr star) (inl i) = 0 :=
begin
  suffices H : ∀ (k : ℕ), k ≤ r → (M ⬝ ((Lrow M).take k).prod) (inr star) (inl i) =
    if k ≤ i then M (inr star) (inl i) else 0,
  { have A : (Lrow M).length = r, by simp [Lrow],
    rw [← list.take_length (Lrow M), A],
    have : ¬ (r ≤ i), by simpa using i.2,
    simpa only [this, ite_eq_right_iff] using H r le_rfl },
  assume k hk,
  induction k with n IH,
  { simp only [if_true, matrix.mul_one, list.take_zero, zero_le', list.prod_nil] },
  { have hnr : n < r := hk,
    let n' : fin r := ⟨n, hnr⟩,
    have A : (Lrow M).nth n = ↑(transvection (inr unit.star) (inl n')
      (-M (inr unit.star) (inl n') / M (inr unit.star) (inr unit.star))),
    { simp only [Lrow, list.of_fn_nth_val, hnr, dif_pos, list.nth_of_fn], refl },
    simp only [list.take_succ, A, ← matrix.mul_assoc, list.prod_append, matrix.mul_one,
      matrix.mul_eq_mul, list.prod_cons, list.prod_nil, option.to_list_some],
    by_cases h : n' = i,
    { have hni : n = i,
      { cases i, simp only [subtype.mk_eq_mk] at h, simp only [h, coe_mk] },
      have : ¬ (n.succ ≤ i), by simp only [← hni, n.lt_succ_self, not_le],
      simp only [h, mul_transvection_apply, list.take, mul_Lrow_last_col_take _ _ hnr.le, hni.le,
        this, if_true, if_false, mul_transvection_apply, IH hnr.le],
      field_simp [hM] },
    { have hni : n ≠ i,
      { rintros rfl, cases i, simpa using h },
      simp only [IH hnr.le, ne.def, mul_transvection_apply_of_ne, not_false_iff, ne.symm h],
      rcases le_or_lt (n+1) i with hi|hi,
      { simp [hi, n.le_succ.trans hi, if_true], },
      { rw [if_neg, if_neg],
        { simpa only [not_le] using hi },
        { simpa only [hni.symm, not_le, or_false] using nat.lt_succ_iff_lt_or_eq.1 hi } } } }
end

lemma Lcol_mul_Lrow_last_col (hM : M (inr star) (inr star) ≠ 0) (i : fin r) :
  ((Lcol M).prod ⬝ M ⬝ (Lrow M).prod) (inr star) (inl i) = 0 :=
begin
  have : Lrow M = Lrow ((Lcol M).prod ⬝ M), by simp [Lrow, Lcol_mul_last_row],
  rw this,
  apply mul_Lrow_last_row,
  simpa [Lcol_mul_last_row] using hM
end

lemma Lcol_mul_Lrow_last_row (hM : M (inr star) (inr star) ≠ 0) (i : fin r) :
  ((Lcol M).prod ⬝ M ⬝ (Lrow M).prod) (inl i) (inr star) = 0 :=
begin
  have : Lcol M = Lcol (M ⬝ (Lrow M).prod), by simp [Lcol, mul_Lrow_last_col],
  rw [this, matrix.mul_assoc],
  apply Lcol_mul_last_col,
  simpa [mul_Lrow_last_col] using hM
end

lemma is_two_block_diagonal_Lcol_mul_Lrow (hM : M (inr star) (inr star) ≠ 0) :
  is_two_block_diagonal ((Lcol M).prod ⬝ M ⬝ (Lrow M).prod) :=
begin
  split,
  { ext i j,
    have : j = star, by simp only [eq_iff_true_of_subsingleton],
    simp [to_blocks₁₂, this, Lcol_mul_Lrow_last_row M hM] },
  { ext i j,
    have : i = star, by simp only [eq_iff_true_of_subsingleton],
    simp [to_blocks₂₁, this, Lcol_mul_Lrow_last_col M hM] },
end

lemma exists_is_two_block_diagonal_of_ne_zero (hM : M (inr star) (inr star) ≠ 0) :
  ∃ (L L' : list (transvection_struct (fin r ⊕ unit) 𝕜)),
  is_two_block_diagonal ((L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod) :=
begin
  let L : list (transvection_struct (fin r ⊕ unit) 𝕜) :=
    list.of_fn (λ i : fin r, ⟨inl i, inr star, by simp,
      -M (inl i) (inr star) / M (inr star) (inr star)⟩),
  let L' : list (transvection_struct (fin r ⊕ unit) 𝕜) :=
    list.of_fn (λ i : fin r, ⟨inr star, inl i, by simp,
      -M (inr star) (inl i)  / M (inr star) (inr star)⟩),
  refine ⟨L, L', _⟩,
  have A : L.map to_matrix = Lcol M, by simp [L, Lcol, (∘)],
  have B : L'.map to_matrix = Lrow M, by simp [L, Lrow, (∘)],
  rw [A, B],
  exact is_two_block_diagonal_Lcol_mul_Lrow M hM
end

lemma exists_is_two_block_diagonal_transvec_mul_mul_transvec
  (M : matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜) :
  ∃ (L L' : list (transvection_struct (fin r ⊕ unit) 𝕜)),
  is_two_block_diagonal ((L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod) :=
begin
  by_cases H : is_two_block_diagonal M, { refine ⟨list.nil, list.nil, by simpa using H⟩ },
  by_cases hM : M (inr star) (inr star) ≠ 0,
  { exact exists_is_two_block_diagonal_of_ne_zero M hM },
  push_neg at hM,
  simp [not_and_distrib, is_two_block_diagonal, to_blocks₁₂, to_blocks₂₁] at H,
  have : ∃ (i : fin r), M (inl i) (inr star) ≠ 0 ∨ M (inr star) (inl i) ≠ 0,
  { cases H,
    { contrapose! H,
      ext i j,
      convert (H i).1,
      simp only [eq_iff_true_of_subsingleton] },
    { contrapose! H,
      ext i j,
      convert (H j).2,
      simp only [eq_iff_true_of_subsingleton] } },
  rcases this with ⟨i, h|h⟩,
  { let M' := transvection (inr unit.star) (inl i) 1 ⬝ M,
    have hM' : M' (inr star) (inr star) ≠ 0, by simpa [M', hM],
    rcases exists_is_two_block_diagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩,
    rw matrix.mul_assoc at hLL',
    refine ⟨L ++ [⟨inr star, inl i, by simp, 1⟩], L', _⟩,
    simp only [list.map_append, list.prod_append, matrix.mul_one, to_matrix_mk, list.prod_cons,
      list.prod_nil, mul_eq_mul, list.map, matrix.mul_assoc (L.map to_matrix).prod],
    exact hLL' },
  { let M' := M ⬝ transvection (inl i) (inr star) 1,
    have hM' : M' (inr star) (inr star) ≠ 0, by simpa [M', hM],
    rcases exists_is_two_block_diagonal_of_ne_zero M' hM' with ⟨L, L', hLL'⟩,
    refine ⟨L, ⟨inl i, inr star, by simp, 1⟩ :: L', _⟩,
    simp only [←matrix.mul_assoc, to_matrix_mk, list.prod_cons, mul_eq_mul, list.map],
    rw [matrix.mul_assoc (L.map to_matrix).prod],
    exact hLL' }
end

@[simp] lemma sum_inl_to_matrix_prod_mul
  (M : matrix n n 𝕜) (L : list (transvection_struct n 𝕜)) (N : matrix p p 𝕜) :
  (L.map (to_matrix ∘ sum_inl p)).prod ⬝ from_blocks M 0 0 N
  = from_blocks ((L.map to_matrix).prod ⬝ M) 0 0 N :=
begin
  induction L with t L IH,
  { simp },
  { simp [matrix.mul_assoc, IH, to_matrix_sum_inl, from_blocks_multiply], },
end

@[simp] lemma mul_sum_inl_to_matrix_prod
  (M : matrix n n 𝕜) (L : list (transvection_struct n 𝕜)) (N : matrix p p 𝕜) :
  (from_blocks M 0 0 N) ⬝ (L.map (to_matrix ∘ sum_inl p)).prod
  = from_blocks (M ⬝ (L.map to_matrix).prod) 0 0 N :=
begin
  induction L with t L IH generalizing M N,
  { simp },
  { simp [IH, to_matrix_sum_inl, from_blocks_multiply], },
end

private lemma exists_transvec_mul_mul_transvec_diagonal_induction
  (IH : ∀ (M : matrix (fin r) (fin r) 𝕜),
    ∃ (L₀ L₀' : list (transvection_struct (fin r) 𝕜)) (D₀ : (fin r) → 𝕜),
      (L₀.map to_matrix).prod ⬝ M ⬝ (L₀'.map to_matrix).prod = diagonal D₀)
  (M : matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜) :
  ∃ (L L' : list (transvection_struct (fin r ⊕ unit) 𝕜)) (D : fin r ⊕ unit → 𝕜),
    (L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod = diagonal D :=
begin
  rcases exists_is_two_block_diagonal_transvec_mul_mul_transvec M with ⟨L₁, L₁', hM⟩,
  let M' := (L₁.map to_matrix).prod ⬝ M ⬝ (L₁'.map to_matrix).prod,
  let M'' := to_blocks₁₁ M',
  rcases IH M'' with ⟨L₀, L₀', D₀, h₀⟩,
  set c := M' (inr star) (inr star) with hc,
  refine ⟨L₀.map (sum_inl unit) ++ L₁, L₁' ++ L₀'.map (sum_inl unit),
    sum.elim D₀ (λ _, M' (inr star) (inr star)), _⟩,
  suffices :
    (L₀.map (to_matrix ∘ sum_inl unit)).prod ⬝ M' ⬝ (L₀'.map (to_matrix ∘ sum_inl unit)).prod =
      diagonal (sum.elim D₀ (λ _, c)), by simpa [M', matrix.mul_assoc, c],
  have : M' = from_blocks M'' 0 0 (diagonal (λ _, c)),
  { rw ← from_blocks_to_blocks M',
    congr,
    { exact hM.1 },
    { exact hM.2 },
    { ext i j,  rw [hc, to_blocks₂₂], congr } },
  rw this,
  simp [h₀],
end

variables {n p}

lemma reindex_list_transvection (M : matrix p p 𝕜) (e : p ≃ n)
  (H : ∃ (L L' : list (transvection_struct n 𝕜)) (D : n → 𝕜),
    (L.map to_matrix).prod ⬝ (matrix.reindex_alg_equiv 𝕜 e M) ⬝ (L'.map to_matrix).prod
      = diagonal D) :
  ∃ (L L' : list (transvection_struct p 𝕜)) (D : p → 𝕜),
    (L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod = diagonal D :=
begin
  rcases H with ⟨L₀, L₀', D₀, h₀⟩,
  sorry,
end

private lemma exists_transvec_mul_mul_transvec_diagonal_Type
  (n : Type) [fintype n] [decidable_eq n]
  (M : matrix n n 𝕜) : ∃ (L L' : list (transvection_struct n 𝕜)) (D : n → 𝕜),
  (L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod = diagonal D :=
begin
  unfreezingI { induction hn : fintype.card n with r IH generalizing n M },
  { refine ⟨list.nil, list.nil, λ _, 1, _⟩,
    ext i j,
    rw fintype.card_eq_zero_iff at hn,
    exact hn.elim' i },
  { have e : n ≃ fin r ⊕ unit,
    { refine fintype.equiv_of_card_eq _,
      rw hn,
      convert (@fintype.card_sum (fin r) unit _ _).symm,
      simp },
    apply reindex_list_transvection M e,
    apply exists_transvec_mul_mul_transvec_diagonal_induction  (λ N, IH (fin r) N (by simp)) }
end

theorem exists_transvec_mul_mul_transvec_diagonal
  (M : matrix n n 𝕜) : ∃ (L L' : list (transvection_struct n 𝕜)) (D : n → 𝕜),
  (L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod = diagonal D :=
begin
  have e : n ≃ fin (fintype.card n) := fintype.equiv_of_card_eq (by simp),
  apply reindex_list_transvection M e,
  apply exists_transvec_mul_mul_transvec_diagonal_Type,
end

end pivot

end matrix
