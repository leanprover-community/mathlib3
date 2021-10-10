/-
Copyright (c) 2021 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import linear_algebra.matrix.determinant
import linear_algebra.matrix.trace
import linear_algebra.matrix.reindex
import tactic.field_simp
import data.matrix.basis

/-!
# Transvections

Transvections are matrices of the form `1 + std_basis_matrix i j c`, where `std_basis_matrix i j c`
is the basic matrix with a `c` at position `(i, j)`. Multiplying by such a transvection on the left
(resp. on the right) amounts to adding `c` times the `j`-th row to to the `i`-th row
(resp `c` times the `i`-th column to the `j`-th column). Therefore, they are useful to present
algorithms operating on rows and columns.

Transvections are a special case of *elementary matrices* (according to most references, these also
contain the matrices exchanging rows, and the matrices multiplying a row by a constant).

We show that, over a field, any matrix can be written as `L ⬝ D ⬝ L'`, where `L` and `L'` are
products of transvections and `D` is diagonal. In other words, one can reduce a matrix to diagonal
form by operations on its rows and columns, a variant of Gauss' pivot algorithm.

## Main definitions and results

* `transvection i j c` is the matrix equal to `1 + std_basis_matrix i j c`.
* `transvection_struct n R` is a structure containing the data of `i, j, c` and a proof that
  `i ≠ j`. These are often easier to manipulate than straight matrices, especially in inductive
  arguments.

* `exists_list_transvec_mul_diagonal_mul_list_transvec` states that any matrix `M` over a field can
  be written in the form `t_1 ⬝ ... ⬝ t_k ⬝ D ⬝ t'_1 ⬝ ... ⬝ t'_l`, where `D` is diagonal and
  the `t_i`, `t'_j` are transvections.

* `diagonal_transvection_induction` shows that a property which is true for diagonal matrices and
  transvections, and invariant under product, is true for all matrices.
* `diagonal_transvection_induction_of_det_ne_zero` is the same statement over invertible matrices.

## Implementation details

The proof of the reduction results is done inductively on the size of the matrices, reducing an
`(r + 1) × (r + 1)` matrix to a matrix whose last row and column are zeroes, except possibly for
the last diagonal entry. This step is done as follows.

If all the coefficients on the last row and column are zero, there is nothing to do. Otherwise,
one can put a nonzero coefficient in the last diagonal entry by a row or column operation, and then
subtract this last diagonal entry from the other entries in the last row and column to make them
vanish.

This step is done in the type `fin r ⊕ unit`, where `fin r` is useful to choose arbitrarily some
order in which we cancel the coefficients, and the sum structure is useful to use the formalism of
block matrices.

To proceed with the induction, we reindex our matrices to reduce to the above situation.
-/

universes u₁ u₂

namespace matrix
open_locale matrix

variables (n p : Type*) (R : Type u₂) {𝕜 : Type*} [field 𝕜]
variables [decidable_eq n] [decidable_eq p]
variables [comm_ring R]

section transvection
variables {R n} (i j : n)

/-- The transvection matrix `transvection i j c` is equal to the identity plus `c` at position
`(i, j)`. Multiplying by it on the left (as in `transvection i j c ⬝ M`) corresponds to adding
`c` times the `j`-th line of `M` to its `i`-th line. Multiplying by it on the right corresponds
to adding `c` times the `i`-th column to the `j`-th column. -/
def transvection (c : R) : matrix n n R := 1 + matrix.std_basis_matrix i j c

@[simp] lemma transvection_zero : transvection i j (0 : R) = 1 :=
by simp [transvection]

section
variable [fintype n]

/-- A transvection matrix is obtained from the identity by adding `c` times the `j`-th row to
the `i`-th row. -/
lemma update_row_eq_transvection (c : R) :
  update_row (1 : matrix n n R) i (((1 : matrix n n R)) i + c • (1 : matrix n n R) j) =
    transvection i j c :=
begin
  ext a b,
  by_cases ha : i = a; by_cases hb : j = b,
  { simp only [update_row, transvection, ha, hb, function.update_same, std_basis_matrix.apply_same,
      pi.add_apply, one_apply_eq, pi.smul_apply, mul_one, algebra.id.smul_eq_mul], },
  { simp only [update_row, transvection, ha, hb, std_basis_matrix.apply_of_ne, function.update_same,
      pi.add_apply, ne.def, not_false_iff, pi.smul_apply, and_false, one_apply_ne,
      algebra.id.smul_eq_mul, mul_zero] },
  { simp only [update_row, transvection, ha, ne.symm ha, std_basis_matrix.apply_of_ne, add_zero,
      algebra.id.smul_eq_mul, function.update_noteq, ne.def, not_false_iff, dmatrix.add_apply,
      pi.smul_apply, mul_zero, false_and] },
  { simp only [update_row, transvection, ha, hb, ne.symm ha, std_basis_matrix.apply_of_ne, add_zero,
      algebra.id.smul_eq_mul, function.update_noteq, ne.def, not_false_iff, and_self,
      dmatrix.add_apply, pi.smul_apply, mul_zero] }
end

lemma transvection_mul_transvection_same (h : i ≠ j) (c d : R) :
  transvection i j c ⬝ transvection i j d = transvection i j (c + d) :=
by simp [transvection, matrix.add_mul, matrix.mul_add, h, h.symm, add_smul, add_assoc,
    std_basis_matrix_add]

@[simp] lemma transvection_mul_apply_same (b : n) (c : R) (M : matrix n n R) :
  (transvection i j c ⬝ M) i b = M i b + c * M j b :=
by simp [transvection, matrix.add_mul]

@[simp] lemma mul_transvection_apply_same (a : n) (c : R) (M : matrix n n R) :
  (M ⬝ transvection i j c) a j = M a j + c * M a i :=
by simp [transvection, matrix.mul_add, mul_comm]

@[simp] lemma transvection_mul_apply_of_ne (a b : n) (ha : a ≠ i) (c : R) (M : matrix n n R) :
  (transvection i j c ⬝ M) a b = M a b :=
by simp [transvection, matrix.add_mul, ha]

@[simp] lemma mul_transvection_apply_of_ne (a b : n) (hb : b ≠ j) (c : R) (M : matrix n n R) :
  (M ⬝ transvection i j c) a b = M a b :=
by simp [transvection, matrix.mul_add, hb]

@[simp] lemma det_transvection_of_ne (h : i ≠ j) (c : R) : det (transvection i j c) = 1 :=
by rw [← update_row_eq_transvection i j, det_update_row_add_smul_self _ h, det_one]

end

variables (R n)

/-- A structure containing all the information from which one can build a nontrivial transvection.
This structure is easier to manipulate than transvections as one has a direct access to all the
relevant fields. -/
@[nolint has_inhabited_instance]
structure transvection_struct :=
(i j : n)
(hij : i ≠ j)
(c : R)

instance [nontrivial n] : nonempty (transvection_struct n R) :=
by { choose x y hxy using exists_pair_ne n, exact ⟨⟨x, y, hxy, 0⟩⟩ }

namespace transvection_struct

variables {R n}

/-- Associating to a `transvection_struct` the corresponding transvection matrix. -/
def to_matrix (t : transvection_struct n R) : matrix n n R :=
transvection t.i t.j t.c

@[simp] lemma to_matrix_mk (i j : n) (hij : i ≠ j) (c : R) :
  transvection_struct.to_matrix ⟨i, j, hij, c⟩ = transvection i j c := rfl

@[simp] protected lemma det [fintype n] (t : transvection_struct n R) : det t.to_matrix = 1 :=
det_transvection_of_ne _ _ t.hij _

@[simp] lemma det_to_matrix_prod [fintype n] (L : list (transvection_struct n 𝕜)) :
  det ((L.map to_matrix).prod) = 1 :=
begin
  induction L with t L IH,
  { simp },
  { simp [IH], }
end

/-- The inverse of a `transvection_struct`, designed so that `t.inv.to_matrix` is the inverse of
`t.to_matrix`. -/
@[simps] protected def inv (t : transvection_struct n R) : transvection_struct n R :=
{ i := t.i,
  j := t.j,
  hij := t.hij,
  c := - t.c }

section
variable [fintype n]

lemma inv_mul (t : transvection_struct n R) :
  t.inv.to_matrix ⬝ t.to_matrix = 1 :=
by { rcases t, simp [to_matrix, transvection_mul_transvection_same, t_hij] }

lemma mul_inv (t : transvection_struct n R) :
  t.to_matrix ⬝ t.inv.to_matrix = 1 :=
by { rcases t, simp [to_matrix, transvection_mul_transvection_same, t_hij] }

lemma reverse_inv_prod_mul_prod (L : list (transvection_struct n R)) :
  (L.reverse.map (to_matrix ∘ transvection_struct.inv)).prod ⬝ (L.map to_matrix).prod = 1 :=
begin
  induction L with t L IH,
  { simp },
  { suffices : (L.reverse.map (to_matrix ∘ transvection_struct.inv)).prod ⬝
      (t.inv.to_matrix ⬝ t.to_matrix) ⬝ (L.map to_matrix).prod = 1, by simpa [matrix.mul_assoc],
    simpa [inv_mul] using IH, }
end

lemma prod_mul_reverse_inv_prod (L : list (transvection_struct n R)) :
  (L.map to_matrix).prod ⬝ (L.reverse.map (to_matrix ∘ transvection_struct.inv)).prod = 1 :=
begin
  induction L with t L IH,
  { simp },
  { suffices : t.to_matrix ⬝ ((L.map to_matrix).prod ⬝
      (L.reverse.map (to_matrix ∘ transvection_struct.inv)).prod) ⬝ t.inv.to_matrix = 1,
        by simpa [matrix.mul_assoc],
    simp_rw [IH, matrix.mul_one, t.mul_inv], }
end

end

variables (p)

open sum

/-- Given a `transvection_struct` on `n`, define the corresponding `transvection_struct` on `n ⊕ p`
using the identity on `p`. -/
def sum_inl (t : transvection_struct n R) : transvection_struct (n ⊕ p) R :=
{ i := inl t.i,
  j := inl t.j,
  hij := by simp [t.hij],
  c := t.c }

lemma to_matrix_sum_inl (t : transvection_struct n R) :
  (t.sum_inl p).to_matrix = from_blocks t.to_matrix 0 0 1 :=
begin
  cases t,
  ext a b,
  cases a; cases b,
  { by_cases h : a = b;
    simp [transvection_struct.sum_inl, transvection, h, std_basis_matrix], },
  { simp [transvection_struct.sum_inl, transvection] },
  { simp [transvection_struct.sum_inl, transvection] },
  { by_cases h : a = b;
    simp [transvection_struct.sum_inl, transvection, h] },
end

@[simp] lemma sum_inl_to_matrix_prod_mul [fintype n] [fintype p]
  (M : matrix n n R) (L : list (transvection_struct n R)) (N : matrix p p R) :
  (L.map (to_matrix ∘ sum_inl p)).prod ⬝ from_blocks M 0 0 N
  = from_blocks ((L.map to_matrix).prod ⬝ M) 0 0 N :=
begin
  induction L with t L IH,
  { simp },
  { simp [matrix.mul_assoc, IH, to_matrix_sum_inl, from_blocks_multiply], },
end

@[simp] lemma mul_sum_inl_to_matrix_prod [fintype n] [fintype p]
  (M : matrix n n R) (L : list (transvection_struct n R)) (N : matrix p p R) :
  (from_blocks M 0 0 N) ⬝ (L.map (to_matrix ∘ sum_inl p)).prod
  = from_blocks (M ⬝ (L.map to_matrix).prod) 0 0 N :=
begin
  induction L with t L IH generalizing M N,
  { simp },
  { simp [IH, to_matrix_sum_inl, from_blocks_multiply], },
end

variable {p}

/-- Given a `transvection_struct` on `n` and an equivalence between `n` and `p`, define the
corresponding `transvection_struct` on `p`. -/
def reindex_equiv (e : n ≃ p) (t : transvection_struct n R) : transvection_struct p R :=
{ i := e t.i,
  j := e t.j,
  hij := by simp [t.hij],
  c := t.c }

variables [fintype n] [fintype p]

lemma to_matrix_reindex_equiv (e : n ≃ p) (t : transvection_struct n R) :
  (t.reindex_equiv e).to_matrix = reindex_alg_equiv R e t.to_matrix :=
begin
  cases t,
  ext a b,
  simp only [reindex_equiv, transvection, mul_boole, algebra.id.smul_eq_mul, to_matrix_mk,
    minor_apply, reindex_apply, dmatrix.add_apply, pi.smul_apply, reindex_alg_equiv_apply],
  by_cases ha : e t_i = a; by_cases hb : e t_j = b; by_cases hab : a = b;
  simp [ha, hb, hab, ← e.apply_eq_iff_eq_symm_apply, std_basis_matrix]
end

lemma to_matrix_reindex_equiv_prod (e : n ≃ p) (L : list (transvection_struct n R)) :
  (L.map (to_matrix ∘ (reindex_equiv e))).prod = reindex_alg_equiv R e (L.map to_matrix).prod :=
begin
  induction L with t L IH,
  { simp },
  { simp only [to_matrix_reindex_equiv, IH, function.comp_app, list.prod_cons, mul_eq_mul,
      reindex_alg_equiv_apply, list.map],
    exact (reindex_alg_equiv_mul _ _ _ _).symm }
end

end transvection_struct

end transvection

/-!
# Reducing matrices by left and right multiplication by transvections

In this section, we show that any matrix can be reduced to diagonal form by left and right
multiplication by transvections (or, equivalently, by elementary operations on lines and columns).
The main step is to kill the last row and column of a matrix in `fin r ⊕ unit` with nonzero last
coefficient, by subtracting this coefficient from the other ones. The list of these operations is
recorded in `list_transvec_col M` and `list_transvec_row M`. We have to analyze inductively how
these operations affect the coefficients in the last row and the last column to conclude that they
have the desired effect.

Once this is done, one concludes the reduction by induction on the size
of the matrices, through a suitable reindexing to identify any fintype with `fin r ⊕ unit`.
-/

namespace pivot

variables {R} {r : ℕ} (M : matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜)

open sum unit fin transvection_struct

/-- A list of transvections such that multiplying on the left with these transvections will replace
the last column with zeroes. -/
def list_transvec_col : list (matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜) :=
list.of_fn $ λ i : fin r, transvection (inl i) (inr star) $
  -M (inl i) (inr star) / M (inr star) (inr star)

/-- A list of transvections such that multiplying on the right with these transvections will replace
the last row with zeroes. -/
def list_transvec_row : list (matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜) :=
list.of_fn $ λ i : fin r, transvection (inr star) (inl i) $
  -M (inr star) (inl i) / M (inr star) (inr star)

/-- Multiplying by some of the matrices in `list_transvec_col M` does not change the last row. -/
lemma list_transvec_col_mul_last_row_drop (i : fin r ⊕ unit) {k : ℕ} (hk : k ≤ r) :
  (((list_transvec_col M).drop k).prod ⬝ M) (inr star) i = M (inr star) i :=
begin
  apply nat.decreasing_induction' _ hk,
  { simp only [list_transvec_col, list.length_of_fn, matrix.one_mul, list.drop_eq_nil_of_le,
      list.prod_nil], },
  { assume n hn hk IH,
    have hn' : n < (list_transvec_col M).length, by simpa [list_transvec_col] using hn,
    rw ← list.cons_nth_le_drop_succ hn',
    simpa [list_transvec_col, matrix.mul_assoc] }
end

/-- Multiplying by all the matrices in `list_transvec_col M` does not change the last row. -/
lemma list_transvec_col_mul_last_row (i : fin r ⊕ unit) :
  ((list_transvec_col M).prod ⬝ M) (inr star) i = M (inr star) i :=
by simpa using list_transvec_col_mul_last_row_drop M i (zero_le _)

/-- Multiplying by all the matrices in `list_transvec_col M` kills all the coefficients in the
last column but the last one. -/
lemma list_transvec_col_mul_last_col (hM : M (inr star) (inr star) ≠ 0) (i : fin r) :
  ((list_transvec_col M).prod ⬝ M) (inl i) (inr star) = 0 :=
begin
  suffices H : ∀ (k : ℕ), k ≤ r → (((list_transvec_col M).drop k).prod ⬝ M) (inl i) (inr star) =
    if k ≤ i then 0 else M (inl i) (inr star),
      by simpa only [if_true, list.drop.equations._eqn_1] using H 0 (zero_le _),
  assume k hk,
  apply nat.decreasing_induction' _ hk,
  { simp only [list_transvec_col, list.length_of_fn, matrix.one_mul, list.drop_eq_nil_of_le,
      list.prod_nil],
    rw if_neg,
    simpa only [not_le] using i.2 },
  { assume n hn hk IH,
    have hn' : n < (list_transvec_col M).length, by simpa [list_transvec_col] using hn,
    let n' : fin r := ⟨n, hn⟩,
    rw ← list.cons_nth_le_drop_succ hn',
    have A : (list_transvec_col M).nth_le n hn' = transvection (inl n') (inr star)
      (-M (inl n') (inr star) / M (inr star) (inr star)), by simp [list_transvec_col],
    simp only [matrix.mul_assoc, A, matrix.mul_eq_mul, list.prod_cons],
    by_cases h : n' = i,
    { have hni : n = i,
      { cases i, simp only [subtype.mk_eq_mk] at h, simp [h] },
      rw [h, transvection_mul_apply_same, IH, list_transvec_col_mul_last_row_drop _ _ hn, ← hni],
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

/-- Multiplying by some of the matrices in `list_transvec_row M` does not change the last column. -/
lemma mul_list_transvec_row_last_col_take (i : fin r ⊕ unit) {k : ℕ} (hk : k ≤ r) :
  (M ⬝ ((list_transvec_row M).take k).prod) i (inr star) = M i (inr star) :=
begin
  induction k with k IH,
  { simp only [matrix.mul_one, list.take_zero, list.prod_nil], },
  { have hkr : k < r := hk,
    let k' : fin r := ⟨k, hkr⟩,
    have : (list_transvec_row M).nth k = ↑(transvection (inr unit.star) (inl k')
      (-M (inr unit.star) (inl k') / M (inr unit.star) (inr unit.star))),
    { simp only [list_transvec_row, list.of_fn_nth_val, hkr, dif_pos, list.nth_of_fn], refl },
    simp only [list.take_succ, ← matrix.mul_assoc, this, list.prod_append, matrix.mul_one,
      matrix.mul_eq_mul, list.prod_cons, list.prod_nil, option.to_list_some],
    rw [mul_transvection_apply_of_ne, IH hkr.le],
    simp only [ne.def, not_false_iff], }
end

/-- Multiplying by all the matrices in `list_transvec_row M` does not change the last column. -/
lemma mul_list_transvec_row_last_col (i : fin r ⊕ unit) :
  (M ⬝ (list_transvec_row M).prod) i (inr star) = M i (inr star) :=
begin
  have A : (list_transvec_row M).length = r, by simp [list_transvec_row],
  rw [← list.take_length (list_transvec_row M), A],
  simpa using mul_list_transvec_row_last_col_take M i le_rfl,
end

/-- Multiplying by all the matrices in `list_transvec_row M` kills all the coefficients in the
last row but the last one. -/
lemma mul_list_transvec_row_last_row (hM : M (inr star) (inr star) ≠ 0) (i : fin r) :
  (M ⬝ (list_transvec_row M).prod) (inr star) (inl i) = 0 :=
begin
  suffices H : ∀ (k : ℕ), k ≤ r → (M ⬝ ((list_transvec_row M).take k).prod) (inr star) (inl i) =
    if k ≤ i then M (inr star) (inl i) else 0,
  { have A : (list_transvec_row M).length = r, by simp [list_transvec_row],
    rw [← list.take_length (list_transvec_row M), A],
    have : ¬ (r ≤ i), by simpa using i.2,
    simpa only [this, ite_eq_right_iff] using H r le_rfl },
  assume k hk,
  induction k with n IH,
  { simp only [if_true, matrix.mul_one, list.take_zero, zero_le', list.prod_nil] },
  { have hnr : n < r := hk,
    let n' : fin r := ⟨n, hnr⟩,
    have A : (list_transvec_row M).nth n = ↑(transvection (inr unit.star) (inl n')
      (-M (inr unit.star) (inl n') / M (inr unit.star) (inr unit.star))),
    { simp only [list_transvec_row, list.of_fn_nth_val, hnr, dif_pos, list.nth_of_fn], refl },
    simp only [list.take_succ, A, ← matrix.mul_assoc, list.prod_append, matrix.mul_one,
      matrix.mul_eq_mul, list.prod_cons, list.prod_nil, option.to_list_some],
    by_cases h : n' = i,
    { have hni : n = i,
      { cases i, simp only [subtype.mk_eq_mk] at h, simp only [h, coe_mk] },
      have : ¬ (n.succ ≤ i), by simp only [← hni, n.lt_succ_self, not_le],
      simp only [h, mul_transvection_apply_same, list.take, if_false,
        mul_list_transvec_row_last_col_take _ _ hnr.le, hni.le, this, if_true, IH hnr.le],
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

/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` kills
all the coefficients in the last row but the last one. -/
lemma list_transvec_col_mul_mul_list_transvec_row_last_col
  (hM : M (inr star) (inr star) ≠ 0) (i : fin r) :
  ((list_transvec_col M).prod ⬝ M ⬝ (list_transvec_row M).prod) (inr star) (inl i) = 0 :=
begin
  have : list_transvec_row M = list_transvec_row ((list_transvec_col M).prod ⬝ M),
    by simp [list_transvec_row, list_transvec_col_mul_last_row],
  rw this,
  apply mul_list_transvec_row_last_row,
  simpa [list_transvec_col_mul_last_row] using hM
end

/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` kills
all the coefficients in the last column but the last one. -/
lemma list_transvec_col_mul_mul_list_transvec_row_last_row
  (hM : M (inr star) (inr star) ≠ 0) (i : fin r) :
  ((list_transvec_col M).prod ⬝ M ⬝ (list_transvec_row M).prod) (inl i) (inr star) = 0 :=
begin
  have : list_transvec_col M = list_transvec_col (M ⬝ (list_transvec_row M).prod),
    by simp [list_transvec_col, mul_list_transvec_row_last_col],
  rw [this, matrix.mul_assoc],
  apply list_transvec_col_mul_last_col,
  simpa [mul_list_transvec_row_last_col] using hM
end

/-- Multiplying by all the matrices either in `list_transvec_col M` and `list_transvec_row M` turns
the matrix in block-diagonal form. -/
lemma is_two_block_diagonal_list_transvec_col_mul_mul_list_transvec_row
  (hM : M (inr star) (inr star) ≠ 0) :
  is_two_block_diagonal ((list_transvec_col M).prod ⬝ M ⬝ (list_transvec_row M).prod) :=
begin
  split,
  { ext i j,
    have : j = star, by simp only [eq_iff_true_of_subsingleton],
    simp [to_blocks₁₂, this, list_transvec_col_mul_mul_list_transvec_row_last_row M hM] },
  { ext i j,
    have : i = star, by simp only [eq_iff_true_of_subsingleton],
    simp [to_blocks₂₁, this, list_transvec_col_mul_mul_list_transvec_row_last_col M hM] },
end

/-- There exist two lists of `transvection_struct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal, when the last coefficient is nonzero. -/
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
  have A : L.map to_matrix = list_transvec_col M, by simp [L, list_transvec_col, (∘)],
  have B : L'.map to_matrix = list_transvec_row M, by simp [L, list_transvec_row, (∘)],
  rw [A, B],
  exact is_two_block_diagonal_list_transvec_col_mul_mul_list_transvec_row M hM
end

/-- There exist two lists of `transvection_struct` such that multiplying by them on the left and
on the right makes a matrix block-diagonal. -/
lemma exists_is_two_block_diagonal_list_transvec_mul_mul_list_transvec
  (M : matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜) :
  ∃ (L L' : list (transvection_struct (fin r ⊕ unit) 𝕜)),
  is_two_block_diagonal ((L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod) :=
begin
  by_cases H : is_two_block_diagonal M, { refine ⟨list.nil, list.nil, by simpa using H⟩ },
  -- we have already proved this when the last coefficient is nonzero
  by_cases hM : M (inr star) (inr star) ≠ 0,
  { exact exists_is_two_block_diagonal_of_ne_zero M hM },
  -- when the last coefficient is zero but there is a nonzero coefficient on the last row or the
  -- last column, we will first put this nonzero coefficient in last position, and then argue as
  -- above.
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

/-- Inductive step for the reduction: if one knows that any size `r` matrix can be reduced to
diagonal form by elementary operations, then one deduces it for matrices over `fin r ⊕ unit`. -/
lemma exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
  (IH : ∀ (M : matrix (fin r) (fin r) 𝕜),
    ∃ (L₀ L₀' : list (transvection_struct (fin r) 𝕜)) (D₀ : (fin r) → 𝕜),
      (L₀.map to_matrix).prod ⬝ M ⬝ (L₀'.map to_matrix).prod = diagonal D₀)
  (M : matrix (fin r ⊕ unit) (fin r ⊕ unit) 𝕜) :
  ∃ (L L' : list (transvection_struct (fin r ⊕ unit) 𝕜)) (D : fin r ⊕ unit → 𝕜),
    (L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod = diagonal D :=
begin
  rcases exists_is_two_block_diagonal_list_transvec_mul_mul_list_transvec M with ⟨L₁, L₁', hM⟩,
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

variables {n p} [fintype n] [fintype p]

/-- Reduction to diagonal form by elementary operations is invariant under reindexing. -/
lemma reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal (M : matrix p p 𝕜) (e : p ≃ n)
  (H : ∃ (L L' : list (transvection_struct n 𝕜)) (D : n → 𝕜),
    (L.map to_matrix).prod ⬝ (matrix.reindex_alg_equiv 𝕜 e M) ⬝ (L'.map to_matrix).prod
      = diagonal D) :
  ∃ (L L' : list (transvection_struct p 𝕜)) (D : p → 𝕜),
    (L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod = diagonal D :=
begin
  rcases H with ⟨L₀, L₀', D₀, h₀⟩,
  refine ⟨L₀.map (reindex_equiv e.symm), L₀'.map (reindex_equiv e.symm), D₀ ∘ e, _⟩,
  have : M = reindex_alg_equiv 𝕜 e.symm (reindex_alg_equiv 𝕜 e M),
    by simp only [equiv.symm_symm, minor_minor, reindex_apply, minor_id_id, equiv.symm_comp_self,
      reindex_alg_equiv_apply],
  rw this,
  simp only [to_matrix_reindex_equiv_prod, list.map_map, reindex_alg_equiv_apply],
  simp only [← reindex_alg_equiv_apply, ← reindex_alg_equiv_mul, h₀],
  simp only [equiv.symm_symm, reindex_apply, minor_diagonal_equiv, reindex_alg_equiv_apply],
end

/-- Any matrix can be reduced to diagonal form by elementary operations. Formulated here on `Type 0`
because we will make an induction using `fin r`.
See `exists_list_transvec_mul_mul_list_transvec_eq_diagonal` for the general version (which follows
from this one and reindexing). -/
lemma exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux
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
    apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e,
    apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_induction
      (λ N, IH (fin r) N (by simp)) }
end

/-- Any matrix can be reduced to diagonal form by elementary operations. -/
theorem exists_list_transvec_mul_mul_list_transvec_eq_diagonal
  (M : matrix n n 𝕜) : ∃ (L L' : list (transvection_struct n 𝕜)) (D : n → 𝕜),
  (L.map to_matrix).prod ⬝ M ⬝ (L'.map to_matrix).prod = diagonal D :=
begin
  have e : n ≃ fin (fintype.card n) := fintype.equiv_of_card_eq (by simp),
  apply reindex_exists_list_transvec_mul_mul_list_transvec_eq_diagonal M e,
  apply exists_list_transvec_mul_mul_list_transvec_eq_diagonal_aux
end

/-- Any matrix can be written as the product of transvections, a diagonal matrix, and
transvections.-/
theorem exists_list_transvec_mul_diagonal_mul_list_transvec
  (M : matrix n n 𝕜) : ∃ (L L' : list (transvection_struct n 𝕜)) (D : n → 𝕜),
  M = (L.map to_matrix).prod ⬝ diagonal D ⬝ (L'.map to_matrix).prod :=
begin
  rcases exists_list_transvec_mul_mul_list_transvec_eq_diagonal M with ⟨L, L', D, h⟩,
  refine ⟨L.reverse.map transvection_struct.inv, L'.reverse.map transvection_struct.inv, D, _⟩,
  suffices : M =
    ((L.reverse.map (to_matrix ∘ transvection_struct.inv)).prod ⬝ (L.map to_matrix).prod) ⬝ M ⬝
    ((L'.map to_matrix).prod ⬝ (L'.reverse.map (to_matrix ∘ transvection_struct.inv)).prod),
      by simpa [← h, matrix.mul_assoc],
  rw [reverse_inv_prod_mul_prod, prod_mul_reverse_inv_prod, matrix.one_mul, matrix.mul_one],
end

end pivot

open pivot transvection_struct

variables {n} [fintype n]

/-- Induction principle for matrices based on transvections: if a property is true for all diagonal
matrices, all transvections, and is stable under product, then it is true for all matrices. This is
the useful way to say that matrices are generated by diagonal matrices and transvections.

We state a slightly more general version: to prove a property for a matrix `M`, it suffices to
assume that the diagonal matrices we consider have the same determinant as `M`. This is useful to
obtain similar principles for `SLₙ` or `GLₙ`. -/
lemma diagonal_transvection_induction (P : matrix n n 𝕜 → Prop) (M : matrix n n 𝕜)
  (hdiag : ∀ D : n → 𝕜, det (diagonal D) = det M → P (diagonal D))
  (htransvec : ∀ (t : transvection_struct n 𝕜), P t.to_matrix)
  (hmul : ∀ A B, P A → P B → P (A ⬝ B)) :
  P M :=
begin
  rcases exists_list_transvec_mul_diagonal_mul_list_transvec M with ⟨L, L', D, h⟩,
  have PD : P (diagonal D) := hdiag D (by simp [h]),
  suffices H : ∀ (L₁ L₂ : list (transvection_struct n 𝕜)) (E : matrix n n 𝕜),
    P E → P ((L₁.map to_matrix).prod ⬝ E ⬝ (L₂.map to_matrix).prod),
      by { rw h, apply H L L', exact PD },
  assume L₁ L₂ E PE,
  induction L₁ with t L₁ IH,
  { simp only [matrix.one_mul, list.prod_nil, list.map],
    induction L₂ with t L₂ IH generalizing E,
    { simpa },
    { simp only [←matrix.mul_assoc, list.prod_cons, mul_eq_mul, list.map],
      apply IH,
      exact hmul _ _ PE (htransvec _) } },
  { simp only [matrix.mul_assoc, list.prod_cons, mul_eq_mul, list.map] at ⊢ IH,
    exact hmul _ _ (htransvec _) IH }
end

/-- Induction principle for invertible matrices based on transvections: if a property is true for
all invertible diagonal matrices, all transvections, and is stable under product of invertible
matrices, then it is true for all invertible matrices. This is the useful way to say that
invertible matrices are generated by invertible diagonal matrices and transvections. -/
lemma diagonal_transvection_induction_of_det_ne_zero (P : matrix n n 𝕜 → Prop)
  (M : matrix n n 𝕜) (hMdet : det M ≠ 0)
  (hdiag : ∀ D : n → 𝕜, det (diagonal D) ≠ 0 → P (diagonal D))
  (htransvec : ∀ (t : transvection_struct n 𝕜), P t.to_matrix)
  (hmul : ∀ A B, det A ≠ 0 → det B ≠ 0 → P A → P B → P (A ⬝ B)) :
  P M :=
begin
  let Q : matrix n n 𝕜 → Prop := λ N, det N ≠ 0 ∧ P N,
  have : Q M,
  { apply diagonal_transvection_induction Q M,
    { assume D hD,
      have detD : det (diagonal D) ≠ 0, by { rw hD, exact hMdet },
      exact ⟨detD, hdiag _ detD⟩ },
    { assume t,
      exact ⟨by simp, htransvec t⟩ },
    { assume A B QA QB,
      exact ⟨by simp [QA.1, QB.1], hmul A B QA.1 QB.1 QA.2 QB.2⟩ } },
  exact this.2
end

end matrix
