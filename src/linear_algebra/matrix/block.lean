/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.determinant
import tactic.fin_cases

/-!
# Block matrices and their determinant

This file defines a predicate `matrix.block_triangular_matrix` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

 * `matrix.block_triangular_matrix` expresses that a `o` by `o` matrix is block triangular,
   if the rows and columns are ordered according to some order `b : o → ℕ`

## Main results
  * `det_of_block_triangular_matrix`: the determinant of a block triangular matrix
    is equal to the product of the determinants of all the blocks
  * `det_of_upper_triangular` and `det_of_lower_triangular`: the determinant of
    a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/

open_locale big_operators

universes v

variables {m n : Type*} [decidable_eq n] [fintype n] [decidable_eq m] [fintype m]
variables {R : Type v} [comm_ring R]

namespace matrix

lemma det_to_block (M : matrix m m R) (p : m → Prop) [decidable_pred p] :
  M.det = (matrix.from_blocks (to_block M p p) (to_block M p (λ j, ¬p j))
    (to_block M (λ j, ¬p j) p) (to_block M (λ j, ¬p j) (λ j, ¬p j))).det :=
begin
  rw ← matrix.det_reindex_self (equiv.sum_compl p).symm M,
  rw [det_apply', det_apply'],
  congr, ext σ, congr, ext,
  generalize hy : σ x = y,
  cases x; cases y;
  simp only [matrix.reindex_apply, to_block_apply, equiv.symm_symm,
    equiv.sum_compl_apply_inr, equiv.sum_compl_apply_inl,
    from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂,
    matrix.minor_apply],
end

lemma det_to_square_block (M : matrix m m R) {n : nat} (b : m → fin n) (k : fin n) :
  (to_square_block M b k).det = (to_square_block_prop M (λ i, b i = k)).det :=
by simp

lemma det_to_square_block' (M : matrix m m R) (b : m → ℕ) (k : ℕ) :
  (to_square_block' M b k).det = (to_square_block_prop M (λ i, b i = k)).det :=
by simp

lemma two_block_triangular_det (M : matrix m m R) (p : m → Prop) [decidable_pred p]
  (h : ∀ i (h1 : ¬p i) j (h2 : p j), M i j = 0) :
  M.det = (to_square_block_prop M p).det * (to_square_block_prop M (λ i, ¬p i)).det :=
begin
  rw det_to_block M p,
  convert upper_two_block_triangular_det (to_block M p p) (to_block M p (λ j, ¬p j))
    (to_block M (λ j, ¬p j) (λ j, ¬p j)),
  ext,
  exact h ↑i i.2 ↑j j.2
end

lemma equiv_block_det (M : matrix m m R) {p q : m → Prop} [decidable_pred p] [decidable_pred q]
  (e : ∀x, q x ↔ p x) : (to_square_block_prop M p).det = (to_square_block_prop M q).det :=
by convert matrix.det_reindex_self (equiv.subtype_equiv_right e) (to_square_block_prop M q)

lemma to_square_block_det'' (M : matrix m m R) {n : nat} (b : m → fin n) (k : fin n) :
  (to_square_block M b k).det = (to_square_block' M (λ i, ↑(b i)) ↑k).det :=
begin
  rw [to_square_block_def', to_square_block_def],
  apply equiv_block_det,
  intro x,
  apply (fin.ext_iff _ _).symm
end

/-- Let `b` map rows and columns of a square matrix `M` to `n` blocks. Then
  `block_triangular_matrix' M n b` says the matrix is block triangular. -/
def block_triangular_matrix' {o : Type*} (M : matrix o o R) {n : ℕ}
  (b : o → fin n) : Prop :=
∀ i j, b j < b i → M i j = 0

lemma upper_two_block_triangular' {m n : Type*}
  (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) :
  block_triangular_matrix' (from_blocks A B 0 D) (sum.elim (λ i, (0 : fin 2)) (λ j, 1)) :=
begin
  intros k1 k2 hk12,
  have h0 : ∀ (k : m ⊕ n), sum.elim (λ i, (0 : fin 2)) (λ j, 1) k = 0 → ∃ i, k = sum.inl i,
  { simp },
  have h1 : ∀ (k : m ⊕ n), sum.elim (λ i, (0 : fin 2)) (λ j, 1) k = 1 → ∃ j, k = sum.inr j,
  { simp },
  set mk1 := (sum.elim (λ i, (0 : fin 2)) (λ j, 1)) k1 with hmk1,
  set mk2 := (sum.elim (λ i, (0 : fin 2)) (λ j, 1)) k2 with hmk2,
  fin_cases mk1 using h; fin_cases mk2 using h_1; rw [h, h_1] at hk12,
  { exact absurd hk12 (nat.not_lt_zero 0) },
  { exact absurd hk12 (by norm_num) },
  { rw hmk1 at h,
    obtain ⟨i, hi⟩ := h1 k1 h,
    rw hmk2 at h_1,
    obtain ⟨j, hj⟩ := h0 k2 h_1,
    rw [hi, hj], simp },
  { exact absurd hk12 (irrefl 1) }
end

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `ℕ`s. Then
  `block_triangular_matrix M n b` says the matrix is block triangular. -/
def block_triangular_matrix {o : Type*} (M : matrix o o R) (b : o → ℕ) : Prop :=
∀ i j, b j < b i → M i j = 0

lemma upper_two_block_triangular {m n : Type*}
  (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) :
  block_triangular_matrix (from_blocks A B 0 D) (sum.elim (λ i, 0) (λ j, 1)) :=
begin
  intros k1 k2 hk12,
  have h01 : ∀ (k : m ⊕ n), sum.elim (λ i, 0) (λ j, 1) k = 0 ∨ sum.elim (λ i, 0) (λ j, 1) k = 1,
  { simp },
  have h0 : ∀ (k : m ⊕ n), sum.elim (λ i, 0) (λ j, 1) k = 0 → ∃ i, k = sum.inl i, { simp },
  have h1 : ∀ (k : m ⊕ n), sum.elim (λ i, 0) (λ j, 1) k = 1 → ∃ j, k = sum.inr j, { simp },
  cases (h01 k1) with hk1 hk1; cases (h01 k2) with hk2 hk2; rw [hk1, hk2] at hk12,
  { exact absurd hk12 (nat.not_lt_zero 0) },
  { exact absurd hk12 (nat.not_lt_zero 1) },
  { obtain ⟨i, hi⟩ := h1 k1 hk1,
    obtain ⟨j, hj⟩ := h0 k2 hk2,
    rw [hi, hj], simp },
  { exact absurd hk12 (irrefl 1) }
end

lemma det_of_block_triangular_matrix (M : matrix m m R) (b : m → ℕ)
  (h : block_triangular_matrix M b) :
  ∀ (n : ℕ) (hn : ∀ i, b i < n), M.det = ∏ k in finset.range n, (to_square_block' M b k).det :=
begin
  intros n hn,
  tactic.unfreeze_local_instances,
  induction n with n hi generalizing m M b,
  { rw finset.prod_range_zero,
    apply det_eq_one_of_card_eq_zero,
    apply fintype.card_eq_zero_iff.mpr,
    exact ⟨λ i, nat.not_lt_zero (b i) (hn i)⟩ },
  { rw [finset.prod_range_succ_comm],
    have h2 : (M.to_square_block_prop (λ (i : m), b i = n.succ)).det =
      (M.to_square_block' b n.succ).det,
    { dunfold to_square_block', dunfold to_square_block_prop, refl },
    rw two_block_triangular_det M (λ i, ¬(b i = n)),
    { rw mul_comm,
      apply congr (congr_arg has_mul.mul _),
      { let m' := {a // ¬b a = n },
        let b' := (λ (i : m'), b ↑i),
        have h' :
          block_triangular_matrix (M.to_square_block_prop (λ (i : m), ¬b i = n)) b',
        { intros i j, apply h ↑i ↑j },
        have hni : ∀ (i : {a // ¬b a = n}), b' i < n,
        { exact λ i, (ne.le_iff_lt i.property).mp (nat.lt_succ_iff.mp (hn ↑i)) },
        have h1 := hi (M.to_square_block_prop (λ (i : m), ¬b i = n)) b' h' hni,
        rw ←fin.prod_univ_eq_prod_range at h1 ⊢,
        convert h1,
        ext k,
        simp only [to_square_block_def', to_square_block_def],
        let he : {a // b' a = ↑k} ≃ {a // b a = ↑k},
        { have hc : ∀ (i : m), (λ a, b a = ↑k) i → (λ a, ¬b a = n) i,
          { intros i hbi, rw hbi, exact ne_of_lt (fin.is_lt k) },
          exact equiv.subtype_subtype_equiv_subtype hc },
        exact matrix.det_reindex_self he (λ (i j : {a // b' a = ↑k}), M ↑i ↑j) },
      { rw det_to_square_block' M b n,
        have hh : ∀ a, b a = n ↔ ¬(λ (i : m), ¬b i = n) a,
        { intro i, simp only [not_not] },
        exact equiv_block_det M hh }},
    { intros i hi j hj,
      apply (h i), simp only [not_not] at hi,
      rw hi,
      exact (ne.le_iff_lt hj).mp (nat.lt_succ_iff.mp (hn j)) }}
end

lemma det_of_block_triangular_matrix'' (M : matrix m m R) (b : m → ℕ)
  (h : block_triangular_matrix M b) :
  M.det = ∏ k in finset.image b finset.univ, (to_square_block' M b k).det :=
begin
  let n : ℕ := (Sup (finset.image b finset.univ : set ℕ)).succ,
  have hn : ∀ i, b i < n,
  { have hbi : ∀ i, b i ∈ finset.image b finset.univ, { simp },
    intro i,
    dsimp only [n],
    apply nat.lt_succ_iff.mpr,
    exact le_cSup (finset.bdd_above _) (hbi i) },
  rw det_of_block_triangular_matrix M b h n hn,
  refine (finset.prod_subset _ _).symm,
  { intros a ha, apply finset.mem_range.mpr,
    obtain ⟨i, ⟨hi, hbi⟩⟩ := finset.mem_image.mp ha,
    rw ←hbi,
    exact hn i },
  { intros k hk hbk,
    apply det_eq_one_of_card_eq_zero,
    apply fintype.card_eq_zero_iff.mpr,
    constructor,
    simp only [subtype.forall],
    intros a hba, apply hbk,
    apply finset.mem_image.mpr,
    use a,
    exact ⟨finset.mem_univ a, hba⟩ }
end

lemma det_of_block_triangular_matrix' (M : matrix m m R) {n : ℕ} (b : m → fin n)
  (h : block_triangular_matrix' M b) :
  M.det = ∏ (k : fin n), (to_square_block M b k).det :=
begin
  let b2 : m → ℕ := λ i, ↑(b i),
  simp_rw to_square_block_det'',
  rw fin.prod_univ_eq_prod_range (λ (k : ℕ), (M.to_square_block' b2 k).det) n,
  apply det_of_block_triangular_matrix,
  { intros i j hij, exact h i j (fin.coe_fin_lt.mp hij) },
  { intro i, exact fin.is_lt (b i) }
end

lemma det_of_upper_triangular {n : ℕ} (M : matrix (fin n) (fin n) R)
  (h : ∀ (i j : fin n), j < i → M i j = 0) :
  M.det = ∏ i : (fin n), M i i :=
begin
  convert det_of_block_triangular_matrix' M id h,
  ext i,
  have h2 : ∀ (j : {a // id a = i}), j = ⟨i, rfl⟩ :=
    λ (j : {a // id a = i}), subtype.ext j.property,
  haveI : unique {a // id a = i} := ⟨⟨⟨i, rfl⟩⟩, h2⟩,
  simp [h2 (default {a // id a = i})]
end

lemma det_of_lower_triangular {n : ℕ} (M : matrix (fin n) (fin n) R)
  (h : ∀ (i j : fin n), i < j → M i j = 0) :
  M.det = ∏ i : (fin n), M i i :=
begin
  rw ← det_transpose,
  exact det_of_upper_triangular _ (λ (i j : fin n) (hji : j < i), h j i hji)
end

end matrix
