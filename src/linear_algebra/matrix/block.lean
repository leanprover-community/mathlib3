/-
Copyright (c) 2019 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johannes Hölzl, Patrick Massot, Casper Putz, Anne Baanen
-/
import linear_algebra.matrix.determinant
import tactic.fin_cases

/-!
# Block matrices and their determinant

This file defines a predicate `matrix.block_triangular` saying a matrix
is block triangular, and proves the value of the determinant for various
matrices built out of blocks.

## Main definitions

 * `matrix.block_triangular` expresses that a `o` by `o` matrix is block triangular,
   if the rows and columns are ordered according to some order `b : o → α`

## Main results
  * `det_of_block_triangular`: the determinant of a block triangular matrix
    is equal to the product of the determinants of all the blocks
  * `det_of_upper_triangular` and `det_of_lower_triangular`: the determinant of
    a triangular matrix is the product of the entries along the diagonal

## Tags

matrix, diagonal, det, block triangular

-/

open finset function order_dual
open_locale big_operators matrix

universes v

variables {α m n : Type*}
variables {R : Type v} [comm_ring R] {M : matrix m m R} {b : m → α}

namespace matrix

section has_lt
variables [has_lt α]

/-- Let `b` map rows and columns of a square matrix `M` to blocks indexed by `ℕ`s. Then
`block_triangular M n b` says the matrix is block triangular. -/
def block_triangular (M : matrix m m R) (b : m → α) : Prop := ∀ ⦃i j⦄, b j < b i → M i j = 0

protected lemma block_triangular.minor {f : n → m} (h : M.block_triangular b) :
  (M.minor f f).block_triangular (b ∘ f) :=
λ i j hij, h hij

@[simp] lemma block_triangular_reindex_iff {b : n → α} {e : m ≃ n} :
  (reindex e e M).block_triangular b ↔ M.block_triangular (b ∘ e) :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { convert h.minor,
    simp only [reindex_apply, minor_minor, minor_id_id, equiv.symm_comp_self] },
  { convert h.minor,
    simp only [comp.assoc b e e.symm, equiv.self_comp_symm, comp.right_id] }
end

protected lemma block_triangular.transpose :
  M.block_triangular b → Mᵀ.block_triangular (to_dual ∘ b) := swap

@[simp] protected lemma block_triangular_transpose_iff {b : m → αᵒᵈ} :
  Mᵀ.block_triangular b ↔ M.block_triangular (of_dual ∘ b) := forall_swap

end has_lt

lemma upper_two_block_triangular' (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) :
  block_triangular (from_blocks A B 0 D) (sum.elim (λ i, (0 : fin 2)) (λ j, 1)) :=
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

lemma upper_two_block_triangular (A : matrix m m R) (B : matrix m n R) (D : matrix n n R) :
  block_triangular (from_blocks A B 0 D) (sum.elim (λ i, 0) (λ j, 1)) :=
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

/-! ### Determinant -/

variables [decidable_eq m] [fintype m] [decidable_eq n] [fintype n]

lemma equiv_block_det (M : matrix m m R) {p q : m → Prop} [decidable_pred p] [decidable_pred q]
  (e : ∀ x, q x ↔ p x) : (to_square_block_prop M p).det = (to_square_block_prop M q).det :=
by convert matrix.det_reindex_self (equiv.subtype_equiv_right e) (to_square_block_prop M q)

@[simp] lemma det_to_square_block_id [decidable_eq R] (M : matrix m m R) (i : m) :
  (M.to_square_block id i).det = M i i :=
begin
  letI : unique {a // id a = i} := ⟨⟨⟨i, rfl⟩⟩, λ j, subtype.ext j.property⟩,
  exact (det_unique _).trans rfl,
end

lemma det_to_block (M : matrix m m R) (p : m → Prop) [decidable_pred p] :
  M.det = (from_blocks (to_block M p p) (to_block M p $ λ j, ¬p j)
    (to_block M (λ j, ¬p j) p) $ to_block M (λ j, ¬p j) $ λ j, ¬p j).det :=
begin
  rw ←matrix.det_reindex_self (equiv.sum_compl p).symm M,
  rw [det_apply', det_apply'],
  congr, ext σ, congr, ext,
  generalize hy : σ x = y,
  cases x; cases y;
  simp only [matrix.reindex_apply, to_block_apply, equiv.symm_symm,
    equiv.sum_compl_apply_inr, equiv.sum_compl_apply_inl,
    from_blocks_apply₁₁, from_blocks_apply₁₂, from_blocks_apply₂₁, from_blocks_apply₂₂,
    matrix.minor_apply],
end

lemma two_block_triangular_det (M : matrix m m R) (p : m → Prop) [decidable_pred p]
  (h : ∀ i, ¬ p i → ∀ j, p j → M i j = 0) :
  M.det = (to_square_block_prop M p).det * (to_square_block_prop M (λ i, ¬p i)).det :=
begin
  rw det_to_block M p,
  convert det_from_blocks_zero₂₁ (to_block M p p) (to_block M p (λ j, ¬p j))
    (to_block M (λ j, ¬p j) (λ j, ¬p j)),
  ext,
  exact h ↑i i.2 ↑j j.2
end

lemma two_block_triangular_det' (M : matrix m m R) (p : m → Prop) [decidable_pred p]
  (h : ∀ i, p i → ∀ j, ¬ p j → M i j = 0) :
  M.det = (to_square_block_prop M p).det * (to_square_block_prop M (λ i, ¬p i)).det :=
begin
  rw [M.two_block_triangular_det (λ i, ¬ p i), mul_comm],
  simp_rw not_not,
  congr' 1,
  exact equiv_block_det _ (λ _, not_not.symm),
  simpa only [not_not] using h,
end

lemma to_square_block_det'' (M : matrix m m R) {n : nat} (b : m → fin n) (k : fin n) :
  (M.to_square_block b k).det = (M.to_square_block (λ i, (b i : ℕ)) k).det :=
equiv_block_det _ $ λ _, (fin.ext_iff _ _).symm

lemma det_of_block_triangular (M : matrix m m R) (b : m → ℕ) (h : M.block_triangular b) :
  ∀ (n : ℕ) (hn : ∀ i, b i < n), M.det = ∏ k in range n, (M.to_square_block b k).det :=
begin
  intros n hn,
  unfreezingI { induction n with n hi generalizing m M b },
  { haveI : is_empty m := ⟨λ i, not_lt_bot $ hn i⟩,
    exact det_is_empty },
  rw [prod_range_succ_comm],
  have h2 : (M.to_square_block_prop (λ (i : m), b i = n.succ)).det =
    (M.to_square_block b n.succ).det,
  { refl },
  rw two_block_triangular_det' M (λ i, b i = n),
  { refine congr_arg _ _,
    let b' := λ i : {a // b a ≠ n}, b ↑i,
    have h' :  block_triangular (M.to_square_block_prop (λ (i : m), b i ≠ n)) b',
    { intros i j, apply h },
    have hni : ∀ (i : {a // b a ≠ n}), b' i < n,
    { exact λ i, (ne.le_iff_lt i.property).mp (nat.lt_succ_iff.mp (hn ↑i)) },
    have h1 := hi (M.to_square_block_prop (λ (i : m), b i ≠ n)) b' h' hni,
    rw ←fin.prod_univ_eq_prod_range at h1 ⊢,
    convert h1,
    ext k,
    simp only [to_square_block_def],
    let he : {a // b' a = ↑k} ≃ {a // b a = ↑k},
    { have hc : ∀ (i : m), (λ a, b a = ↑k) i → (λ a, b a ≠ n) i,
      { intros i hbi, rw hbi, exact ne_of_lt (fin.is_lt k) },
      exact equiv.subtype_subtype_equiv_subtype hc },
    exact matrix.det_reindex_self he (λ (i j : {a // b' a = ↑k}), M ↑i ↑j) },
  { rintro i rfl j hj,
    exact h ((nat.lt_succ_iff.mp $ hn _).lt_of_ne hj) }
end

lemma _root_.function.surjective.image_univ {β} [fintype α] [fintype β] [decidable_eq β] {f : α → β}
  (hf : function.surjective f) : univ.image f = univ :=
eq_univ_iff_forall.mpr $ λ x, mem_image.mpr $ (exists_congr $ by simp).mp $ hf x

-- there's already an `equiv.subtype_congr`; I feel like it's misnamed though.
@[simps?] def equiv.subtype_congr {α₁ α₂ : Type*} (e : α₁ ≃ α₂) (p : α₂ → Prop) : {a₁ // p (e a₁)} ≃ {a₂ // p a₂} :=
{ to_fun    := λ a₁, ⟨e a₁, a₁.prop⟩,
  inv_fun   := λ a₂, ⟨e.symm a₂, by simpa using a₂.prop⟩,
  left_inv  := λ a₁, subtype.ext $ by simp,
  right_inv := λ a₂, subtype.ext $ by simp }

protected lemma block_triangular.det [decidable_eq α] [preorder α] (hM : block_triangular M b) :
  M.det = ∏ a in univ.image b, (M.to_square_block b a).det :=
begin
  unfreezingI { induction ‹fintype m› using fintype.induction_empty_option'
    with α₁ α₂ h₂ e ih m h ih },
  { haveI : fintype α₁ := fintype.of_equiv _ e.symm,
    haveI : decidable_eq α₁ := classical.dec_eq _,
    rw ←det_reindex_self e.symm,
    convert (ih hM.minor).trans _,
    simp_rw e.symm_symm,
    refine prod_congr _ (λ a ha, _),
    { rw ←image_image,
      congr,
      convert e.surjective.image_univ },
    unfold to_square_block to_square_block_prop to_block,
    rw [minor_minor],
    let e' : {a₁ // (b ∘ e.symm.symm) a₁ = a} ≃ {a₂ // b a₂ = a} :=
      equiv.subtype_congr e.symm.symm (λ x, b x = a),
    rw [←det_minor_equiv_self e' $ M.minor coe coe, minor_minor],
    congr' 1 },
  sorry { simp only [coe_det_is_empty, prod_const_one] },sorry /-
  rw two_block_triangular_det M (λ i, i ≠ none),
  let n : ℕ := (Sup (univ.image b : set ℕ)).succ,
  have hn : ∀ i, b i < n,
  { intro i,
    dsimp only [n],
    apply nat.lt_succ_iff.mpr,
    exact le_cSup (finset.bdd_above _) (mem_image_of_mem _ $ mem_univ _) },
  rw det_of_block_triangular M b h n hn,
  refine (prod_subset (λ a ha, _) $ λ k hk hbk, _).symm,
  { apply mem_range.mpr,
    obtain ⟨i, hi, hbi⟩ := mem_image.mp ha,
    rw ←hbi,
    exact hn i },
{ haveI : is_empty {a // b a = k},
  { refine subtype.is_empty_of_false _,
    rintro a rfl,
    exact hbk (mem_image_of_mem _ $ mem_univ _) },
  exact det_is_empty } -/
end

lemma block_triangular.det_fintype [decidable_eq α] [fintype α] [preorder α]
  (h : block_triangular M b) :
  M.det = ∏ k : α, (M.to_square_block b k).det :=
begin
  refine h.det.trans (prod_subset (subset_univ _) $ λ a _ ha, _),
  have : is_empty {i // b i = a} := ⟨λ i, ha $ mem_image.2 ⟨i, mem_univ _, i.2⟩⟩,
  exactI det_is_empty,
end

lemma det_of_upper_triangular [preorder m] (h : M.block_triangular id) : M.det = ∏ i : m, M i i :=
begin
  haveI : decidable_eq R := classical.dec_eq _,
  simp_rw [h.det, image_id, det_to_square_block_id],
end

lemma det_of_lower_triangular [preorder m] (M : matrix m m R) (h : M.block_triangular to_dual) :
  M.det = ∏ i : m, M i i :=
by { rw ←det_transpose, exact det_of_upper_triangular h.transpose }

end matrix
