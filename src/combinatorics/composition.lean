/-
Ccompoyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import data.fintype.card tactic.omega tactic.tidy

/-!
# Compositions

A composition of an integer `n` is a decomposition of `{0, ..., n-1}` into blocks of consecutive
integers. Equivalently, it is a decomposition `n = i₀ + ... + i_{k-1}` into a sum of positive
integers, where the `iⱼ` are the lengths of the blocks. This notion is closely related to that
of a partition of `n`, but in a composition of `n` the order of the `iⱼ`s matters.

We represent a composition of `n` as a subset of `{0, ..., n}` containing `0` and `n`, where
the elements of the subset (but `n`) correspond to the leftmost points of each block. Another
implementation would be a subset of `{0, ..., n-1}` containing `0`, but this fails in the edge case
`n = 0`. Another implementation would be as an integer `k` and a function `fin k → ℕ` summing to
`n`, but this turns out to be less handy because of dependent type issues.

## Main functions

* `compo : composition n` is a structure, made of a subset of `{0, ..., n}` containing `0` and
  `n`, representing a composition of the natural number `n`.
* `composition_card` states that the cardinality of `composition n` is exactly
  `2^(n-1)`, which is proved by constructing an equiv with the subsets of `fin (n-1)` (this holds
  even for `n = 0`, where `-` is nat subtraction).

Let `compo : composition n` be a composition of `n`. Then
* `compo.max_index` is the number of blocks in the composition
* `compo.size : fin compo.max_index → ℕ` is the size of each block in the composition
* `compo.size_up_to : ℕ → ℕ` is the sum of the size of the blocks up to `i`.
* `compo.embedding i : fin (compo.size i) → fin n` is the increasing embedding of the `i`-th block in
  `fin n`.
* `compo.index j`, for `j : fin n`, is the index of the block containing `j`.

There is a function to construct a composition from a size function, called
`composition.of_size size`, taking a function `size : fin k → ℕ`, and returning the corresponding
composition of `finset.univ.sum size`. Then `of_size_size` states that the size function
of the resulting composition coincides with the original `size`, if it is positive everywhere.
Conversely, starting from a composition `compo` and considering `of_size compo.size` gives
back `compo`.

We also give some tools to compare compositions even when `n` is varying, trying to
circumvent dependent type issues. Notably
* `eq_of_size_up_to_eq` states that two compositions with equal `size_up_to` are equal
* `of_size_inj` states that if two compositions constructed from size functions (possibly
  defined on different `fin k`) are equal, then the size functions themselves had to coincide.

## Implementation details

The main motivation for this structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

## Tags

Composition, partition

## References

<https://en.wikipedia.org/wiki/Composition_(combinatorics)>

-/

/-- A composition of an integer `n` represents a decomposition of `n` into blocks of positive
size `i₀, ..., i_{k-1}`. It is encoded as a subset of `fin (n+1)` containing `0` and `n`, where
the elements of the subset (but `n`) correspond to the leftmost points of each block. -/
@[ext] structure composition (n : ℕ) :=
(boundaries : finset (fin n.succ))
(zero_mem   : (0 : fin n.succ) ∈ boundaries)
(last_mem   : (fin.last n ∈ boundaries))

instance {n : ℕ} : inhabited (composition n) :=
⟨⟨finset.univ, finset.mem_univ _, finset.mem_univ _⟩⟩

/-- Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the left by one. -/
def composition_equiv (n : ℕ) : composition n ≃ finset (fin (n - 1)) :=
{ to_fun := λ compo, {i : fin (n-1) |
    (⟨1 + i.val, by { have := i.2, omega }⟩ : fin n.succ) ∈ compo.boundaries}.to_finset,
  inv_fun := λ s,
    { boundaries := {i : fin n.succ | (i = 0) ∨ (i = fin.last n)
        ∨ (∃ (j : fin (n-1)) (hj : j ∈ s), i.val = j.val + 1)}.to_finset,
      zero_mem   := by simp,
      last_mem   := by simp },
  left_inv := begin
    assume compo,
    ext i,
    simp only [exists_prop, add_comm, set.mem_to_finset, true_or, or_true, set.mem_set_of_eq,
               fin.last_val],
    split,
    { rintro (rfl | rfl | ⟨j, hj1, hj2⟩),
      { exact compo.zero_mem },
      { exact compo.last_mem },
      { convert hj1, rwa fin.ext_iff } },
    { simp only [classical.or_iff_not_imp_left],
      assume i_mem i_ne_zero i_ne_last,
      simp [fin.ext_iff] at i_ne_zero i_ne_last,
      refine ⟨⟨i.val - 1, _⟩, _, _⟩,
      { have : i.val < n + 1 := i.2, omega },
      { convert i_mem, rw fin.ext_iff, simp, omega },
      { simp, omega } },
  end,
  right_inv := begin
    assume s,
    ext i,
    have : 1 + i.val ≠ n,
      by { apply ne_of_lt, have := i.2, omega },
    simp only [fin.ext_iff, this, exists_prop, fin.val_zero, false_or, add_left_inj, add_comm,
      set.mem_to_finset, true_or, add_eq_zero_iff, or_true, one_ne_zero, set.mem_set_of_eq,
      fin.last_val, false_and],
    split,
    { rintros ⟨j, js, hj⟩, convert js, exact (fin.ext_iff _ _).2 hj },
    { assume h, exact ⟨i, h, rfl⟩ }
  end }

instance composition_fintype (n : ℕ) : fintype (composition n) :=
fintype.of_equiv _ (composition_equiv n).symm

lemma composition_card (n : ℕ) : fintype.card (composition n) = 2 ^ (n - 1) :=
begin
  have : fintype.card (finset (fin (n-1))) = 2 ^ (n - 1), by simp,
  rw ← this,
  exact fintype.card_congr (composition_equiv n)
end

namespace composition

variables {n : ℕ} (compo : composition n)

lemma boundaries_nonempty : compo.boundaries.nonempty :=
⟨0, compo.zero_mem⟩

lemma card_boundaries_pos : 0 < finset.card compo.boundaries :=
finset.card_pos.mpr compo.boundaries_nonempty

/-- Number of blocks in a composition. -/
def max_index : ℕ := finset.card compo.boundaries - 1

lemma max_index_le : compo.max_index ≤ n :=
begin
  have : finset.card compo.boundaries ≤ finset.card (finset.univ : finset (fin n.succ)) :=
    finset.card_le_of_subset (finset.subset_univ compo.boundaries),
  rw [finset.card_fin] at this,
  exact nat.pred_le_iff.mpr this
end

lemma lt_length (i : fin compo.max_index) : i.val + 1 < compo.boundaries.card :=
nat.add_lt_of_lt_sub_right i.2

lemma lt_length' (i : fin compo.max_index) : i.val < compo.boundaries.card :=
lt_of_le_of_lt (nat.le_succ i.val) (compo.lt_length i)

lemma lt_card_boundaries_iff {j : ℕ} : j < compo.boundaries.card ↔ j ≤ compo.max_index :=
⟨nat.pred_le_pred, λ H, lt_of_le_of_lt H (buffer.lt_aux_2 compo.card_boundaries_pos)⟩

/-- Size of the `i`-th block in a composition -/
def size (i : fin compo.max_index) : ℕ :=
(finset.mono_of_fin compo.boundaries rfl ⟨i.val + 1, compo.lt_length i⟩).val
  - (finset.mono_of_fin compo.boundaries rfl ⟨i.val, compo.lt_length' i⟩).val

lemma size_pos (i : fin compo.max_index) : 0 < compo.size i :=
begin
  have : (⟨i.val, compo.lt_length' i⟩ : fin compo.boundaries.card) < ⟨i.val + 1, compo.lt_length i⟩ :=
    lt_add_one i.val,
  exact nat.lt_sub_left_of_add_lt (finset.mono_of_fin_strict_mono compo.boundaries rfl this)
end

/-- Sum of the sizes of the first `i` blocks in a composition -/
def size_up_to (i : ℕ) :=
((finset.univ : finset (fin compo.max_index)).filter
  (λ (j : fin compo.max_index), j.val < i)).sum compo.size

lemma size_up_to_zero : compo.size_up_to 0 = 0 :=
begin
  rw size_up_to,
  convert finset.sum_empty,
  ext j,
  simp
end

lemma size_up_to_mono : monotone compo.size_up_to :=
begin
  assume i j hij,
  have A : ∀ k : fin compo.max_index, k.val < i → k.val < j := λ k hk, lt_of_lt_of_le hk hij,
  apply finset.sum_le_sum_of_subset,
  simpa [finset.subset_iff] using A
end

lemma size_up_to_succ (i : fin compo.max_index) :
  compo.size_up_to (i + 1) = compo.size_up_to i + compo.size i :=
begin
  have : ((finset.univ : finset (fin compo.max_index)).filter (λ j, j.val < i + 1))
    = ((finset.univ : finset (fin compo.max_index)).filter (λ j, j.val < i)) ∪ {i},
    by { ext j, simp [nat.lt_succ_iff_lt_or_eq, fin.ext_iff, - add_comm], refl },
  rw [size_up_to, this, finset.sum_union, size_up_to],
  { simp },
  { simp, exact le_refl _ }
end

lemma size_up_to_eq (i : ℕ) (h : i ≤ compo.max_index) :
  compo.size_up_to i = (finset.mono_of_fin compo.boundaries rfl
    ⟨i, compo.lt_card_boundaries_iff.2 h⟩).val :=
begin
  induction i with i IH,
  { simp [size_up_to_zero],
    rw finset.mono_of_fin_zero rfl compo.boundaries_nonempty compo.card_boundaries_pos,
    symmetry,
    suffices H : compo.boundaries.min' compo.boundaries_nonempty = 0, from congr_arg coe H,
    apply le_antisymm,
    { exact finset.min'_le _ compo.boundaries_nonempty _ compo.zero_mem },
    { exact fin.zero_le _ } },
  { let i' : fin compo.max_index := ⟨i, h⟩,
    have : compo.size_up_to (i + 1) = compo.size_up_to i + compo.size i' :=
      compo.size_up_to_succ i',
    rw [this, size, IH (le_of_lt h)],
    apply nat.add_sub_cancel',
    apply (finset.mono_of_fin_strict_mono compo.boundaries rfl).monotone,
    exact nat.le_succ _ }
end

lemma size_up_to_max_index : compo.size_up_to compo.max_index = n :=
begin
  have : (compo.boundaries.max' compo.boundaries_nonempty : ℕ) = n,
  { change ((finset.max' compo.boundaries compo.boundaries_nonempty : fin n.succ) : ℕ) = fin.last n,
    apply congr_arg,
    refine le_antisymm (fin.le_last _) _,
    exact finset.le_max' _ compo.boundaries_nonempty _ compo.last_mem },
  conv_rhs { rw ← this },
  rw compo.size_up_to_eq _ (le_refl _),
  apply congr_arg,
  exact finset.mono_of_fin_last rfl compo.boundaries_nonempty compo.card_boundaries_pos
end

lemma size_up_to_of_max_index_le {i : ℕ} (hi : compo.max_index ≤ i) :
  compo.size_up_to i = n :=
begin
  have : compo.size_up_to i = compo.size_up_to compo.max_index,
  { dsimp [size_up_to],
    have A : ∀ (j : fin (max_index compo)), j.val < max_index compo := λ j, j.2,
    have B : ∀ (j : fin (max_index compo)), j.val < i := λ j, lt_of_lt_of_le j.2 hi,
    simp [A, B] },
  simpa [compo.size_up_to_max_index] using this
end

lemma sum_size : finset.univ.sum compo.size = n :=
begin
  conv_rhs { rw ← compo.size_up_to_max_index },
  dsimp [size_up_to],
  congr' 1,
  ext i,
  simp [i.2]
end

/-- An element belongs to a composition if and only if it can be written as a sum of sizes
of blocks. -/
lemma mem_boundaries_iff_size_up_to_image (i : fin n.succ) :
  i ∈ compo.boundaries ↔ i.val ∈ set.range compo.size_up_to :=
begin
  split,
  { assume h,
    have := (finset.bij_on_mono_of_fin compo.boundaries rfl).surj_on h,
    simp only [set.image_univ, set.mem_range] at this,
    rcases this with ⟨j, hj⟩,
    rw set.mem_range,
    refine ⟨j.val, _⟩,
    rw compo.size_up_to_eq j.1 (compo.lt_card_boundaries_iff.1 j.2),
    rw fin.ext_iff at hj,
    exact hj },
  { assume h,
    have : ∃ j, j ≤ compo.max_index ∧ i.val = compo.size_up_to j,
    { rcases set.mem_range.1 h with ⟨j0, hj0⟩,
      by_cases hj : j0 ≤ compo.max_index,
      { exact ⟨j0, hj, hj0.symm⟩ },
      { refine ⟨compo.max_index, le_refl _, _⟩,
        rw [compo.size_up_to_max_index, ← hj0, compo.size_up_to_of_max_index_le],
        exact le_of_not_ge hj } },
    rcases this with ⟨j, j_le, hj⟩,
    rw [compo.size_up_to_eq _ j_le, ← fin.ext_iff] at hj,
    rw hj,
    exact (finset.bij_on_mono_of_fin compo.boundaries rfl).maps_to (set.mem_univ _) }
end

/-- If two compositions (possibly with varying `n`) have the same function `size_up_to`, then
they coincide. The interest of this formulation is that the type of the function `size_up_to` does
not depend on `n`, avoiding dependent type issues. -/
lemma eq_of_size_up_to_eq (a b : Σ n, composition n) (h : a.2.size_up_to = b.2.size_up_to) :
  a = b :=
begin
  rcases a with ⟨n, compo⟩,
  rcases b with ⟨n', compo'⟩,
  have : n' = n,
  { have A : compo.size_up_to (max compo.max_index compo'.max_index) = n :=
      compo.size_up_to_of_max_index_le (le_max_left _ _),
    have B : compo'.size_up_to (max compo.max_index compo'.max_index) = n' :=
      compo'.size_up_to_of_max_index_le (le_max_right _ _),
    rwa [h, B] at A },
  induction this,
  have : compo.boundaries = compo'.boundaries,
    by { ext i, simp only [mem_boundaries_iff_size_up_to_image, h] },
  tidy
end

/-- Given a composition `compo`, and its `index`-th block, of size `compo.size index`, then
`compo.embedding index` is the increasing map from `fin (compo.size index)` to `fin n` with image
the `index`-th block. -/
def embedding (index : fin compo.max_index) : fin (compo.size index) → fin n :=
λ j, ⟨compo.size_up_to index + j.val,
  calc compo.size_up_to index + j.val
  < compo.size_up_to index + compo.size index : add_lt_add_left j.2 _
  ... = compo.size_up_to (index + 1) : (compo.size_up_to_succ _).symm
  ... ≤ n :
    by { conv_rhs { rw ← compo.size_up_to_max_index }, exact compo.size_up_to_mono index.2 } ⟩

lemma embedding_inj (index : fin compo.max_index) : function.injective (compo.embedding index) :=
λ a b hab, by simpa [embedding, fin.ext_iff] using hab

lemma index_exists {j : ℕ} (h : j < n) :
  ∃ i : ℕ, j < compo.size_up_to i.succ ∧ i < compo.max_index :=
begin
  have n_pos : 0 < n := lt_of_le_of_lt (zero_le j) h,
  have max_index_pos : 0 < compo.max_index,
  { by_contradiction H,
    simp only [le_zero_iff_eq, not_lt] at H,
    have : (finset.univ : finset (fin compo.max_index)) = ∅,
    { ext j,
      have : j.val < 0, by { convert j.2, exact H.symm },
      exact false.elim (nat.not_succ_le_zero j.val this) },
    have A := compo.size_up_to_max_index,
    simp [this, size_up_to] at A,
    exact ne_of_lt n_pos A },
  refine ⟨compo.max_index.pred, _, nat.pred_lt (ne_of_gt max_index_pos)⟩,
  have : compo.max_index.pred.succ = compo.max_index := nat.succ_pred_eq_of_pos max_index_pos,
  rw ← compo.size_up_to_max_index at h,
  simp [this, h]
end

/-- `compo.index j` is the index of the block in the composition `compo` containing `j`. -/
def index (j : fin n) : fin compo.max_index :=
⟨nat.find (compo.index_exists j.2), (nat.find_spec (compo.index_exists j.2)).2⟩

lemma lt_size_up_to_index_succ (j : fin n) : j.val < compo.size_up_to (compo.index j).succ :=
(nat.find_spec (compo.index_exists j.2)).1

lemma size_up_to_index_le (j : fin n) : compo.size_up_to (compo.index j) ≤ j :=
begin
  by_contradiction H,
  set i := compo.index j with hi,
  push_neg at H,
  have i_pos : (0 : ℕ) < i,
  { by_contradiction i_pos,
    push_neg at i_pos,
    simp [le_zero_iff_eq.mp i_pos, compo.size_up_to_zero] at H,
    exact nat.not_succ_le_zero j H },
  let i₁ := (i : ℕ).pred,
  have i₁_lt_i : i₁ < i := nat.pred_lt (ne_of_gt i_pos),
  have i₁_succ : i₁.succ = i := nat.succ_pred_eq_of_pos i_pos,
  have := nat.find_min (compo.index_exists j.2) i₁_lt_i,
  simp [lt_trans i₁_lt_i (compo.index j).2, i₁_succ] at this,
  exact nat.lt_le_antisymm H this
end

/-- Mapping an element `j` of `fin n` to the element in the block containing it, identified with
`fin (compo.size (compo.index j))` through the canonical increasing bijection. -/
def inv_embedding (j : fin n) : fin (compo.size (compo.index j)) :=
⟨j - compo.size_up_to (compo.index j),
begin
  rw [nat.sub_lt_right_iff_lt_add, add_comm, ← size_up_to_succ],
  { exact lt_size_up_to_index_succ _ _ },
  { exact size_up_to_index_le _ _ }
end⟩

lemma embedding_comp_inv (j : fin n) :
  j = compo.embedding (compo.index j) (compo.inv_embedding j) :=
begin
  rw fin.ext_iff,
  apply (nat.add_sub_cancel' (compo.size_up_to_index_le j)).symm,
end

lemma mem_range_embedding_iff {j : fin n} {i : fin compo.max_index} :
  j ∈ set.range (compo.embedding i) ↔
  compo.size_up_to i ≤ j ∧ (j : ℕ) < compo.size_up_to (i : ℕ).succ :=
begin
  split,
  { assume h,
    rcases set.mem_range.2 h with ⟨k, hk⟩,
    rw fin.ext_iff at hk,
    change compo.size_up_to i + k.val = (j : ℕ) at hk,
    rw ← hk,
    simp [size_up_to_succ, k.2] },
  { assume h,
    apply set.mem_range.2,
    refine ⟨⟨j.val - compo.size_up_to i, _⟩, _⟩,
    { rw [nat.sub_lt_left_iff_lt_add, ← size_up_to_succ],
      { exact h.2 },
      { exact h.1 } },
    { rw fin.ext_iff,
      exact nat.add_sub_cancel' h.1 } }
end

/-- The embeddings of different blocks of a composition are dijoint. -/
lemma disjoint_range {i₁ i₂ : fin compo.max_index} (h : i₁ ≠ i₂) :
  disjoint (set.range (compo.embedding i₁)) (set.range (compo.embedding i₂)) :=
begin
  classical,
  wlog h' : i₁ ≤ i₂ using i₁ i₂,
  { by_contradiction d,
    obtain ⟨x, hx₁, hx₂⟩ :
      ∃ x : fin n, (x ∈ set.range (compo.embedding i₁) ∧ x ∈ set.range (compo.embedding i₂)) :=
    set.not_disjoint_iff.1 d,
    have : i₁ < i₂ := lt_of_le_of_ne h' h,
    have A : (i₁ : ℕ).succ ≤ i₂ := nat.succ_le_of_lt this,
    apply lt_irrefl (x : ℕ),
    calc (x : ℕ) < compo.size_up_to (i₁ : ℕ).succ : (compo.mem_range_embedding_iff.1 hx₁).2
    ... ≤ compo.size_up_to (i₂ : ℕ) : compo.size_up_to_mono A
    ... ≤ x : (compo.mem_range_embedding_iff.1 hx₂).1 },
  { rw disjoint.comm,
    apply this (ne.symm h) }
end

lemma mem_range_embedding (j : fin n) :
  j ∈ set.range (compo.embedding (compo.index j)) :=
begin
  have : compo.embedding (compo.index j) (compo.inv_embedding j)
    ∈ set.range (compo.embedding (compo.index j)) := set.mem_range_self _,
  rwa ← compo.embedding_comp_inv j at this
end

lemma mem_range_embedding_iff' {j : fin n} {i : fin compo.max_index} :
  j ∈ set.range (compo.embedding i) ↔ i = compo.index j :=
begin
  split,
  { rw ← not_imp_not,
    assume h,
    exact set.disjoint_right.1 (compo.disjoint_range h) (compo.mem_range_embedding j) },
  { assume h,
    rw h,
    exact compo.mem_range_embedding j }
end

/-- From a `size` function on `fin k`, construct a composition of the integer
`finset.univ.sum size`, whose blocks have a size given by `size`. -/
def of_size {k : ℕ} (size : fin k → ℕ) : composition (finset.univ.sum size) :=
begin
  let n := finset.univ.sum size,
  let F : ℕ → fin n.succ := λ i,
    ⟨finset.sum ((finset.univ : finset (fin k)).filter (λ (j : fin k), j.val < i)) size,
      by { rw [nat.lt_succ_iff], exact finset.sum_le_sum_of_subset (finset.subset_univ _) }⟩,
  refine ⟨finset.image F (finset.range k.succ), _, _⟩,
  { have A : ∀ (j : fin k), ¬ (j.val < 0) := λ j, not_lt_bot,
    rw finset.mem_image,
    exact ⟨0, by simp [F, fin.ext_iff, A]⟩ },
  { rw finset.mem_image,
    have A : ∀ (j : fin k), j.val < k := λ j, j.2,
    refine ⟨k, by simp [F, A, fin.ext_iff, lt_add_one k]⟩ }
end

lemma of_size_strict_mono {k : ℕ} {size : fin k → ℕ}
  (h' : ∀ i, 0 < size i) {i j : ℕ} (ij : i < j) (jk : j < k.succ) :
  finset.sum (finset.filter (λ (a : fin k), a.val < i) finset.univ) size
      < finset.sum (finset.filter (λ (a : fin k), a.val < j) finset.univ) size :=
begin
  have ik : i < k := lt_of_lt_of_le ij (nat.lt_succ_iff.mp jk),
  have : (⟨i, ik⟩ : fin k) ∈ (finset.filter (λ (a : fin k), a.val < j) finset.univ)
    \ (finset.filter (λ (a : fin k), a.val < i) finset.univ), by simp [finset.mem_sdiff, ij],
  apply finset.sum_lt_sum_of_subset _ this (h' _) (λ a ha, bot_le),
  assume a ha,
  simp only [true_and, finset.mem_univ, finset.mem_filter] at ha ⊢,
  exact lt_trans ha ij
end

/-- The number of blocks in a composition constructed from a `size` function with `k` terms
is precisely `k`. -/
lemma of_size_max_index {k : ℕ} {size : fin k → ℕ} (h' : ∀ i, 0 < size i) :
  (of_size size).max_index = k :=
begin
  dsimp [max_index, of_size],
  rw finset.card_image_of_inj_on,
  { simp },
  { assume i hi j hj hij,
    rw fin.ext_iff at hij,
    wlog hle : i ≤ j,
    by_contradiction hne,
    have ij : i < j := lt_of_le_of_ne hle hne,
    exact ne_of_lt (of_size_strict_mono h' ij (list.mem_range.mp hj)) hij }
end

lemma of_size_size_up_to {k : ℕ} {size : fin k → ℕ} (h' : ∀ i, 0 < size i) (i : ℕ) :
  size_up_to (of_size size) i =
  finset.sum (finset.filter (λ (a : fin k), a.val < i) finset.univ) size :=
begin
  let n := finset.univ.sum size,
  let compo := of_size size,
  have k_succ : k.succ = finset.card compo.boundaries,
  { conv_lhs { rw ← of_size_max_index h' },
    exact pnat.to_pnat'_coe compo.card_boundaries_pos },
  let F : ℕ → fin n.succ := λ i,
    ⟨finset.sum ((finset.univ : finset (fin k)).filter (λ (j : fin k), j.val < i)) size,
      by { rw [nat.lt_succ_iff], exact finset.sum_le_sum_of_subset (finset.subset_univ _) }⟩,
  have GF : finset.mono_of_fin compo.boundaries rfl = (λ i, F i.val),
  { symmetry,
    apply finset.mono_of_fin_unique',
    { assume i hi,
      simp only [compo, of_size, -set.mem_image, set.mem_image_of_mem, set.mem_preimage,
                 finset.coe_image],
      apply set.mem_image_of_mem,
      simp only [finset.mem_range, finset.mem_coe],
      convert i.2 },
    { assume i j hij,
      apply of_size_strict_mono h' hij,
      rw k_succ,
      exact j.2 } },
  by_cases hi : i ≤ k,
  { rw [size_up_to_eq, GF],
    rwa of_size_max_index h' },
  { have : ∀ (a : fin k), a.val < i := λ a, lt_trans a.2 (not_le.mp hi),
    simp only [this, finset.filter_true, finset.filter_congr_decidable],
    rw [size_up_to_of_max_index_le],
    rw [of_size_max_index h'],
    exact le_of_not_ge hi }
end

/-- In a composition constructed from a `size` function, the size of the blocks is precisely
given by `size`. -/
lemma of_size_size {k : ℕ} {size : fin k → ℕ} (h' : ∀ i, 0 < size i) (i : fin k) :
  size i = (of_size size).size ⟨i.val, lt_of_lt_of_le i.2 (le_of_eq (of_size_max_index h').symm)⟩ :=
begin
  let compo := of_size size,
  let i' : fin compo.max_index :=
    ⟨i.val, lt_of_lt_of_le i.2 (le_of_eq (of_size_max_index h').symm)⟩,
  have A := compo.size_up_to_succ i',
  rw [of_size_size_up_to h', of_size_size_up_to h'] at A,
  have : ((finset.univ : finset (fin k)).filter (λ (j : fin k), j.val < i' + 1))
    = ((finset.univ : finset (fin k)).filter (λ (j : fin k), j.val < i')) ∪ {i},
    by { ext j, simp [nat.lt_succ_iff_lt_or_eq, fin.ext_iff, - add_comm] },
  rw [this, finset.sum_union] at A,
  { simpa using A },
  { simp }
end

/-- If two `size` functions give rise to the same composition, then they coincide. -/
lemma of_size_inj {k k' : ℕ} {size : fin k → ℕ} {size' : fin k' → ℕ}
  (h : ∀ i, 0 < size i) (h' : ∀ i, 0 < size' i)
  (H : (⟨finset.univ.sum size, of_size size⟩ : Σ n, composition n) =
    ⟨finset.univ.sum size', of_size size'⟩) :
  (⟨k, size⟩ : Σ k, fin k → ℕ) = ⟨k', size'⟩ :=
begin
  have : k' = k,
  { let F : (Σ n, composition n) → ℕ := λ a, a.2.max_index,
    have A : F ⟨finset.univ.sum size, of_size size⟩ = k := of_size_max_index h,
    have B : F ⟨finset.univ.sum size', of_size size'⟩ = k' := of_size_max_index h',
    rwa [H, B] at A },
  induction this,
  suffices H' : size = size', by simp [H'],
  ext i,
  let F : (Σ n, composition n) → ℕ :=
    λ a, if hi : i.val < a.2.max_index then a.2.size ⟨i.val, hi⟩ else 0,
  have A : size i = F ⟨_, of_size size⟩,
  { have : i.val < max_index (of_size size), by { rw of_size_max_index h, exact i.2 },
    simp [F, this],
    exact of_size_size h i },
  have B : size' i = F ⟨_, of_size size'⟩,
  { have : i.val < max_index (of_size size'), by { rw of_size_max_index h', exact i.2 },
    simp [F, this],
    exact of_size_size h' i },
  rw [A, B, H]
end

/-- Starting from a composition `compo`, and constructing a new composition from the
size function `compo.size`, gives back `compo`. -/
lemma of_size_eq_self {n : ℕ} (compo : composition n) :
  (⟨n, compo⟩ : Σ n, composition n) =
  ⟨finset.univ.sum compo.size, composition.of_size compo.size⟩ :=
begin
  have : n = finset.univ.sum compo.size := compo.sum_size.symm,
  apply eq_of_size_up_to_eq,
  ext i,
  simp [of_size_size_up_to, compo.size_pos],
  refl
end

end composition
