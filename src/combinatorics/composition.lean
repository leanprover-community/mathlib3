/-
Copyright (c) 2020 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/

import data.fintype.card tactic.omega

/-!
# Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers. Combinatorially, it corresponds to a decomposition of `{0, ..., n-1}` into
non-empty blocks of consecutive integers, where the `iⱼ` are the lengths of the blocks.
This notion is closely related to that of a partition of `n`, but in a composition of `n` the
order of the `iⱼ`s matters.

We implement two different structures covering these two viewpoints on compositions. The first
one, made of a list of positive integers summing to `n`, is the main one and is called
`composition n`. The second one is useful for combinatorial arguments (for instance to show that
the number of compositions of `n` is `2^(n-1)`). It is given by a subset of `{0, ..., n}`
containing `0` and `n`, where the elements of the subset (other than `n`) correspond to the leftmost
points of each block. The main API is built on `composition n`, and we provide an equivalence
between the two types.

## Main functions

* `c : composition n` is a structure, made of a list of positive integers summing to `n`.
* `composition_card` states that the cardinality of `composition n` is exactly
  `2^(n-1)`, which is proved by constructing an equiv with `composition_as_set n` (see below), which
  is itself in bijection with the subsets of `fin (n-1)` (this holds even for `n = 0`, where `-` is
  nat subtraction).

Let `c : composition n` be a composition of `n`. Then
* `c.blocks_pnat` is the list of blocks in `c`, as positive integers
* `c.blocks` is the list of blocks in `c`, as elements of `ℕ`
* `c.length` is the number of blocks in the composition;
* `c.blocks_fun : fin c.length → ℕ` is the realization of `c.blocks` as a function on
  `fin c.length`. This is the main object when using compositions to understand the composition of
    analytic functions.
* `c.size_up_to : ℕ → ℕ` is the sum of the size of the blocks up to `i`.;
* `c.embedding i : fin (c.blocks_fun i) → fin n` is the increasing embedding of the `i`-th block in
  `fin n`;
* `c.index j`, for `j : fin n`, is the index of the block containing `j`.

We turn to the second viewpoint on compositions, that we realize as a finset of `fin (n+1)`.
`c : composition_as_set n` is a structure made of a finset of `fin (n+1)` called `c.boundaries`
and proofs that it contains `0` and `n`. (Taking a finset of `fin n` containing `0` would not
make sense in the edge case `n = 0`, while the previous description works in all cases).
The elements of this set (other than `n`) correspond to leftmost points of blocks.
Thus, there is an equiv between `composition n` and `composition_as_set n`. We
only construct basic API on `composition_as_set` (notably `c.length` and `c.blocks`) to be able
to construct this equiv, called `composition_equiv n`. Since there is a straightforward equiv
between `composition_as_set n` and finsets of `{1, ..., n-1}` (obtained by removing `0` and `n`
from a `composition_as_set` and called `composition_as_set_equiv n`), we deduce that
`composition_as_set n` and `composition n` are both fintypes of cardinality `2^(n - 1)`
(see `composition_as_set_card` and `composition_card`).

## Implementation details

The main motivation for this structure and its API is in the construction of the composition of
formal multilinear series, and the proof that the composition of analytic functions is analytic.

The representation of a composition as a list is very handy as lists are very flexible and already
have a well-developed API.

## Tags

Composition, partition

## References

<https://en.wikipedia.org/wiki/Composition_(combinatorics)>
-/

open list
open_locale classical

variable {n : ℕ}

/-- A composition of `n` is a list of positive integers summing to `n`. -/
@[ext] structure composition (n : ℕ) :=
(blocks_pnat : list ℕ+)
(blocks_pnat_sum : (blocks_pnat.map (λ n : ℕ+, (n : ℕ))).sum = n)

instance {n : ℕ} : inhabited (composition n) :=
⟨⟨repeat (1 : ℕ+) n, (by simp)⟩⟩

/-- Combinatorial viewpoint on a composition of `n`, by seeing it as non-empty blocks of
consecutive integers in `{0, ..., n-1}`. We register every block by its left end-point, yielding
a finset containing `0`. As this does not make sense for `n = 0`, we add `n` to this finset, and
get a finset of `{0, ..., n}` containing `0` and `n`. This is the data in the structure
`composition_as_set n`. -/
@[ext] structure composition_as_set (n : ℕ) :=
(boundaries : finset (fin n.succ))
(zero_mem   : (0 : fin n.succ) ∈ boundaries)
(last_mem   : (fin.last n ∈ boundaries))

instance {n : ℕ} : inhabited (composition_as_set n) :=
⟨⟨finset.univ, finset.mem_univ _, finset.mem_univ _⟩⟩

/-!
### Compositions

A composition of an integer `n` is a decomposition `n = i₀ + ... + i_{k-1}` of `n` into a sum of
positive integers.
-/

namespace composition

variables (c : composition n)

/-- The list of blocks in a composition, as natural numbers. -/
def blocks : list ℕ := c.blocks_pnat.map (λ n : ℕ+, (n : ℕ))

lemma blocks_sum : c.blocks.sum = n := c.blocks_pnat_sum

/-- The length of a composition, i.e., the number of blocks in the composition. -/
def length : ℕ := c.blocks.length

@[simp] lemma blocks_length : c.blocks.length = c.length := rfl

@[simp] lemma blocks_pnat_length : c.blocks_pnat.length = c.length :=
by rw [← c.blocks_length, blocks, length_map]

/-- The blocks of a composition, seen as a function on `fin c.length`. When composing analytic
functions using compositions, this is the main player. -/
def blocks_fun : fin c.length → ℕ := λ i, nth_le c.blocks i.1 i.2

lemma sum_blocks_fun : finset.univ.sum c.blocks_fun = n :=
begin
  conv_rhs { rw [← c.blocks_sum, ← of_fn_nth_le c.blocks, of_fn_sum] },
  simp [blocks_fun, length],
  refl
end

@[simp] lemma one_le_blocks {i : ℕ} (h : i ∈ c.blocks) : 1 ≤ i :=
begin
  simp only [mem_map, blocks] at h,
  rcases h with ⟨h, ha, rfl⟩,
  exact h.2
end

@[simp] lemma blocks_pos {i : ℕ} (h : i ∈ c.blocks) : 0 < i :=
c.one_le_blocks h

@[simp] lemma one_le_blocks' {i : ℕ} (h : i < c.length) : 1 ≤ nth_le c.blocks i h:=
c.one_le_blocks (nth_le_mem (blocks c) i h)

@[simp] lemma blocks_pos' (i : ℕ) (h : i < c.length) : 0 < nth_le c.blocks i h:=
c.one_le_blocks' h

lemma length_le : c.length ≤ n :=
begin
  conv_rhs { rw ← c.blocks_sum },
  exact length_le_sum_of_one_le _ (λ i hi, c.one_le_blocks hi)
end

lemma length_pos_of_pos (h : 0 < n) : 0 < c.length :=
begin
  apply length_pos_of_sum_pos,
  convert h,
  exact c.blocks_sum
end

/-- The sum of the sizes of the blocks in a composition up to `i`. -/
def size_up_to (i : ℕ) : ℕ := (c.blocks.take i).sum

@[simp] lemma size_up_to_zero : c.size_up_to 0 = 0 := by simp [size_up_to]

lemma size_up_to_of_length_le (i : ℕ) (h : c.length ≤ i) : c.size_up_to i = n :=
begin
  dsimp [size_up_to],
  convert c.blocks_sum,
  exact take_all_of_le h
end

@[simp] lemma size_up_to_length : c.size_up_to c.length = n :=
c.size_up_to_of_length_le c.length (le_refl _)

lemma size_up_to_le (i : ℕ) : c.size_up_to i ≤ n :=
begin
  conv_rhs { rw [← c.blocks_sum, ← sum_take_add_sum_drop _ i] },
  exact nat.le_add_right _ _
end

lemma size_up_to_succ {i : ℕ} (h : i < c.length) :
  c.size_up_to (i+1) = c.size_up_to i + c.blocks.nth_le i h :=
by { simp only [size_up_to], rw sum_take_succ _ _ h }

lemma size_up_to_succ' (i : fin c.length) :
  c.size_up_to ((i : ℕ) + 1) = c.size_up_to i + c.blocks_fun i :=
c.size_up_to_succ i.2

lemma size_up_to_strict_mono {i : ℕ} (h : i < c.length) : c.size_up_to i < c.size_up_to (i+1) :=
by { rw c.size_up_to_succ h, simp }

/-- The `i`-th boundary of a composition, i.e., the leftmost point of the `i`-th block. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundary : fin (c.length + 1) → fin (n+1) :=
λ i, ⟨c.size_up_to i, nat.lt_succ_of_le (c.size_up_to_le i)⟩

@[simp] lemma boundary_zero : c.boundary 0 = 0 :=
by simp [boundary, fin.ext_iff]

@[simp] lemma boundary_last : c.boundary (fin.last c.length) = fin.last n :=
by simp [boundary, fin.ext_iff]

lemma strict_mono_boundary : strict_mono c.boundary :=
begin
  apply fin.strict_mono_iff_lt_succ.2 (λ i hi, _),
  exact c.size_up_to_strict_mono ((add_lt_add_iff_right 1).mp hi)
end

/-- The boundaries of a composition, i.e., the leftmost point of all the blocks. We include
a virtual point at the right of the last block, to make for a nice equiv with
`composition_as_set n`. -/
def boundaries : finset (fin (n+1)) :=
finset.univ.image c.boundary

lemma card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
begin
  dsimp [boundaries],
  rw finset.card_image_of_injective finset.univ c.strict_mono_boundary.injective,
  simp
end

/-- To `c : composition n`, one can associate a `composition_as_set n` by registering the leftmost
point of each block, and adding a virtual point at the right of the last block. -/
def to_composition_as_set : composition_as_set n :=
{ boundaries := c.boundaries,
  zero_mem := begin
    simp only [boundaries, finset.mem_univ, exists_prop_of_true, finset.mem_image],
    exact ⟨0, rfl⟩,
  end,
  last_mem := begin
    simp only [boundaries, finset.mem_univ, exists_prop_of_true, finset.mem_image],
    exact ⟨fin.last c.length, c.boundary_last⟩,
  end }

/-- The canonical increasing bijection between `fin (c.length + 1)` and `c.boundaries` is
exactly `c.boundary`. -/
lemma mono_of_fin_boundaries :
  c.boundary = finset.mono_of_fin c.boundaries c.card_boundaries_eq_succ_length :=
begin
  apply finset.mono_of_fin_unique' _ _ c.strict_mono_boundary,
  assume i hi,
  simp [boundaries, - set.mem_range, set.mem_range_self]
end

/-- Embedding the `i`-th block of a composition (identified with `fin (c.blocks_fun i)`) into
`fin n` at the relevant position. -/
def embedding (i : fin c.length) : fin (c.blocks_fun i) → fin n :=
λ j, ⟨c.size_up_to i.1 + j.val,
  calc c.size_up_to i.1 + j.val
  < c.size_up_to i.1 + c.blocks.nth_le i.1 i.2 : add_lt_add_left j.2 _
  ... = c.size_up_to (i.1 + 1) : (c.size_up_to_succ _).symm
  ... ≤ n :
    by { conv_rhs { rw ← c.size_up_to_length }, exact monotone_sum_take _ i.2 } ⟩

lemma embedding_inj (i : fin c.length) : function.injective (c.embedding i) :=
λ a b hab, by simpa [embedding, fin.ext_iff] using hab

/--
`index_exists` asserts there is some `i` so `j < c.size_up_to (i+1)`.
In the next definition we use `nat.find` to produce the minimal such index.
-/
lemma index_exists {j : ℕ} (h : j < n) :
  ∃ i : ℕ, j < c.size_up_to i.succ ∧ i < c.length :=
begin
  have n_pos : 0 < n := lt_of_le_of_lt (zero_le j) h,
  have : 0 < c.blocks.sum, by rwa [← c.blocks_sum] at n_pos,
  have length_pos : 0 < c.blocks.length := length_pos_of_sum_pos (blocks c) this,
  refine ⟨c.length.pred, _, nat.pred_lt (ne_of_gt length_pos)⟩,
  have : c.length.pred.succ = c.length := nat.succ_pred_eq_of_pos length_pos,
  simp [this, h]
end

/-- `c.index j` is the index of the block in the composition `c` containing `j`. -/
def index (j : fin n) : fin c.length :=
⟨nat.find (c.index_exists j.2), (nat.find_spec (c.index_exists j.2)).2⟩

lemma lt_size_up_to_index_succ (j : fin n) : j.val < c.size_up_to (c.index j).succ :=
(nat.find_spec (c.index_exists j.2)).1

lemma size_up_to_index_le (j : fin n) : c.size_up_to (c.index j) ≤ j :=
begin
  by_contradiction H,
  set i := c.index j with hi,
  push_neg at H,
  have i_pos : (0 : ℕ) < i,
  { by_contradiction i_pos,
    push_neg at i_pos,
    simp [le_zero_iff_eq.mp i_pos, c.size_up_to_zero] at H,
    exact nat.not_succ_le_zero j H },
  let i₁ := (i : ℕ).pred,
  have i₁_lt_i : i₁ < i := nat.pred_lt (ne_of_gt i_pos),
  have i₁_succ : i₁.succ = i := nat.succ_pred_eq_of_pos i_pos,
  have := nat.find_min (c.index_exists j.2) i₁_lt_i,
  simp [lt_trans i₁_lt_i (c.index j).2, i₁_succ] at this,
  exact nat.lt_le_antisymm H this
end

/-- Mapping an element `j` of `fin n` to the element in the block containing it, identified with
`fin (c.blocks_fun (c.index j))` through the canonical increasing bijection. -/
def inv_embedding (j : fin n) : fin (c.blocks_fun (c.index j)) :=
⟨j - c.size_up_to (c.index j),
begin
  rw [nat.sub_lt_right_iff_lt_add, add_comm, ← size_up_to_succ'],
  { exact lt_size_up_to_index_succ _ _ },
  { exact size_up_to_index_le _ _ }
end⟩

lemma embedding_comp_inv (j : fin n) :
  j = c.embedding (c.index j) (c.inv_embedding j) :=
begin
  rw fin.ext_iff,
  apply (nat.add_sub_cancel' (c.size_up_to_index_le j)).symm,
end

lemma mem_range_embedding_iff {j : fin n} {i : fin c.length} :
  j ∈ set.range (c.embedding i) ↔
  c.size_up_to i ≤ j ∧ (j : ℕ) < c.size_up_to (i : ℕ).succ :=
begin
  split,
  { assume h,
    rcases set.mem_range.2 h with ⟨k, hk⟩,
    rw fin.ext_iff at hk,
    change c.size_up_to i + k.val = (j : ℕ) at hk,
    rw ← hk,
    simp [size_up_to_succ', k.2] },
  { assume h,
    apply set.mem_range.2,
    refine ⟨⟨j.val - c.size_up_to i, _⟩, _⟩,
    { rw [nat.sub_lt_left_iff_lt_add, ← size_up_to_succ'],
      { exact h.2 },
      { exact h.1 } },
    { rw fin.ext_iff,
      exact nat.add_sub_cancel' h.1 } }
end

/-- The embeddings of different blocks of a composition are disjoint. -/
lemma disjoint_range {i₁ i₂ : fin c.length} (h : i₁ ≠ i₂) :
  disjoint (set.range (c.embedding i₁)) (set.range (c.embedding i₂)) :=
begin
  classical,
  wlog h' : i₁ ≤ i₂ using i₁ i₂,
  { by_contradiction d,
    obtain ⟨x, hx₁, hx₂⟩ :
      ∃ x : fin n, (x ∈ set.range (c.embedding i₁) ∧ x ∈ set.range (c.embedding i₂)) :=
    set.not_disjoint_iff.1 d,
    have : i₁ < i₂ := lt_of_le_of_ne h' h,
    have A : (i₁ : ℕ).succ ≤ i₂ := nat.succ_le_of_lt this,
    apply lt_irrefl (x : ℕ),
    calc (x : ℕ) < c.size_up_to (i₁ : ℕ).succ : (c.mem_range_embedding_iff.1 hx₁).2
    ... ≤ c.size_up_to (i₂ : ℕ) : monotone_sum_take _ A
    ... ≤ x : (c.mem_range_embedding_iff.1 hx₂).1 },
  { rw disjoint.comm,
    apply this (ne.symm h) }
end

lemma mem_range_embedding (j : fin n) :
  j ∈ set.range (c.embedding (c.index j)) :=
begin
  have : c.embedding (c.index j) (c.inv_embedding j)
    ∈ set.range (c.embedding (c.index j)) := set.mem_range_self _,
  rwa ← c.embedding_comp_inv j at this
end

lemma mem_range_embedding_iff' {j : fin n} {i : fin c.length} :
  j ∈ set.range (c.embedding i) ↔ i = c.index j :=
begin
  split,
  { rw ← not_imp_not,
    assume h,
    exact set.disjoint_right.1 (c.disjoint_range h) (c.mem_range_embedding j) },
  { assume h,
    rw h,
    exact c.mem_range_embedding j }
end

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks of positive integers. -/
lemma sigma_eq_iff_blocks_pnat_eq {c : Σ n, composition n} {c' : Σ n, composition n} :
  c = c' ↔ c.2.blocks_pnat = c'.2.blocks_pnat :=
begin
  refine ⟨λ H, by rw H, λ H, _⟩,
  rcases c with ⟨n, c⟩,
  rcases c' with ⟨n', c'⟩,
  have : n = n', by { rw [← c.blocks_pnat_sum, ← c'.blocks_pnat_sum, H] },
  induction this,
  simp only [true_and, eq_self_iff_true, heq_iff_eq],
  ext1,
  exact H
end

/-- Two compositions (possibly of different integers) coincide if and only if they have the
same sequence of blocks. -/
lemma sigma_eq_iff_blocks_eq {c : Σ n, composition n} {c' : Σ n, composition n} :
  c = c' ↔ c.2.blocks = c'.2.blocks :=
begin
  refine ⟨λ H, by rw H, λ H, _⟩,
  rwa [sigma_eq_iff_blocks_pnat_eq, ← (injective_map_iff.2 subtype.val_injective).eq_iff]
end

end composition


/-!
### Compositions as sets

Combinatorial viewpoints on compositions, seen as finite subsets of `fin (n+1)` containing `0` and
`n`, where the points of the set (other than `n`) correspond to the leftmost points of each block.
-/

/-- Bijection between compositions of `n` and subsets of `{0, ..., n-2}`, defined by
considering the restriction of the subset to `{1, ..., n-1}` and shifting to the left by one. -/
def composition_as_set_equiv (n : ℕ) : composition_as_set n ≃ finset (fin (n - 1)) :=
{ to_fun := λ c, {i : fin (n-1) |
    (⟨1 + i.val, by { have := i.2, omega }⟩ : fin n.succ) ∈ c.boundaries}.to_finset,
  inv_fun := λ s,
    { boundaries := {i : fin n.succ | (i = 0) ∨ (i = fin.last n)
        ∨ (∃ (j : fin (n-1)) (hj : j ∈ s), i.val = j.val + 1)}.to_finset,
      zero_mem   := by simp,
      last_mem   := by simp },
  left_inv := begin
    assume c,
    ext i,
    simp only [exists_prop, add_comm, set.mem_to_finset, true_or, or_true, set.mem_set_of_eq,
               fin.last_val],
    split,
    { rintro (rfl | rfl | ⟨j, hj1, hj2⟩),
      { exact c.zero_mem },
      { exact c.last_mem },
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

instance composition_as_set_fintype (n : ℕ) : fintype (composition_as_set n) :=
fintype.of_equiv _ (composition_as_set_equiv n).symm

lemma composition_as_set_card (n : ℕ) : fintype.card (composition_as_set n) = 2 ^ (n - 1) :=
begin
  have : fintype.card (finset (fin (n-1))) = 2 ^ (n - 1), by simp,
  rw ← this,
  exact fintype.card_congr (composition_as_set_equiv n)
end

namespace composition_as_set

variables (c : composition_as_set n)

lemma boundaries_nonempty : c.boundaries.nonempty :=
⟨0, c.zero_mem⟩

lemma card_boundaries_pos : 0 < finset.card c.boundaries :=
finset.card_pos.mpr c.boundaries_nonempty

/-- Number of blocks in a `composition_as_set`. -/
def length : ℕ := finset.card c.boundaries - 1

lemma card_boundaries_eq_succ_length : c.boundaries.card = c.length + 1 :=
(nat.sub_eq_iff_eq_add c.card_boundaries_pos).mp rfl

lemma length_lt_card_boundaries : c.length < c.boundaries.card :=
by { rw c.card_boundaries_eq_succ_length, exact lt_add_one _ }

lemma lt_length (i : fin c.length) : i.val + 1 < c.boundaries.card :=
nat.add_lt_of_lt_sub_right i.2

lemma lt_length' (i : fin c.length) : i.val < c.boundaries.card :=
lt_of_le_of_lt (nat.le_succ i.val) (c.lt_length i)

/-- Canonical increasing bijection from `fin c.boundaries.card` to `c.boundaries`. -/
def boundary : fin c.boundaries.card → fin (n+1) :=
finset.mono_of_fin c.boundaries rfl

@[simp] lemma boundary_zero : c.boundary ⟨0, c.card_boundaries_pos⟩ = 0 :=
begin
  rw [boundary, finset.mono_of_fin_zero rfl c.boundaries_nonempty c.card_boundaries_pos],
  exact le_antisymm (finset.min'_le _ _ _ c.zero_mem) (fin.zero_le _),
end

@[simp] lemma boundary_length : c.boundary ⟨c.length, c.length_lt_card_boundaries⟩ = fin.last n :=
begin
  convert finset.mono_of_fin_last rfl c.boundaries_nonempty c.card_boundaries_pos,
  exact le_antisymm (finset.le_max' _ _ _ c.last_mem) (fin.le_last _)
end

/-- Size of the `i`-th block in a `composition_as_set`, seen as a function on `fin c.length`. -/
def blocks_fun (i : fin c.length) : ℕ :=
(c.boundary ⟨i.val + 1, c.lt_length i⟩).val - (c.boundary ⟨i.val, c.lt_length' i⟩).val

lemma blocks_fun_pos (i : fin c.length) : 0 < c.blocks_fun i :=
begin
  have : (⟨i.val, c.lt_length' i⟩ : fin c.boundaries.card) < ⟨i.val + 1, c.lt_length i⟩ :=
    nat.lt_succ_self _,
  exact nat.lt_sub_left_of_add_lt (finset.mono_of_fin_strict_mono c.boundaries rfl this)
end

/-- List of the sizes of the blocks in a `composition_as_set`. -/
def blocks (c : composition_as_set n) : list ℕ :=
of_fn c.blocks_fun

@[simp] lemma blocks_length : c.blocks.length = c.length :=
length_of_fn _

lemma blocks_partial_sum {i : ℕ} (h : i < c.boundaries.card) :
  (c.blocks.take i).sum = c.boundary ⟨i, h⟩ :=
begin
  induction i with i IH, { simp },
  have A : i < c.blocks.length,
  { rw c.card_boundaries_eq_succ_length at h,
    simp [blocks, nat.lt_of_succ_lt_succ h] },
  have B : i < c.boundaries.card := lt_of_lt_of_le A (by simp [blocks, length, nat.sub_le]),
  rw [sum_take_succ _ _ A, IH B],
  simp only [blocks, blocks_fun, fin.coe_eq_val, nth_le_of_fn'],
  rw nat.add_sub_cancel',
  refine le_of_lt (@finset.mono_of_fin_strict_mono _ _ c.boundaries _ rfl
    (⟨i, B⟩ : fin c.boundaries.card) _ _),
  exact nat.lt_succ_self _
end

lemma mem_boundaries_iff_exists_blocks_sum_take_eq {j : fin (n+1)} :
  j ∈ c.boundaries ↔ ∃ i < c.boundaries.card, (c.blocks.take i).sum = j.val :=
begin
  split,
  { assume hj,
    rcases (c.boundaries.mono_of_fin_bij_on rfl).surj_on hj with ⟨i, _, hi⟩,
    refine ⟨i.1, i.2, _⟩,
    rw [← hi, c.blocks_partial_sum i.2],
    refl },
  { rintros ⟨i, hi, H⟩,
    convert (c.boundaries.mono_of_fin_bij_on rfl).maps_to (set.mem_univ ⟨i, hi⟩),
    have : c.boundary ⟨i, hi⟩ = j, by rwa [fin.ext_iff, ← fin.coe_eq_val, ← c.blocks_partial_sum hi],
    exact this.symm }
end

lemma blocks_sum : c.blocks.sum = n :=
begin
  have : c.blocks.take c.length = c.blocks := take_all_of_le (by simp [blocks]),
  rw [← this, c.blocks_partial_sum c.length_lt_card_boundaries, c.boundary_length],
  refl
end

/-- List of the sizes of the blocks in a `composition_as_set`, seen as positive integers. -/
def blocks_pnat : list (ℕ+ ) :=
of_fn (λ i, ⟨c.blocks_fun i, c.blocks_fun_pos i⟩)

lemma coe_blocks_pnat_eq_blocks : c.blocks_pnat.map coe = c.blocks :=
by { simp [blocks_pnat, blocks], refl }

@[simp] lemma blocks_pnat_length : c.blocks_pnat.length = c.length :=
length_of_fn _

/-- Associating a `composition n` to a `composition_as_set n`, by registering the sizes of the
blocks as a list of positive integers. -/
def to_composition : composition n :=
{ blocks_pnat := c.blocks_pnat,
  blocks_pnat_sum := begin
    rw [blocks_pnat, map_of_fn],
    conv_rhs { rw ← c.blocks_sum },
    congr
  end }

end composition_as_set


/-!
### Equivalence between compositions and compositions as sets

In this section, we explain how to go back and forth between a `composition` and a
`composition_as_set`, by showing that their `blocks` and `length` and `boundaries` correspond to
each other, and construct an equivalence between them called `composition_equiv`.
-/

@[simp] lemma composition.to_composition_as_set_length (c : composition n) :
  c.to_composition_as_set.length = c.length :=
by simp [composition.to_composition_as_set, composition_as_set.length,
         c.card_boundaries_eq_succ_length]

@[simp] lemma composition_as_set.to_composition_length (c : composition_as_set n) :
  c.to_composition.length = c.length :=
by simp [composition_as_set.to_composition, composition.length, composition.blocks]

@[simp] lemma composition.to_composition_as_set_blocks (c : composition n) :
  c.to_composition_as_set.blocks = c.blocks :=
begin
  let d := c.to_composition_as_set,
  change d.blocks = c.blocks,
  have length_eq : d.blocks.length = c.blocks.length,
  { convert c.to_composition_as_set_length,
    simp [composition_as_set.blocks] },
  suffices H : ∀ (i ≤ d.blocks.length), (d.blocks.take i).sum = (c.blocks.take i).sum,
    from eq_of_sum_take_eq length_eq H,
  assume i hi,
  have i_lt : i < d.boundaries.card,
  { convert nat.lt_succ_iff.2 hi,
    convert d.card_boundaries_eq_succ_length,
    exact length_of_fn _ },
  have i_lt' : i < c.boundaries.card := i_lt,
  have i_lt'' : i < c.length + 1, by rwa c.card_boundaries_eq_succ_length at i_lt',
  have A : finset.mono_of_fin d.boundaries rfl ⟨i, i_lt⟩
    = finset.mono_of_fin c.boundaries rfl ⟨i, i_lt'⟩ := rfl,
  have B : c.size_up_to i = c.boundary ⟨i, i_lt''⟩ := rfl,
  rw [d.blocks_partial_sum i_lt, composition_as_set.boundary, A, ← composition.size_up_to, B,
      fin.coe_eq_val, fin.coe_eq_val, ← fin.ext_iff,
      c.mono_of_fin_boundaries, finset.mono_of_fin_eq_mono_of_fin_iff]
end

@[simp] lemma composition.to_composition_as_set_blocks_pnat (c : composition n) :
  c.to_composition_as_set.blocks_pnat = c.blocks_pnat :=
begin
  rw ← (injective_map_iff.2 subtype.val_injective).eq_iff,
  convert c.to_composition_as_set_blocks,
  exact composition_as_set.coe_blocks_pnat_eq_blocks _
end

@[simp] lemma composition_as_set.to_composition_blocks_pnat (c : composition_as_set n) :
  c.to_composition.blocks_pnat = c.blocks_pnat := rfl

@[simp] lemma composition_as_set.to_composition_blocks (c : composition_as_set n) :
  c.to_composition.blocks = c.blocks :=
by simp [composition.blocks, composition_as_set.coe_blocks_pnat_eq_blocks]

@[simp] lemma composition_as_set.to_composition_boundaries (c : composition_as_set n) :
  c.to_composition.boundaries = c.boundaries :=
begin
  ext j,
  simp [c.mem_boundaries_iff_exists_blocks_sum_take_eq, c.card_boundaries_eq_succ_length,
    composition.boundary, fin.ext_iff, composition.size_up_to, exists_prop, finset.mem_univ,
    take, exists_prop_of_true, finset.mem_image, composition_as_set.to_composition_blocks,
    composition.boundaries],
  split,
  { rintros ⟨i, hi⟩,
    refine ⟨i.1, _, hi⟩,
    convert i.2,
    simp },
  { rintros ⟨i, i_lt, hi⟩,
    have : i < c.to_composition.length + 1, by simpa using i_lt,
    exact ⟨⟨i, this⟩, hi⟩ }
end

@[simp] lemma composition.to_composition_as_set_boundaries (c : composition n) :
  c.to_composition_as_set.boundaries = c.boundaries := rfl

/-- Equivalence between `composition n` and `composition_as_set n`. -/
def composition_equiv (n : ℕ) : composition n ≃ composition_as_set n :=
{ to_fun    := λ c, c.to_composition_as_set,
  inv_fun   := λ c, c.to_composition,
  left_inv  := λ c, by { ext1, exact c.to_composition_as_set_blocks_pnat },
  right_inv := λ c, by { ext1, exact c.to_composition_boundaries } }

instance composition_fintype (n : ℕ) : fintype (composition n) :=
fintype.of_equiv _ (composition_equiv n).symm

lemma composition_card (n : ℕ) : fintype.card (composition n) = 2 ^ (n - 1) :=
begin
  rw ← composition_as_set_card n,
  exact fintype.card_congr (composition_equiv n)
end
