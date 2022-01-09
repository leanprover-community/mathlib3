/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin
-/
import data.matrix.basic

/-!
# Block Matrices

## Main definitions

* `matrix.from_blocks`: build a block matrix out of 4 blocks
* `matrix.to_blocks₁₁`, `matrix.to_blocks₁₂`, `matrix.to_blocks₂₁`, `matrix.to_blocks₂₂`:
  extract each of the four blocks from `matrix.from_blocks`.
* `matrix.block_diagonal`: block diagonal of equally sized blocks
* `matrix.block_diagonal'`: block diagonal of unequally sized blocks
-/

variables {l m n o : Type*} {m' : o → Type*} {n' : o → Type*}
variables {R : Type*} {S : Type*} {α : Type*} {β : Type*}

open_locale matrix

namespace matrix

section block_matrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
def from_blocks (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  matrix (n ⊕ o) (l ⊕ m) α :=
sum.elim (λ i, sum.elim (A i) (B i))
         (λ i, sum.elim (C i) (D i))

@[simp] lemma from_blocks_apply₁₁
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : n) (j : l) :
  from_blocks A B C D (sum.inl i) (sum.inl j) = A i j :=
rfl

@[simp] lemma from_blocks_apply₁₂
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : n) (j : m) :
  from_blocks A B C D (sum.inl i) (sum.inr j) = B i j :=
rfl

@[simp] lemma from_blocks_apply₂₁
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : o) (j : l) :
  from_blocks A B C D (sum.inr i) (sum.inl j) = C i j :=
rfl

@[simp] lemma from_blocks_apply₂₂
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (i : o) (j : m) :
  from_blocks A B C D (sum.inr i) (sum.inr j) = D i j :=
rfl

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top left" submatrix. -/
def to_blocks₁₁ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix n l α :=
λ i j, M (sum.inl i) (sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def to_blocks₁₂ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix n m α :=
λ i j, M (sum.inl i) (sum.inr j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def to_blocks₂₁ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix o l α :=
λ i j, M (sum.inr i) (sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def to_blocks₂₂ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix o m α :=
λ i j, M (sum.inr i) (sum.inr j)

lemma from_blocks_to_blocks (M : matrix (n ⊕ o) (l ⊕ m) α) :
  from_blocks M.to_blocks₁₁ M.to_blocks₁₂ M.to_blocks₂₁ M.to_blocks₂₂ = M :=
begin
  ext i j, rcases i; rcases j; refl,
end

@[simp] lemma to_blocks_from_blocks₁₁
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).to_blocks₁₁ = A :=
rfl

@[simp] lemma to_blocks_from_blocks₁₂
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).to_blocks₁₂ = B :=
rfl

@[simp] lemma to_blocks_from_blocks₂₁
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).to_blocks₂₁ = C :=
rfl

@[simp] lemma to_blocks_from_blocks₂₂
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).to_blocks₂₂ = D :=
rfl

lemma from_blocks_map
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (f : α → β) :
  (from_blocks A B C D).map f = from_blocks (A.map f) (B.map f) (C.map f) (D.map f) :=
begin
  ext i j, rcases i; rcases j; simp [from_blocks],
end

lemma from_blocks_transpose
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D)ᵀ = from_blocks Aᵀ Cᵀ Bᵀ Dᵀ :=
begin
  ext i j, rcases i; rcases j; simp [from_blocks],
end

lemma from_blocks_conj_transpose [has_star α]
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D)ᴴ = from_blocks Aᴴ Cᴴ Bᴴ Dᴴ :=
begin
  simp only [conj_transpose, from_blocks_transpose, from_blocks_map]
end

/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
def is_two_block_diagonal [has_zero α] (A : matrix (n ⊕ o) (l ⊕ m) α) : Prop :=
to_blocks₁₂ A = 0 ∧ to_blocks₂₁ A = 0

/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `to_block M p q` is the corresponding block matrix. -/
def to_block (M : matrix m n α) (p : m → Prop) (q : n → Prop) :
  matrix {a // p a} {a // q a} α := M.minor coe coe

@[simp] lemma to_block_apply (M : matrix m n α) (p : m → Prop) (q : n → Prop)
  (i : {a // p a}) (j : {a // q a}) : to_block M p q i j = M ↑i ↑j := rfl

/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `to_square_block M b k` is the block `k` matrix. -/
def to_square_block (M : matrix m m α) {n : nat} (b : m → fin n) (k : fin n) :
  matrix {a // b a = k} {a // b a = k} α := M.minor coe coe

@[simp] lemma to_square_block_def (M : matrix m m α) {n : nat} (b : m → fin n) (k : fin n) :
  to_square_block M b k = λ i j, M ↑i ↑j := rfl

/-- Alternate version with `b : m → nat`. Let `b` map rows and columns of a square matrix `M` to
  blocks. Then `to_square_block' M b k` is the block `k` matrix. -/
def to_square_block' (M : matrix m m α) (b : m → nat) (k : nat) :
  matrix {a // b a = k} {a // b a = k} α := M.minor coe coe

@[simp] lemma to_square_block_def' (M : matrix m m α) (b : m → nat) (k : nat) :
  to_square_block' M b k = λ i j, M ↑i ↑j := rfl

/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `to_square_block_prop M p` is the corresponding block matrix. -/
def to_square_block_prop (M : matrix m m α) (p : m → Prop) :
  matrix {a // p a} {a // p a} α := M.minor coe coe

@[simp] lemma to_square_block_prop_def (M : matrix m m α) (p : m → Prop) :
  to_square_block_prop M p = λ i j, M ↑i ↑j := rfl

variables [semiring α]

lemma from_blocks_smul
  (x : α) (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  x • (from_blocks A B C D) = from_blocks (x • A) (x • B) (x • C) (x • D) :=
begin
  ext i j, rcases i; rcases j; simp [from_blocks],
end

lemma from_blocks_add
  (A  : matrix n l α) (B  : matrix n m α) (C  : matrix o l α) (D  : matrix o m α)
  (A' : matrix n l α) (B' : matrix n m α) (C' : matrix o l α) (D' : matrix o m α) :
  (from_blocks A B C D) + (from_blocks A' B' C' D') =
  from_blocks (A + A') (B + B')
              (C + C') (D + D') :=
begin
  ext i j, rcases i; rcases j; refl,
end

lemma from_blocks_multiply {p q : Type*} [fintype l] [fintype m]
  (A  : matrix n l α) (B  : matrix n m α) (C  : matrix o l α) (D  : matrix o m α)
  (A' : matrix l p α) (B' : matrix l q α) (C' : matrix m p α) (D' : matrix m q α) :
  (from_blocks A B C D) ⬝ (from_blocks A' B' C' D') =
  from_blocks (A ⬝ A' + B ⬝ C') (A ⬝ B' + B ⬝ D')
              (C ⬝ A' + D ⬝ C') (C ⬝ B' + D ⬝ D') :=
begin
  ext i j, rcases i; rcases j;
  simp only [from_blocks, mul_apply, fintype.sum_sum_type, sum.elim_inl, sum.elim_inr,
    pi.add_apply],
end

variables [decidable_eq l] [decidable_eq m]

@[simp] lemma from_blocks_diagonal (d₁ : l → α) (d₂ : m → α) :
  from_blocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (sum.elim d₁ d₂) :=
begin
  ext i j, rcases i; rcases j; simp [diagonal],
end

@[simp] lemma from_blocks_one : from_blocks (1 : matrix l l α) 0 0 (1 : matrix m m α) = 1 :=
by { ext i j, rcases i; rcases j; simp [one_apply] }

end block_matrices

section block_diagonal

variables (M N : o → matrix m n α) [decidable_eq o]

section has_zero

variables [has_zero α] [has_zero β]

/-- `matrix.block_diagonal M` turns a homogenously-indexed collection of matrices
`M : o → matrix m n α'` into a `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `matrix.block_diagonal'` if the matrices may not have the same size everywhere.
-/
def block_diagonal : matrix (m × o) (n × o) α
| ⟨i, k⟩ ⟨j, k'⟩ := if k = k' then M k i j else 0

lemma block_diagonal_apply (ik jk) :
  block_diagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 :=
by { cases ik, cases jk, refl }

@[simp]
lemma block_diagonal_apply_eq (i j k) :
  block_diagonal M (i, k) (j, k) = M k i j :=
if_pos rfl

lemma block_diagonal_apply_ne (i j) {k k'} (h : k ≠ k') :
  block_diagonal M (i, k) (j, k') = 0 :=
if_neg h

lemma block_diagonal_map (f : α → β) (hf : f 0 = 0) :
  (block_diagonal M).map f = block_diagonal (λ k, (M k).map f) :=
begin
  ext,
  simp only [map_apply, block_diagonal_apply, eq_comm],
  rw [apply_ite f, hf],
end

@[simp] lemma block_diagonal_transpose :
  (block_diagonal M)ᵀ = block_diagonal (λ k, (M k)ᵀ) :=
begin
  ext,
  simp only [transpose_apply, block_diagonal_apply, eq_comm],
  split_ifs with h,
  { rw h },
  { refl }
end

@[simp] lemma block_diagonal_conj_transpose
  {α : Type*} [semiring α] [star_ring α] (M : o → matrix m n α) :
  (block_diagonal M)ᴴ = block_diagonal (λ k, (M k)ᴴ) :=
begin
  simp only [conj_transpose, block_diagonal_transpose],
  rw block_diagonal_map _ star (star_zero α),
end

@[simp] lemma block_diagonal_zero :
  block_diagonal (0 : o → matrix m n α) = 0 :=
by { ext, simp [block_diagonal_apply] }

@[simp] lemma block_diagonal_diagonal [decidable_eq m] (d : o → m → α) :
  block_diagonal (λ k, diagonal (d k)) = diagonal (λ ik, d ik.2 ik.1) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  simp only [block_diagonal_apply, diagonal, prod.mk.inj_iff, ← ite_and],
  congr' 1,
  rw and_comm,
end

@[simp] lemma block_diagonal_one [decidable_eq m] [has_one α] :
  block_diagonal (1 : o → matrix m m α) = 1 :=
show block_diagonal (λ (_ : o), diagonal (λ (_ : m), (1 : α))) = diagonal (λ _, 1),
by rw [block_diagonal_diagonal]

end has_zero

@[simp] lemma block_diagonal_add [add_monoid α] :
  block_diagonal (M + N) = block_diagonal M + block_diagonal N :=
begin
  ext,
  simp only [block_diagonal_apply, pi.add_apply],
  split_ifs; simp
end

@[simp] lemma block_diagonal_neg [add_group α] :
  block_diagonal (-M) = - block_diagonal M :=
begin
  ext,
  simp only [block_diagonal_apply, pi.neg_apply],
  split_ifs; simp
end

@[simp] lemma block_diagonal_sub [add_group α] :
  block_diagonal (M - N) = block_diagonal M - block_diagonal N :=
by simp [sub_eq_add_neg]

@[simp] lemma block_diagonal_mul {p : Type*} [fintype n] [fintype o] [semiring α]
  (N : o → matrix n p α) :
  block_diagonal (λ k, M k ⬝ N k) = block_diagonal M ⬝ block_diagonal N :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  simp only [block_diagonal_apply, mul_apply, ← finset.univ_product_univ, finset.sum_product],
  split_ifs with h; simp [h]
end

@[simp] lemma block_diagonal_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α]
  (x : R) : block_diagonal (x • M) = x • block_diagonal M :=
by { ext, simp only [block_diagonal_apply, pi.smul_apply], split_ifs; simp }

end block_diagonal

section block_diagonal'

variables (M N : Π i, matrix (m' i) (n' i) α) [decidable_eq o]

section has_zero

variables [has_zero α] [has_zero β]

/-- `matrix.block_diagonal' M` turns `M : Π i, matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `matrix.block_diagonal`. -/
def block_diagonal' : matrix (Σ i, m' i) (Σ i, n' i) α
| ⟨k, i⟩ ⟨k', j⟩ := if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0

lemma block_diagonal'_eq_block_diagonal (M : o → matrix m n α) {k k'} (i j) :
  block_diagonal M (i, k) (j, k') = block_diagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
rfl

lemma block_diagonal'_minor_eq_block_diagonal (M : o → matrix m n α) :
  (block_diagonal' M).minor (prod.to_sigma ∘ prod.swap) (prod.to_sigma ∘ prod.swap) =
    block_diagonal M :=
matrix.ext $ λ ⟨k, i⟩ ⟨k', j⟩, rfl

lemma block_diagonal'_apply (ik jk) :
  block_diagonal' M ik jk = if h : ik.1 = jk.1 then
    M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 :=
by { cases ik, cases jk, refl }

@[simp]
lemma block_diagonal'_apply_eq (k i j) :
  block_diagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
dif_pos rfl

lemma block_diagonal'_apply_ne {k k'} (i j) (h : k ≠ k') :
  block_diagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
dif_neg h

lemma block_diagonal'_map (f : α → β) (hf : f 0 = 0) :
  (block_diagonal' M).map f = block_diagonal' (λ k, (M k).map f) :=
begin
  ext,
  simp only [map_apply, block_diagonal'_apply, eq_comm],
  rw [apply_dite f, hf],
end

@[simp] lemma block_diagonal'_transpose :
  (block_diagonal' M)ᵀ = block_diagonal' (λ k, (M k)ᵀ) :=
begin
  ext ⟨ii, ix⟩ ⟨ji, jx⟩,
  simp only [transpose_apply, block_diagonal'_apply, eq_comm],
  dsimp only,
  split_ifs with h₁ h₂ h₂,
  { subst h₁, refl, },
  { exact (h₂ h₁.symm).elim },
  { exact (h₁ h₂.symm).elim },
  { refl }
end

@[simp] lemma block_diagonal'_conj_transpose {α} [semiring α] [star_ring α]
  (M : Π i, matrix (m' i) (n' i) α) :
  (block_diagonal' M)ᴴ = block_diagonal' (λ k, (M k)ᴴ) :=
begin
  simp only [conj_transpose, block_diagonal'_transpose],
  exact block_diagonal'_map _ star (star_zero α),
end

@[simp] lemma block_diagonal'_zero :
  block_diagonal' (0 : Π i, matrix (m' i) (n' i) α) = 0 :=
by { ext, simp [block_diagonal'_apply] }

@[simp] lemma block_diagonal'_diagonal [∀ i, decidable_eq (m' i)] (d : Π i, m' i → α) :
  block_diagonal' (λ k, diagonal (d k)) = diagonal (λ ik, d ik.1 ik.2) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  simp only [block_diagonal'_apply, diagonal],
  split_ifs; -- `finish` can close these goals
  try { refl }; exfalso,
  { exact h_2 ⟨h, (cast_eq_iff_heq.mp h_1.symm).symm⟩ },
  { exact h_1 (cast_eq_iff_heq.mpr h_2.right.symm).symm },
  { tauto },
end

@[simp] lemma block_diagonal'_one [∀ i, decidable_eq (m' i)] [has_one α] :
  block_diagonal' (1 : Π i, matrix (m' i) (m' i) α) = 1 :=
show block_diagonal' (λ (i : o), diagonal (λ (_ : m' i), (1 : α))) = diagonal (λ _, 1),
by rw [block_diagonal'_diagonal]

end has_zero

@[simp] lemma block_diagonal'_add [add_monoid α] :
  block_diagonal' (M + N) = block_diagonal' M + block_diagonal' N :=
begin
  ext,
  simp only [block_diagonal'_apply, pi.add_apply],
  split_ifs; simp
end

@[simp] lemma block_diagonal'_neg [add_group α] :
  block_diagonal' (-M) = - block_diagonal' M :=
begin
  ext,
  simp only [block_diagonal'_apply, pi.neg_apply],
  split_ifs; simp
end

@[simp] lemma block_diagonal'_sub [add_group α] :
  block_diagonal' (M - N) = block_diagonal' M - block_diagonal' N :=
by simp [sub_eq_add_neg]

@[simp] lemma block_diagonal'_mul {p : o → Type*} [semiring α] [Π i, fintype (n' i)] [fintype o]
  (N : Π i, matrix (n' i) (p i) α) :
    block_diagonal' (λ k, M k ⬝ N k) = block_diagonal' M ⬝ block_diagonal' N :=
begin
  ext ⟨k, i⟩ ⟨k', j⟩,
  simp only [block_diagonal'_apply, mul_apply, ← finset.univ_sigma_univ, finset.sum_sigma],
  rw fintype.sum_eq_single k,
  { split_ifs; simp },
  { intros j' hj', exact finset.sum_eq_zero (λ _ _, by rw [dif_neg hj'.symm, zero_mul]) },
end

@[simp] lemma block_diagonal'_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α]
  (x : R) : block_diagonal' (x • M) = x • block_diagonal' M :=
by { ext, simp only [block_diagonal'_apply, pi.smul_apply], split_ifs; simp }

end block_diagonal'

end matrix
