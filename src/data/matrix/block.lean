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
* `matrix.block_diagonal`: block diagonal of equally sized blocks. On square blocks, this is a
  ring homomorphisms, `matrix.block_diagonal_ring_hom`.
* `matrix.block_diag`: extract the blocks from the diagonal of a block diagonal matrix.
* `matrix.block_diagonal'`: block diagonal of unequally sized blocks. On square blocks, this is a
  ring homomorphisms, `matrix.block_diagonal'_ring_hom`.
* `matrix.block_diag'`: extract the blocks from the diagonal of a block diagonal matrix.
-/

variables {l m n o p q : Type*} {m' n' p' : o → Type*}
variables {R : Type*} {S : Type*} {α : Type*} {β : Type*}

open_locale matrix

namespace matrix

section block_matrices

/-- We can form a single large matrix by flattening smaller 'block' matrices of compatible
dimensions. -/
@[pp_nodot]
def from_blocks (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  matrix (n ⊕ o) (l ⊕ m) α :=
of $ sum.elim (λ i, sum.elim (A i) (B i))
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
of $ λ i j, M (sum.inl i) (sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"top right" submatrix. -/
def to_blocks₁₂ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix n m α :=
of $ λ i j, M (sum.inl i) (sum.inr j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom left" submatrix. -/
def to_blocks₂₁ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix o l α :=
of $ λ i j, M (sum.inr i) (sum.inl j)

/-- Given a matrix whose row and column indexes are sum types, we can extract the corresponding
"bottom right" submatrix. -/
def to_blocks₂₂ (M : matrix (n ⊕ o) (l ⊕ m) α) : matrix o m α :=
of $ λ i j, M (sum.inr i) (sum.inr j)

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

@[simp] lemma from_blocks_submatrix_sum_swap_left
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (f : p → l ⊕ m) :
  (from_blocks A B C D).submatrix sum.swap f = (from_blocks C D A B).submatrix id f :=
by { ext i j, cases i; dsimp; cases f j; refl }

@[simp] lemma from_blocks_submatrix_sum_swap_right
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (f : p → n ⊕ o) :
  (from_blocks A B C D).submatrix f sum.swap = (from_blocks B A D C).submatrix f id :=
by { ext i j, cases j; dsimp; cases f i; refl }

lemma from_blocks_submatrix_sum_swap_sum_swap {l m n o α : Type*}
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  (from_blocks A B C D).submatrix sum.swap sum.swap = from_blocks D C B A :=
by simp

/-- A 2x2 block matrix is block diagonal if the blocks outside of the diagonal vanish -/
def is_two_block_diagonal [has_zero α] (A : matrix (n ⊕ o) (l ⊕ m) α) : Prop :=
to_blocks₁₂ A = 0 ∧ to_blocks₂₁ A = 0

/-- Let `p` pick out certain rows and `q` pick out certain columns of a matrix `M`. Then
  `to_block M p q` is the corresponding block matrix. -/
def to_block (M : matrix m n α) (p : m → Prop) (q : n → Prop) :
  matrix {a // p a} {a // q a} α := M.submatrix coe coe

@[simp] lemma to_block_apply (M : matrix m n α) (p : m → Prop) (q : n → Prop)
  (i : {a // p a}) (j : {a // q a}) : to_block M p q i j = M ↑i ↑j := rfl

/-- Let `p` pick out certain rows and columns of a square matrix `M`. Then
  `to_square_block_prop M p` is the corresponding block matrix. -/
def to_square_block_prop (M : matrix m m α) (p : m → Prop) : matrix {a // p a} {a // p a} α :=
to_block M _ _

lemma to_square_block_prop_def (M : matrix m m α) (p : m → Prop) :
  to_square_block_prop M p = λ i j, M ↑i ↑j := rfl

/-- Let `b` map rows and columns of a square matrix `M` to blocks. Then
  `to_square_block M b k` is the block `k` matrix. -/
def to_square_block (M : matrix m m α) (b : m → β) (k : β) :
  matrix {a // b a = k} {a // b a = k} α := to_square_block_prop M _

lemma to_square_block_def (M : matrix m m α) (b : m → β) (k : β) :
  to_square_block M b k = λ i j, M ↑i ↑j := rfl

lemma from_blocks_smul [has_smul R α]
  (x : R) (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) :
  x • (from_blocks A B C D) = from_blocks (x • A) (x • B) (x • C) (x • D) :=
begin
  ext i j, rcases i; rcases j; simp [from_blocks],
end

lemma from_blocks_neg [has_neg R]
  (A : matrix n l R) (B : matrix n m R) (C : matrix o l R) (D : matrix o m R) :
  - (from_blocks A B C D) = from_blocks (-A) (-B) (-C) (-D) :=
begin
  ext i j, cases i; cases j; simp [from_blocks],
end

lemma from_blocks_add [has_add α]
  (A  : matrix n l α) (B  : matrix n m α) (C  : matrix o l α) (D  : matrix o m α)
  (A' : matrix n l α) (B' : matrix n m α) (C' : matrix o l α) (D' : matrix o m α) :
  (from_blocks A B C D) + (from_blocks A' B' C' D') =
  from_blocks (A + A') (B + B')
              (C + C') (D + D') :=
begin
  ext i j, rcases i; rcases j; refl,
end

lemma from_blocks_multiply [fintype l] [fintype m] [non_unital_non_assoc_semiring α]
  (A  : matrix n l α) (B  : matrix n m α) (C  : matrix o l α) (D  : matrix o m α)
  (A' : matrix l p α) (B' : matrix l q α) (C' : matrix m p α) (D' : matrix m q α) :
  (from_blocks A B C D) ⬝ (from_blocks A' B' C' D') =
  from_blocks (A ⬝ A' + B ⬝ C') (A ⬝ B' + B ⬝ D')
              (C ⬝ A' + D ⬝ C') (C ⬝ B' + D ⬝ D') :=
begin
  ext i j, rcases i; rcases j;
  simp only [from_blocks, mul_apply, fintype.sum_sum_type, sum.elim_inl, sum.elim_inr,
    pi.add_apply, of_apply],
end

lemma from_blocks_mul_vec [fintype l] [fintype m] [non_unital_non_assoc_semiring α]
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (x : l ⊕ m → α) :
  mul_vec (from_blocks A B C D) x =
  sum.elim (mul_vec A (x ∘ sum.inl) + mul_vec B (x ∘ sum.inr))
           (mul_vec C (x ∘ sum.inl) + mul_vec D (x ∘ sum.inr)) :=
by { ext i, cases i; simp [mul_vec, dot_product] }

lemma vec_mul_from_blocks [fintype n] [fintype o] [non_unital_non_assoc_semiring α]
  (A : matrix n l α) (B : matrix n m α) (C : matrix o l α) (D : matrix o m α) (x : n ⊕ o → α) :
  vec_mul x (from_blocks A B C D) =
  sum.elim (vec_mul (x ∘ sum.inl) A + vec_mul (x ∘ sum.inr) C)
           (vec_mul (x ∘ sum.inl) B + vec_mul (x ∘ sum.inr) D) :=
by { ext i, cases i; simp [vec_mul, dot_product] }

variables [decidable_eq l] [decidable_eq m]

section has_zero
variables [has_zero α]

lemma to_block_diagonal_self (d : m → α) (p : m → Prop) :
  matrix.to_block (diagonal d) p p = diagonal (λ i : subtype p, d ↑i) :=
begin
  ext i j,
  by_cases i = j,
  { simp [h] },
  { simp [has_one.one, h, λ h', h $ subtype.ext h'], }
end

lemma to_block_diagonal_disjoint (d : m → α) {p q : m → Prop} (hpq : disjoint p q) :
  matrix.to_block (diagonal d) p q = 0 :=
begin
  ext ⟨i, hi⟩ ⟨j, hj⟩,
  have : i ≠ j, from λ heq, hpq.le_bot i ⟨hi, heq.symm ▸ hj⟩,
  simp [diagonal_apply_ne d this]
end

@[simp] lemma from_blocks_diagonal (d₁ : l → α) (d₂ : m → α) :
  from_blocks (diagonal d₁) 0 0 (diagonal d₂) = diagonal (sum.elim d₁ d₂) :=
begin
  ext i j, rcases i; rcases j; simp [diagonal],
end

end has_zero

section has_zero_has_one
variables [has_zero α] [has_one α]

@[simp] lemma from_blocks_one :
  from_blocks (1 : matrix l l α) 0 0 (1 : matrix m m α) = 1 :=
by { ext i j, rcases i; rcases j; simp [one_apply] }

@[simp] lemma to_block_one_self (p : m → Prop) : matrix.to_block (1 : matrix m m α) p p = 1 :=
to_block_diagonal_self _ p

lemma to_block_one_disjoint {p q : m → Prop} (hpq : disjoint p q) :
  matrix.to_block (1 : matrix m m α) p q = 0 :=
to_block_diagonal_disjoint _ hpq

end has_zero_has_one

end block_matrices

section block_diagonal
variables [decidable_eq o]

section has_zero
variables [has_zero α] [has_zero β]

/-- `matrix.block_diagonal M` turns a homogenously-indexed collection of matrices
`M : o → matrix m n α'` into a `m × o`-by-`n × o` block matrix which has the entries of `M` along
the diagonal and zero elsewhere.

See also `matrix.block_diagonal'` if the matrices may not have the same size everywhere.
-/
def block_diagonal (M : o → matrix m n α) : matrix (m × o) (n × o) α
| ⟨i, k⟩ ⟨j, k'⟩ := if k = k' then M k i j else 0

lemma block_diagonal_apply (M : o → matrix m n α) (ik jk) :
  block_diagonal M ik jk = if ik.2 = jk.2 then M ik.2 ik.1 jk.1 else 0 :=
by { cases ik, cases jk, refl }

@[simp]
lemma block_diagonal_apply_eq (M : o → matrix m n α) (i j k) :
  block_diagonal M (i, k) (j, k) = M k i j :=
if_pos rfl

lemma block_diagonal_apply_ne (M : o → matrix m n α) (i j) {k k'} (h : k ≠ k') :
  block_diagonal M (i, k) (j, k') = 0 :=
if_neg h

lemma block_diagonal_map (M : o → matrix m n α) (f : α → β) (hf : f 0 = 0) :
  (block_diagonal M).map f = block_diagonal (λ k, (M k).map f) :=
begin
  ext,
  simp only [map_apply, block_diagonal_apply, eq_comm],
  rw [apply_ite f, hf],
end

@[simp] lemma block_diagonal_transpose (M : o → matrix m n α) :
  (block_diagonal M)ᵀ = block_diagonal (λ k, (M k)ᵀ) :=
begin
  ext,
  simp only [transpose_apply, block_diagonal_apply, eq_comm],
  split_ifs with h,
  { rw h },
  { refl }
end

@[simp] lemma block_diagonal_conj_transpose
  {α : Type*} [add_monoid α] [star_add_monoid α] (M : o → matrix m n α) :
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

@[simp] lemma block_diagonal_add [add_zero_class α] (M N : o → matrix m n α) :
  block_diagonal (M + N) = block_diagonal M + block_diagonal N :=
begin
  ext,
  simp only [block_diagonal_apply, pi.add_apply],
  split_ifs; simp
end

section
variables (o m n α)
/-- `matrix.block_diagonal` as an `add_monoid_hom`. -/
@[simps] def block_diagonal_add_monoid_hom [add_zero_class α] :
  (o → matrix m n α) →+ matrix (m × o) (n × o) α :=
{ to_fun := block_diagonal,
  map_zero' := block_diagonal_zero,
  map_add' := block_diagonal_add }
end

@[simp] lemma block_diagonal_neg [add_group α] (M : o → matrix m n α) :
  block_diagonal (-M) = - block_diagonal M :=
map_neg (block_diagonal_add_monoid_hom m n o α) M

@[simp] lemma block_diagonal_sub [add_group α] (M N : o → matrix m n α) :
  block_diagonal (M - N) = block_diagonal M - block_diagonal N :=
map_sub (block_diagonal_add_monoid_hom m n o α) M N

@[simp] lemma block_diagonal_mul [fintype n] [fintype o] [non_unital_non_assoc_semiring α]
  (M : o → matrix m n α) (N : o → matrix n p α) :
  block_diagonal (λ k, M k ⬝ N k) = block_diagonal M ⬝ block_diagonal N :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  simp only [block_diagonal_apply, mul_apply, ← finset.univ_product_univ, finset.sum_product],
  split_ifs with h; simp [h]
end

section
variables (α m o)
/-- `matrix.block_diagonal` as a `ring_hom`. -/
@[simps]
def block_diagonal_ring_hom [decidable_eq m] [fintype o] [fintype m] [non_assoc_semiring α] :
  (o → matrix m m α) →+* matrix (m × o) (m × o) α :=
{ to_fun := block_diagonal,
  map_one' := block_diagonal_one,
  map_mul' := block_diagonal_mul,
  ..block_diagonal_add_monoid_hom m m o α }
end

@[simp] lemma block_diagonal_pow [decidable_eq m] [fintype o] [fintype m] [semiring α]
  (M : o → matrix m m α) (n : ℕ)  :
  block_diagonal (M ^ n) = block_diagonal M ^ n :=
map_pow (block_diagonal_ring_hom m o α) M n

@[simp] lemma block_diagonal_smul {R : Type*} [monoid R] [add_monoid α] [distrib_mul_action R α]
  (x : R) (M : o → matrix m n α) : block_diagonal (x • M) = x • block_diagonal M :=
by { ext, simp only [block_diagonal_apply, pi.smul_apply], split_ifs; simp }

end block_diagonal

section block_diag


/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `matrix.diag`, and the left-inverse of `matrix.block_diagonal`. -/
def block_diag (M : matrix (m × o) (n × o) α) (k : o) : matrix m n α
| i j := M (i, k) (j, k)

lemma block_diag_map (M : matrix (m × o) (n × o) α) (f : α → β) :
  block_diag (M.map f) = λ k, (block_diag M k).map f :=
rfl

@[simp] lemma block_diag_transpose (M : matrix (m × o) (n × o) α) (k : o) :
  block_diag Mᵀ k = (block_diag M k)ᵀ :=
ext $ λ i j, rfl

@[simp] lemma block_diag_conj_transpose
  {α : Type*} [add_monoid α] [star_add_monoid α] (M : matrix (m × o) (n × o) α) (k : o) :
  block_diag Mᴴ k = (block_diag M k)ᴴ :=
ext $ λ i j, rfl

section has_zero
variables [has_zero α] [has_zero β]

@[simp] lemma block_diag_zero :
  block_diag (0 : matrix (m × o) (n × o) α) = 0 :=
rfl

@[simp] lemma block_diag_diagonal [decidable_eq o] [decidable_eq m] (d : (m × o) → α) (k : o) :
  block_diag (diagonal d) k = diagonal (λ i, d (i, k)) :=
ext $ λ i j, begin
  obtain rfl | hij := decidable.eq_or_ne i j,
  { rw [block_diag, diagonal_apply_eq, diagonal_apply_eq] },
  { rw [block_diag, diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt _ hij)],
    exact prod.fst_eq_iff.mpr },
end

@[simp] lemma block_diag_block_diagonal [decidable_eq o] (M : o → matrix m n α) :
  block_diag (block_diagonal M) = M :=
funext $ λ k, ext $ λ i j, block_diagonal_apply_eq _ _ _ _

@[simp] lemma block_diag_one [decidable_eq o] [decidable_eq m] [has_one α] :
  block_diag (1 : matrix (m × o) (m × o) α) = 1 :=
funext $ block_diag_diagonal _

end has_zero

@[simp] lemma block_diag_add [add_zero_class α] (M N : matrix (m × o) (n × o) α) :
  block_diag (M + N) = block_diag M + block_diag N :=
rfl

section
variables (o m n α)
/-- `matrix.block_diag` as an `add_monoid_hom`. -/
@[simps] def block_diag_add_monoid_hom [add_zero_class α] :
  matrix (m × o) (n × o) α →+ (o → matrix m n α) :=
{ to_fun := block_diag,
  map_zero' := block_diag_zero,
  map_add' := block_diag_add }
end

@[simp] lemma block_diag_neg [add_group α] (M : matrix (m × o) (n × o) α) :
  block_diag (-M) = - block_diag M :=
map_neg (block_diag_add_monoid_hom m n o α) M

@[simp] lemma block_diag_sub [add_group α] (M N : matrix (m × o) (n × o) α) :
  block_diag (M - N) = block_diag M - block_diag N :=
map_sub (block_diag_add_monoid_hom m n o α) M N

@[simp] lemma block_diag_smul {R : Type*} [monoid R] [add_monoid α] [distrib_mul_action R α]
  (x : R) (M : matrix (m × o) (n × o) α) : block_diag (x • M) = x • block_diag M :=
rfl

end block_diag

section block_diagonal'

variables [decidable_eq o]

section has_zero
variables [has_zero α] [has_zero β]

/-- `matrix.block_diagonal' M` turns `M : Π i, matrix (m i) (n i) α` into a
`Σ i, m i`-by-`Σ i, n i` block matrix which has the entries of `M` along the diagonal
and zero elsewhere.

This is the dependently-typed version of `matrix.block_diagonal`. -/
def block_diagonal' (M : Π i, matrix (m' i) (n' i) α) : matrix (Σ i, m' i) (Σ i, n' i) α
| ⟨k, i⟩ ⟨k', j⟩ := if h : k = k' then M k i (cast (congr_arg n' h.symm) j) else 0

lemma block_diagonal'_eq_block_diagonal (M : o → matrix m n α) {k k'} (i j) :
  block_diagonal M (i, k) (j, k') = block_diagonal' M ⟨k, i⟩ ⟨k', j⟩ :=
rfl

lemma block_diagonal'_submatrix_eq_block_diagonal (M : o → matrix m n α) :
  (block_diagonal' M).submatrix (prod.to_sigma ∘ prod.swap) (prod.to_sigma ∘ prod.swap) =
    block_diagonal M :=
matrix.ext $ λ ⟨k, i⟩ ⟨k', j⟩, rfl

lemma block_diagonal'_apply (M : Π i, matrix (m' i) (n' i) α) (ik jk) :
  block_diagonal' M ik jk = if h : ik.1 = jk.1 then
    M ik.1 ik.2 (cast (congr_arg n' h.symm) jk.2) else 0 :=
by { cases ik, cases jk, refl }

@[simp]
lemma block_diagonal'_apply_eq (M : Π i, matrix (m' i) (n' i) α) (k i j) :
  block_diagonal' M ⟨k, i⟩ ⟨k, j⟩ = M k i j :=
dif_pos rfl

lemma block_diagonal'_apply_ne (M : Π i, matrix (m' i) (n' i) α) {k k'} (i j) (h : k ≠ k') :
  block_diagonal' M ⟨k, i⟩ ⟨k', j⟩ = 0 :=
dif_neg h

lemma block_diagonal'_map (M : Π i, matrix (m' i) (n' i) α) (f : α → β) (hf : f 0 = 0) :
  (block_diagonal' M).map f = block_diagonal' (λ k, (M k).map f) :=
begin
  ext,
  simp only [map_apply, block_diagonal'_apply, eq_comm],
  rw [apply_dite f, hf],
end

@[simp] lemma block_diagonal'_transpose (M : Π i, matrix (m' i) (n' i) α) :
  (block_diagonal' M)ᵀ = block_diagonal' (λ k, (M k)ᵀ) :=
begin
  ext ⟨ii, ix⟩ ⟨ji, jx⟩,
  simp only [transpose_apply, block_diagonal'_apply],
  split_ifs; cc
end

@[simp] lemma block_diagonal'_conj_transpose {α} [add_monoid α] [star_add_monoid α]
  (M : Π i, matrix (m' i) (n' i) α) :
  (block_diagonal' M)ᴴ = block_diagonal' (λ k, (M k)ᴴ) :=
begin
  simp only [conj_transpose, block_diagonal'_transpose],
  exact block_diagonal'_map _ star (star_zero α),
end

@[simp] lemma block_diagonal'_zero :
  block_diagonal' (0 : Π i, matrix (m' i) (n' i) α) = 0 :=
by { ext, simp [block_diagonal'_apply] }

@[simp] lemma block_diagonal'_diagonal [Π i, decidable_eq (m' i)] (d : Π i, m' i → α) :
  block_diagonal' (λ k, diagonal (d k)) = diagonal (λ ik, d ik.1 ik.2) :=
begin
  ext ⟨i, k⟩ ⟨j, k'⟩,
  simp only [block_diagonal'_apply, diagonal],
  obtain rfl | hij := decidable.eq_or_ne i j,
  { simp, },
  { simp [hij] },
end

@[simp] lemma block_diagonal'_one [∀ i, decidable_eq (m' i)] [has_one α] :
  block_diagonal' (1 : Π i, matrix (m' i) (m' i) α) = 1 :=
show block_diagonal' (λ (i : o), diagonal (λ (_ : m' i), (1 : α))) = diagonal (λ _, 1),
by rw [block_diagonal'_diagonal]

end has_zero

@[simp] lemma block_diagonal'_add [add_zero_class α] (M N : Π i, matrix (m' i) (n' i) α) :
  block_diagonal' (M + N) = block_diagonal' M + block_diagonal' N :=
begin
  ext,
  simp only [block_diagonal'_apply, pi.add_apply],
  split_ifs; simp
end


section
variables (m' n' α)
/-- `matrix.block_diagonal'` as an `add_monoid_hom`. -/
@[simps] def block_diagonal'_add_monoid_hom [add_zero_class α] :
  (Π i, matrix (m' i) (n' i) α) →+ matrix (Σ i, m' i) (Σ i, n' i) α :=
{ to_fun := block_diagonal',
  map_zero' := block_diagonal'_zero,
  map_add' := block_diagonal'_add }
end

@[simp] lemma block_diagonal'_neg [add_group α] (M : Π i, matrix (m' i) (n' i) α) :
  block_diagonal' (-M) = - block_diagonal' M :=
map_neg (block_diagonal'_add_monoid_hom m' n' α) M

@[simp] lemma block_diagonal'_sub [add_group α] (M N : Π i, matrix (m' i) (n' i) α) :
  block_diagonal' (M - N) = block_diagonal' M - block_diagonal' N :=
map_sub (block_diagonal'_add_monoid_hom m' n' α) M N

@[simp] lemma block_diagonal'_mul [non_unital_non_assoc_semiring α]
  [Π i, fintype (n' i)] [fintype o]
  (M : Π i, matrix (m' i) (n' i) α) (N : Π i, matrix (n' i) (p' i) α) :
  block_diagonal' (λ k, M k ⬝ N k) = block_diagonal' M ⬝ block_diagonal' N :=
begin
  ext ⟨k, i⟩ ⟨k', j⟩,
  simp only [block_diagonal'_apply, mul_apply, ← finset.univ_sigma_univ, finset.sum_sigma],
  rw fintype.sum_eq_single k,
  { split_ifs; simp },
  { intros j' hj', exact finset.sum_eq_zero (λ _ _, by rw [dif_neg hj'.symm, zero_mul]) },
end

section
variables (α m')
/-- `matrix.block_diagonal'` as a `ring_hom`. -/
@[simps]
def block_diagonal'_ring_hom [Π i, decidable_eq (m' i)] [fintype o] [Π i, fintype (m' i)]
  [non_assoc_semiring α] :
  (Π i, matrix (m' i) (m' i) α) →+* matrix (Σ i, m' i) (Σ i, m' i) α :=
{ to_fun := block_diagonal',
  map_one' := block_diagonal'_one,
  map_mul' := block_diagonal'_mul,
  ..block_diagonal'_add_monoid_hom m' m' α }
end

@[simp] lemma block_diagonal'_pow [Π i, decidable_eq (m' i)] [fintype o] [Π i, fintype (m' i)]
  [semiring α] (M : Π i, matrix (m' i) (m' i) α) (n : ℕ)  :
  block_diagonal' (M ^ n) = block_diagonal' M ^ n :=
map_pow (block_diagonal'_ring_hom m' α) M n

@[simp] lemma block_diagonal'_smul {R : Type*} [semiring R] [add_comm_monoid α] [module R α]
  (x : R) (M : Π i, matrix (m' i) (n' i) α) : block_diagonal' (x • M) = x • block_diagonal' M :=
by { ext, simp only [block_diagonal'_apply, pi.smul_apply], split_ifs; simp }

end block_diagonal'

section block_diag'

/-- Extract a block from the diagonal of a block diagonal matrix.

This is the block form of `matrix.diag`, and the left-inverse of `matrix.block_diagonal'`. -/
def block_diag' (M : matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) : matrix (m' k) (n' k) α
| i j := M ⟨k, i⟩ ⟨k, j⟩

lemma block_diag'_map (M : matrix (Σ i, m' i) (Σ i, n' i) α) (f : α → β) :
  block_diag' (M.map f) = λ k, (block_diag' M k).map f :=
rfl

@[simp] lemma block_diag'_transpose (M : matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) :
  block_diag' Mᵀ k = (block_diag' M k)ᵀ :=
ext $ λ i j, rfl

@[simp] lemma block_diag'_conj_transpose
  {α : Type*} [add_monoid α] [star_add_monoid α] (M : matrix (Σ i, m' i) (Σ i, n' i) α) (k : o) :
  block_diag' Mᴴ k = (block_diag' M k)ᴴ :=
ext $ λ i j, rfl

section has_zero
variables [has_zero α] [has_zero β]

@[simp] lemma block_diag'_zero :
  block_diag' (0 : matrix (Σ i, m' i) (Σ i, n' i) α) = 0 :=
rfl

@[simp] lemma block_diag'_diagonal [decidable_eq o] [Π i, decidable_eq (m' i)]
  (d : (Σ i, m' i) → α) (k : o) :
  block_diag' (diagonal d) k = diagonal (λ i, d ⟨k, i⟩) :=
ext $ λ i j, begin
  obtain rfl | hij := decidable.eq_or_ne i j,
  { rw [block_diag', diagonal_apply_eq, diagonal_apply_eq] },
  { rw [block_diag', diagonal_apply_ne _ hij, diagonal_apply_ne _ (mt (λ h, _) hij)],
    cases h, refl },
end

@[simp] lemma block_diag'_block_diagonal' [decidable_eq o] (M : Π i, matrix (m' i) (n' i) α) :
  block_diag' (block_diagonal' M) = M :=
funext $ λ k, ext $ λ i j, block_diagonal'_apply_eq _ _ _ _

@[simp] lemma block_diag'_one [decidable_eq o] [Π i, decidable_eq (m' i)] [has_one α] :
  block_diag' (1 : matrix (Σ i, m' i) (Σ i, m' i) α) = 1 :=
funext $ block_diag'_diagonal _

end has_zero

@[simp] lemma block_diag'_add [add_zero_class α] (M N : matrix (Σ i, m' i) (Σ i, n' i) α) :
  block_diag' (M + N) = block_diag' M + block_diag' N :=
rfl

section
variables (m' n' α)
/-- `matrix.block_diag'` as an `add_monoid_hom`. -/
@[simps] def block_diag'_add_monoid_hom [add_zero_class α] :
  matrix (Σ i, m' i) (Σ i, n' i) α →+ Π i, matrix (m' i) (n' i) α :=
{ to_fun := block_diag',
  map_zero' := block_diag'_zero,
  map_add' := block_diag'_add }
end

@[simp] lemma block_diag'_neg [add_group α] (M : matrix (Σ i, m' i) (Σ i, n' i) α) :
  block_diag' (-M) = - block_diag' M :=
map_neg (block_diag'_add_monoid_hom m' n' α) M

@[simp] lemma block_diag'_sub [add_group α] (M N : matrix (Σ i, m' i) (Σ i, n' i) α) :
  block_diag' (M - N) = block_diag' M - block_diag' N :=
map_sub (block_diag'_add_monoid_hom m' n' α) M N

@[simp] lemma block_diag'_smul {R : Type*} [monoid R] [add_monoid α] [distrib_mul_action R α]
  (x : R) (M : matrix (Σ i, m' i) (Σ i, n' i) α) : block_diag' (x • M) = x • block_diag' M :=
rfl

end block_diag'

section
variables [comm_ring R]

lemma to_block_mul_eq_mul {m n k : Type*} [fintype n] (p : m → Prop) (q : k → Prop)
  (A : matrix m n R) (B : matrix n k R) :
  (A ⬝ B).to_block p q = A.to_block p ⊤ ⬝ B.to_block ⊤ q :=
begin
  ext i k,
  simp only [to_block_apply, mul_apply],
  rw finset.sum_subtype,
  simp [has_top.top, complete_lattice.top, bounded_order.top],
end

lemma to_block_mul_eq_add
  {m n k : Type*} [fintype n] (p : m → Prop) (q : n → Prop) [decidable_pred q] (r : k → Prop)
  (A : matrix m n R) (B : matrix n k R) :
  (A ⬝ B).to_block p r =
    A.to_block p q ⬝ B.to_block q r + A.to_block p (λ i, ¬ q i) ⬝ B.to_block (λ i, ¬ q i) r :=
begin
  classical,
  ext i k,
  simp only [to_block_apply, mul_apply, pi.add_apply],
  convert (fintype.sum_subtype_add_sum_subtype q (λ x, A ↑i x * B x ↑k)).symm
end

end

end matrix
