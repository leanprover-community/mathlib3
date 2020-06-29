/-
Copyright (c) 2020 Anne Baanen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anne Baanen

Notation for vectors and matrices
-/

import data.fintype.card
import data.matrix.basic
import tactic.fin_cases

/-!
# Matrix and vector notation

This file defines notation for vectors and matrices. Given `a b c d : α`,
the notation allows us to write `![a, b, c, d] : fin 4 → α`.
Nesting vectors gives a matrix, so `![![a, b], ![c, d]] : matrix (fin 2) (fin 2) α`.
This file includes `simp` lemmas for applying operations in
`data.matrix.basic` to values built out of this notation.

## Main definitions

* `vec_empty` is the empty vector (or `0` by `n` matrix) `![]`
* `vec_cons` prepends an entry to a vector, so `![a, b]` is `vec_cons a (vec_cons b vec_empty)`

## Implementation notes

The `simp` lemmas require that one of the arguments is of the form `vec_cons _ _`.
This ensures `simp` works with entries only when (some) entries are already given.
In other words, this notation will only appear in the output of `simp` if it
already appears in the input.

## Notations

The main new notation is `![a, b]`, which gets expanded to `vec_cons a (vec_cons b vec_empty)`.
-/

namespace matrix

universe u
variables {α : Type u}

open_locale matrix

section matrix_notation

/-- `![]` is the vector with no entries. -/
def vec_empty : fin 0 → α :=
fin_zero_elim

/-- `vec_cons h t` prepends an entry `h` to a vector `t`.

The inverse functions are `vec_head` and `vec_tail`.
The notation `![a, b, ...]` expands to `vec_cons a (vec_cons b ...)`.
-/
def vec_cons {n : ℕ} (h : α) (t : fin n → α) : fin n.succ → α :=
fin.cons h t

notation `![` l:(foldr `, ` (h t, vec_cons h t) vec_empty `]`) := l

/-- `vec_head v` gives the first entry of the vector `v` -/
def vec_head {n : ℕ} (v : fin n.succ → α) : α :=
v 0

/-- `vec_tail v` gives a vector consisting of all entries of `v` except the first -/
def vec_tail {n : ℕ} (v : fin n.succ → α) : fin n → α :=
v ∘ fin.succ

end matrix_notation

variables {m n o : ℕ} {m' n' o' : Type} [fintype m'] [fintype n'] [fintype o']

lemma empty_eq (v : fin 0 → α) : v = ![] :=
by { ext i, fin_cases i }

section val

@[simp] lemma cons_val_zero (x : α) (u : fin m → α) : vec_cons x u 0 = x := rfl

@[simp] lemma cons_val_zero' (h : 0 < m.succ) (x : α) (u : fin m → α) :
  vec_cons x u ⟨0, h⟩ = x :=
rfl

@[simp] lemma cons_val_succ (x : α) (u : fin m → α) (i : fin m) :
  vec_cons x u i.succ = u i :=
by simp [vec_cons]

@[simp] lemma cons_val_succ' {i : ℕ} (h : i.succ < m.succ) (x : α) (u : fin m → α) :
  vec_cons x u ⟨i.succ, h⟩ = u ⟨i, nat.lt_of_succ_lt_succ h⟩ :=
by simp [vec_cons, fin.cons, fin.cases]

@[simp] lemma head_cons (x : α) (u : fin m → α) :
  vec_head (vec_cons x u) = x :=
rfl

@[simp] lemma tail_cons (x : α) (u : fin m → α) :
  vec_tail (vec_cons x u) = u :=
by { ext, simp [vec_tail] }

@[simp] lemma empty_val' {n' : Type} (j : n') :
  (λ i, (![] : fin 0 → n' → α) i j) = ![] :=
empty_eq _

@[simp] lemma cons_val' (v : n' → α) (B : matrix (fin m) n' α) (i j) :
  vec_cons v B i j = vec_cons (v j) (λ i, B i j) i :=
by { refine fin.cases _ _ i; simp }

@[simp] lemma head_val' (B : matrix (fin m.succ) n' α) (j : n') :
  vec_head (λ i, B i j) = vec_head B j := rfl

@[simp] lemma tail_val' (B : matrix (fin m.succ) n' α) (j : n') :
  vec_tail (λ i, B i j) = λ i, vec_tail B i j :=
by { ext, simp [vec_tail] }

@[simp] lemma cons_head_tail (u : fin m.succ → α) :
 vec_cons (vec_head u) (vec_tail u) = u :=
by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

/-- `![a, b, ...] 1` is equal to `b`.

  The simplifier needs a special lemma for length `≥ 2`, in addition to
  `cons_val_succ`, because `1 : fin 1 = 0 : fin 1`.
-/
@[simp] lemma cons_val_one (x : α) (u : fin m.succ → α) :
  vec_cons x u 1 = vec_head u :=
cons_val_succ x u 0

@[simp] lemma cons_val_fin_one (x : α) (u : fin 0 → α) (i : fin 1) :
  vec_cons x u i = x :=
by { fin_cases i, refl }

end val

section dot_product

variables [add_comm_monoid α] [has_mul α]

@[simp] lemma dot_product_empty (v w : fin 0 → α) :
  dot_product v w = 0 := finset.sum_empty

@[simp] lemma cons_dot_product (x : α) (v : fin n → α) (w : fin n.succ → α) :
  dot_product (vec_cons x v) w = x * vec_head w + dot_product v (vec_tail w) :=
by simp [dot_product, fin.sum_univ_succ, vec_head, vec_tail]

@[simp] lemma dot_product_cons (v : fin n.succ → α) (x : α) (w : fin n → α) :
  dot_product v (vec_cons x w) = vec_head v * x + dot_product (vec_tail v) w :=
by simp [dot_product, fin.sum_univ_succ, vec_head, vec_tail]

end dot_product

section col_row

@[simp] lemma col_empty (v : fin 0 → α) : col v = vec_empty :=
empty_eq _

@[simp] lemma col_cons (x : α) (u : fin m → α) :
  col (vec_cons x u) = vec_cons (λ _, x) (col u) :=
by { ext i j, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

@[simp] lemma row_empty : row (vec_empty : fin 0 → α) = λ _, vec_empty :=
by { ext, refl }

@[simp] lemma row_cons (x : α) (u : fin m → α) :
  row (vec_cons x u) = λ _, vec_cons x u :=
by { ext, refl }

end col_row

section transpose

@[simp] lemma transpose_empty_rows (A : matrix m' (fin 0) α) : Aᵀ = ![] := empty_eq _

@[simp] lemma transpose_empty_cols : (![] : matrix (fin 0) m' α)ᵀ = λ i, ![] :=
funext (λ i, empty_eq _)

@[simp] lemma cons_transpose (v : n' → α) (A : matrix (fin m) n' α) :
  (vec_cons v A)ᵀ = λ i, vec_cons (v i) (Aᵀ i) :=
by { ext i j, refine fin.cases _ _ j; simp }

@[simp] lemma head_transpose (A : matrix m' (fin n.succ) α) : vec_head (Aᵀ) = vec_head ∘ A :=
rfl

@[simp] lemma tail_transpose (A : matrix m' (fin n.succ) α) : vec_tail (Aᵀ) = (vec_tail ∘ A)ᵀ :=
by { ext i j, refl }

end transpose

section mul

variables [semiring α]

@[simp] lemma empty_mul (A : matrix (fin 0) n' α) (B : matrix n' o' α) :
  A ⬝ B = ![] :=
empty_eq _

@[simp] lemma empty_mul_empty (A : matrix m' (fin 0) α) (B : matrix (fin 0) o' α) :
  A ⬝ B = 0 :=
rfl

@[simp] lemma mul_empty (A : matrix m' n' α) (B : matrix n' (fin 0) α) :
  A ⬝ B = λ _, ![] :=
funext (λ _, empty_eq _)

lemma mul_val_succ (A : matrix (fin m.succ) n' α) (B : matrix n' o' α) (i : fin m) (j : o') :
  (A ⬝ B) i.succ j = (vec_tail A ⬝ B) i j := rfl

@[simp] lemma cons_mul (v : n' → α) (A : matrix (fin m) n' α) (B : matrix n' o' α) :
  vec_cons v A ⬝ B = vec_cons (vec_mul v B) (A  ⬝ B) :=
by { ext i j, refine fin.cases _ _ i, { refl }, simp [mul_val_succ] }

end mul

section vec_mul

variables [semiring α]

@[simp] lemma empty_vec_mul (v : fin 0 → α) (B : matrix (fin 0) o' α) :
  vec_mul v B = 0 :=
rfl

@[simp] lemma vec_mul_empty (v : n' → α) (B : matrix n' (fin 0) α) :
  vec_mul v B = ![] :=
empty_eq _

@[simp] lemma cons_vec_mul (x : α) (v : fin n → α) (B : matrix (fin n.succ) o' α) :
  vec_mul (vec_cons x v) B = x • (vec_head B) + vec_mul v (vec_tail B) :=
by { ext i, simp [vec_mul] }

@[simp] lemma vec_mul_cons (v : fin n.succ → α) (w : o' → α) (B : matrix (fin n) o' α) :
  vec_mul v (vec_cons w B) = vec_head v • w + vec_mul (vec_tail v) B :=
by { ext i, simp [vec_mul] }

end vec_mul

section mul_vec

variables [semiring α]

@[simp] lemma empty_mul_vec (A : matrix (fin 0) n' α) (v : n' → α) :
  mul_vec A v = ![] :=
empty_eq _

@[simp] lemma mul_vec_empty (A : matrix m' (fin 0) α) (v : fin 0 → α) :
  mul_vec A v = 0 :=
rfl

@[simp] lemma cons_mul_vec (v : n' → α) (A : fin m → n' → α) (w : n' → α) :
  mul_vec (vec_cons v A) w = vec_cons (dot_product v w) (mul_vec A w) :=
by { ext i, refine fin.cases _ _ i; simp [mul_vec] }

@[simp] lemma mul_vec_cons {α} [comm_semiring α] (A : m' → (fin n.succ) → α) (x : α) (v : fin n → α) :
  mul_vec A (vec_cons x v) = (x • vec_head ∘ A) + mul_vec (vec_tail ∘ A) v :=
by { ext i, simp [mul_vec, mul_comm] }

end mul_vec

section vec_mul_vec

variables [semiring α]

@[simp] lemma empty_vec_mul_vec (v : fin 0 → α) (w : n' → α) :
  vec_mul_vec v w = ![] :=
empty_eq _

@[simp] lemma vec_mul_vec_empty (v : m' → α) (w : fin 0 → α) :
  vec_mul_vec v w = λ _, ![] :=
funext (λ i, empty_eq _)

@[simp] lemma cons_vec_mul_vec (x : α) (v : fin m → α) (w : n' → α) :
  vec_mul_vec (vec_cons x v) w = vec_cons (x • w) (vec_mul_vec v w) :=
by { ext i, refine fin.cases _ _ i; simp [vec_mul_vec] }

@[simp] lemma vec_mul_vec_cons (v : m' → α) (x : α) (w : fin n → α) :
  vec_mul_vec v (vec_cons x w) = λ i, v i • vec_cons x w :=
by { ext i j, simp [vec_mul_vec]}

end vec_mul_vec

section smul

variables [semiring α]

@[simp] lemma smul_empty (x : α) (v : fin 0 → α) : x • v = ![] := empty_eq _

@[simp] lemma smul_mat_empty {m' : Type} (x : α) (A : fin 0 → m' → α) : x • A = ![] := empty_eq _

@[simp] lemma smul_cons (x y : α) (v : fin n → α) :
  x • vec_cons y v = vec_cons (x * y) (x • v) :=
by { ext i, refine fin.cases _ _ i; simp }

@[simp] lemma smul_mat_cons (x : α) (v : n' → α) (A : matrix (fin m) n' α) :
  x • vec_cons v A = vec_cons (x • v) (x • A) :=
by { ext i, refine fin.cases _ _ i; simp }

end smul

section add

variables [has_add α]

@[simp] lemma empty_add_empty (v w : fin 0 → α) : v + w = ![] := empty_eq _

@[simp] lemma cons_add (x : α) (v : fin n → α) (w : fin n.succ → α) :
  vec_cons x v + w = vec_cons (x + vec_head w) (v + vec_tail w) :=
by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

@[simp] lemma add_cons (v : fin n.succ → α) (y : α) (w : fin n → α) :
  v + vec_cons y w = vec_cons (vec_head v + y) (vec_tail v + w) :=
by { ext i, refine fin.cases _ _ i; simp [vec_head, vec_tail] }

end add

section zero

variables [has_zero α]

@[simp] lemma zero_empty : (0 : fin 0 → α) = ![] :=
empty_eq _

@[simp] lemma cons_zero_zero : vec_cons (0 : α) (0 : fin n → α) = 0 :=
by { ext i j, refine fin.cases _ _ i, { refl }, simp }

@[simp] lemma head_zero : vec_head (0 : fin n.succ → α) = 0 := rfl

@[simp] lemma tail_zero : vec_tail (0 : fin n.succ → α) = 0 := rfl

@[simp] lemma cons_eq_zero_iff {v : fin n → α} {x : α} :
  vec_cons x v = 0 ↔ x = 0 ∧ v = 0 :=
⟨ λ h, ⟨ congr_fun h 0, by { convert congr_arg vec_tail h, simp } ⟩,
  λ ⟨hx, hv⟩, by simp [hx, hv] ⟩

open_locale classical

lemma cons_nonzero_iff {v : fin n → α} {x : α} :
  vec_cons x v ≠ 0 ↔ (x ≠ 0 ∨ v ≠ 0) :=
⟨ λ h, not_and_distrib.mp (h ∘ cons_eq_zero_iff.mpr),
  λ h, mt cons_eq_zero_iff.mp (not_and_distrib.mpr h) ⟩

end zero

section neg

variables [has_neg α]

@[simp] lemma neg_empty (v : fin 0 → α) : -v = ![] := empty_eq _

@[simp] lemma neg_cons (x : α) (v : fin n → α) :
  -(vec_cons x v) = vec_cons (-x) (-v) :=
by { ext i, refine fin.cases _ _ i; simp }

end neg

section minor

@[simp] lemma minor_empty (A : matrix m' n' α) (row : fin 0 → m') (col : o' → n') :
  minor A row col = ![] :=
empty_eq _

@[simp] lemma minor_cons_row (A : matrix m' n' α) (i : m') (row : fin m → m') (col : o' → n') :
  minor A (vec_cons i row) col = vec_cons (λ j, A i (col j)) (minor A row col) :=
by { ext i j, refine fin.cases _ _ i; simp [minor] }

end minor

end matrix
