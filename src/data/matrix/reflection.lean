/-
Copyright (c) 2022 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import algebra.expr
import data.matrix.notation
import data.matrix.basic
import data.fin.tuple.reflection

/-!
# Lemmas for concrete matrices `matrix (fin m) (fin n) α`

This file contains alternative definitions of common operators on matrices that expand
definitionally to the expected expression when evaluated on `!![]` notation.

This allows "proof by reflection", where we prove `A = !![A 0 0, A 0 1;  A 1 0, A 1 1]` by defining
`matrix.eta_expand A` to be equal to the RHS definitionally, and then prove that
`A = eta_expand A`.

The definitions in this file should normally not be used directly; the intent is for the
corresponding `*_eq` lemmas to be used in a place where they are definitionally unfolded.

## Main definitionss

* `matrix.transposeᵣ`
* `matrix.dot_productᵣ`
* `matrix.mulᵣ`
* `matrix.eta_expand`

-/

open_locale matrix

namespace matrix
variables {l m n : ℕ} {α β : Type*}

/-- `∀` with better defeq for `∀ x : matrix (fin m) (fin n) α, P x`. -/
def «forall» : Π {m n} (P : (matrix (fin m) (fin n) α) → Prop), Prop
| 0 n P := P (of ![])
| (m + 1) n P := fin_vec.forall $ λ r, «forall» (λ A, P (of (matrix.vec_cons r A)))

/--
This can be use to prove
```lean
example (P : matrix (fin 2) (fin 3) α → Prop) :
  (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
(forall_iff _).symm
```
-/
lemma forall_iff : Π {m n} (P : (matrix (fin m) (fin n) α) → Prop), «forall» P ↔ ∀ x, P x
| 0 n P := iff.symm fin.forall_fin_zero_pi
| (m + 1) n P := begin
  simp only [«forall», fin_vec.forall_iff, forall_iff],
  exact iff.symm fin.forall_fin_succ_pi,
end

example (P : matrix (fin 2) (fin 3) α → Prop) :
  (∀ x, P x) ↔ ∀ a b c d e f, P !![a, b, c; d, e, f] :=
(forall_iff _).symm

/--`∃` with better defeq for `∃ x : matrix (fin m) (fin n) α, P x`. -/
def «exists» : Π {m n} (P : (matrix (fin m) (fin n) α) → Prop), Prop
| 0 n P := P (of ![])
| (m + 1) n P := fin_vec.exists $ λ r, «exists» (λ A, P (of (matrix.vec_cons r A)))

/--
This can be use to prove
```lean
example (P : matrix (fin 2) (fin 3) α → Prop) :
  (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
(exists_iff _).symm
```
-/
lemma exists_iff : Π {m n} (P : (matrix (fin m) (fin n) α) → Prop), «exists» P ↔ ∃ x, P x
| 0 n P := iff.symm fin.exists_fin_zero_pi
| (m + 1) n P := begin
  simp only [«exists», fin_vec.exists_iff, exists_iff],
  exact iff.symm fin.exists_fin_succ_pi,
end

example (P : matrix (fin 2) (fin 3) α → Prop) :
  (∃ x, P x) ↔ ∃ a b c d e f, P !![a, b, c; d, e, f] :=
(exists_iff _).symm

/-- `matrix.tranpose` with better defeq for `fin` -/
def transposeᵣ : Π {m n}, matrix (fin m) (fin n) α → matrix (fin n) (fin m) α
| _ 0 A := of ![]
| m (n + 1) A := of $ vec_cons (fin_vec.map (λ v : fin _ → α, v 0) A)
                               (transposeᵣ (A.submatrix id fin.succ))

/-- This can be used to prove
```lean
example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] := (transposeᵣ_eq _).symm
```
-/
@[simp]
lemma transposeᵣ_eq : Π {m n} (A : matrix (fin m) (fin n) α),
  transposeᵣ A = transpose A
| _ 0 A := subsingleton.elim _ _
| m (n + 1) A := matrix.ext $ λ i j, begin
  simp_rw [transposeᵣ, transposeᵣ_eq],
  refine i.cases _ (λ i, _),
  { dsimp, rw fin_vec.map_eq },
  { simp only [of_apply, matrix.cons_val_succ], refl },
end

example (a b c d : α) : transpose !![a, b; c, d] = !![a, c; b, d] := (transposeᵣ_eq _).symm

/-- `matrix.dot_product` with better defeq for `fin` -/
def dot_productᵣ [has_mul α] [has_add α] [has_zero α] {m} (a b : fin m → α) : α :=
fin_vec.sum $ fin_vec.seq (fin_vec.map (*) a) b

/-- This can be used to prove
```lean
example (a b c d : α) [has_mul α] [add_comm_monoid α] :
  dot_product ![a, b] ![c, d] = a * c + b * d :=
(dot_productᵣ_eq _ _).symm
```
-/
@[simp]
lemma dot_productᵣ_eq [has_mul α] [add_comm_monoid α] {m} (a b : fin m → α) :
  dot_productᵣ a b = dot_product a b :=
by simp_rw [dot_productᵣ, dot_product, fin_vec.sum_eq, fin_vec.seq_eq, fin_vec.map_eq]

example (a b c d : α) [has_mul α] [add_comm_monoid α] :
  dot_product ![a, b] ![c, d] = a * c + b * d :=
(dot_productᵣ_eq _ _).symm

/-- `matrix.mul` with better defeq for `fin` -/
def mulᵣ [has_mul α] [has_add α] [has_zero α]
  (A : matrix (fin l) (fin m) α) (B : matrix (fin m) (fin n) α) :
  matrix (fin l) (fin n) α :=
of $ fin_vec.map (λ v₁, fin_vec.map (λ v₂, dot_productᵣ v₁ v₂) (transposeᵣ B)) A

/-- This can be used to prove
```lean
example [add_comm_monoid α] [has_mul α]
  (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂] ⬝ !![b₁₁, b₁₂;
                    b₂₁, b₂₂] =
  !![a₁₁*b₁₁ + a₁₂*b₂₁, a₁₁*b₁₂ + a₁₂*b₂₂;
     a₂₁*b₁₁ + a₂₂*b₂₁, a₂₁*b₁₂ + a₂₂*b₂₂] :=
```
-/
@[simp]
lemma mulᵣ_eq [has_mul α] [add_comm_monoid α]
  (A : matrix (fin l) (fin m) α) (B : matrix (fin m) (fin n) α) :
  mulᵣ A B = A.mul B :=
begin
  simp [mulᵣ, function.comp, matrix.mul, matrix.transpose],
  refl,
end

example [add_comm_monoid α] [has_mul α]
  (a₁₁ a₁₂ a₁₃ a₂₁ a₂₂ a₂₃ a₃₁ a₃₂ a₃₃ b₁₁ b₁₂ b₁₃ b₂₁ b₂₂ b₂₃ b₃₁ b₃₂ b₃₃ : α) :
  !![a₁₁, a₁₂;
     a₂₁, a₂₂].mul !![b₁₁, b₁₂;
                      b₂₁, b₂₂] =
  !![a₁₁*b₁₁ + a₁₂*b₂₁, a₁₁*b₁₂ + a₁₂*b₂₂;
     a₂₁*b₁₁ + a₂₂*b₂₁, a₂₁*b₁₂ + a₂₂*b₂₂] :=
(mulᵣ_eq _ _).symm

/-- Expand `A` to `!![A 0 0, ...; ..., A m n]` -/
def eta_expand {m n} (A : matrix (fin m) (fin n) α) : matrix (fin m) (fin n) α :=
matrix.of (fin_vec.eta_expand (λ i, fin_vec.eta_expand (λ j, A i j)))

/-- This can be used to prove
```lean
example (A : matrix (fin 2) (fin 2) α) :
  A = !![A 0 0, A 0 1;
         A 1 0, A 1 1] :=
(eta_expand_eq _).symm
```
-/
lemma eta_expand_eq {m n} (A : matrix (fin m) (fin n) α) :
  eta_expand A = A :=
by simp_rw [eta_expand, fin_vec.eta_expand_eq, matrix.of, equiv.refl_apply]

example (A : matrix (fin 2) (fin 2) α) :
  A = !![A 0 0, A 0 1;
         A 1 0, A 1 1] :=
(eta_expand_eq _).symm

end matrix

/-- Like `list.mmap` but for a vector. -/
def fin.mmap {α} {n : ℕ} {m : Type* → Type*} [monad m] (f : fin n → m α) : m (fin n → α) :=
vector.nth <$> vector.mmap f ⟨list.fin_range n, list.length_fin_range _⟩
