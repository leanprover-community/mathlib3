/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro

Matrices
-/

import algebra.module data.fintype

universes u v

def matrix (m n : Type u) [fintype m] [fintype n] (α : Type v) : Type (max u v) :=
m → n → α

namespace matrix
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {α : Type v}

section ext
variables {M N : matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
⟨λ h, funext $ λ i, funext $ λ j, h i j, λ h, by simp [h]⟩

@[extensionality] theorem ext : (∀ i j, M i j = N i j) → M = N :=
ext_iff.mp

end ext

section zero
variables [has_zero α]

instance : has_zero (matrix m n α) := ⟨λ _ _, 0⟩

@[simp] theorem zero_val {i j} : (0 : matrix m n α) i j = 0 := rfl

end zero

section one
variables [decidable_eq n] [has_zero α] [has_one α]

instance : has_one (matrix n n α) := ⟨λ i j, if i = j then 1 else 0⟩

theorem one_val {i j} : (1 : matrix n n α) i j = if i = j then 1 else 0 := rfl

@[simp] theorem one_val_eq (i) : (1 : matrix n n α) i i = 1 := by simp [one_val]

@[simp] theorem one_val_ne {i j} (h : i ≠ j) : (1 : matrix n n α) i j = 0 :=
by simp [one_val, h]

theorem one_val_ne' {i j} (h : j ≠ i) : (1 : matrix n n α) i j = 0 :=
one_val_ne h.symm

end one

section neg
variables [has_neg α]

instance : has_neg (matrix m n α) := ⟨λ M i j, - M i j⟩

@[simp] theorem neg_val {M : matrix m n α} {i j} : (- M) i j = - M i j := rfl

end neg

section add
variables [has_add α]

instance : has_add (matrix m n α) := ⟨λ M N i j, M i j + N i j⟩

@[simp] theorem add_val {M N : matrix m n α} {i j} : (M + N) i j = M i j + N i j := rfl

end add

instance [add_semigroup α] : add_semigroup (matrix m n α) :=
{ add_assoc := by intros; ext; simp, ..matrix.has_add }

instance [add_comm_semigroup α] : add_comm_semigroup (matrix m n α) :=
{ add_comm := by intros; ext; simp, ..matrix.add_semigroup }

instance [add_monoid α] : add_monoid (matrix m n α) :=
{ zero := 0, add := (+),
  zero_add := by intros; ext; simp,
  add_zero := by intros; ext; simp,
  ..matrix.add_semigroup }

instance [add_comm_monoid α] : add_comm_monoid (matrix m n α) :=
{ ..matrix.add_monoid, ..matrix.add_comm_semigroup }

protected def mul [has_mul α] [add_comm_monoid α] (M : matrix l m α) (N : matrix m n α) :
  matrix l n α :=
λ i k, finset.univ.sum (λ j, M i j * N j k)

@[simp] theorem mul_val [has_mul α] [add_comm_monoid α] {M : matrix l m α} {N : matrix m n α} {i k} :
  (M.mul N) i k = finset.univ.sum (λ j, M i j * N j k) := rfl

instance [has_mul α] [add_comm_monoid α] : has_mul (matrix n n α) := ⟨matrix.mul⟩

@[simp] theorem mul_val' [has_mul α] [add_comm_monoid α] {M N : matrix n n α} {i k} :
  (M * N) i k = finset.univ.sum (λ j, M i j * N j k) := rfl

section semigroup
variables [decidable_eq m] [decidable_eq n] [semiring α]

protected theorem mul_assoc (L : matrix l m α) (M : matrix m n α) (N : matrix n o α) :
  (L.mul M).mul N = L.mul (M.mul N) :=
by funext i k;
   simp [finset.mul_sum, finset.sum_mul, mul_assoc];
   rw finset.sum_comm

instance : semigroup (matrix n n α) :=
{ mul_assoc := matrix.mul_assoc, ..matrix.has_mul }

end semigroup

section monoid
variables [decidable_eq n] [decidable_eq m] [semiring α]

protected theorem one_mul (M : matrix n m α) : (1 : matrix n n α).mul M = M :=
by ext i j; simp; rw finset.sum_eq_single i; simp [one_val_ne'] {contextual := tt}

protected theorem mul_one (M : matrix n m α) : M.mul (1 : matrix m m α) = M :=
by ext i j; simp; rw finset.sum_eq_single j; simp {contextual := tt}

instance : monoid (matrix n n α) :=
{ one_mul := matrix.one_mul,
  mul_one := matrix.mul_one,
  ..matrix.has_one, ..matrix.semigroup }

end monoid

instance [add_group α] : add_group (matrix m n α) :=
{ zero := 0, add := (+), neg := has_neg.neg,
  add_left_neg := by intros; ext; simp,
  ..matrix.add_monoid }

instance [add_comm_group α] : add_comm_group (matrix m n α) :=
{ ..matrix.add_group, ..matrix.add_comm_monoid }

section semiring
variables [semiring α]

theorem mul_zero (M : matrix m n α) : M.mul (0 : matrix n n α) = 0 :=
by ext i j; simp

theorem zero_mul (M : matrix m n α) : (0 : matrix m m α).mul M = 0 :=
by ext i j; simp

theorem mul_add (L : matrix m n α) (M N : matrix n n α) : L.mul (M + N) = L.mul M + L.mul N :=
by ext i j; simp [finset.sum_add_distrib, mul_add]

theorem add_mul (L M : matrix m m α) (N : matrix m n α) : (L + M).mul N = L.mul N + M.mul N :=
by ext i j; simp [finset.sum_add_distrib, add_mul]

instance [decidable_eq n] [semiring α] : semiring (matrix n n α) :=
{ mul_zero := mul_zero,
  zero_mul := zero_mul,
  left_distrib := mul_add,
  right_distrib := add_mul,
  ..matrix.add_comm_monoid,
  ..matrix.monoid }

end semiring

instance [decidable_eq n] [ring α] : ring (matrix n n α) :=
{ ..matrix.add_comm_group, ..matrix.semiring }

instance [has_mul α] : has_scalar α (matrix m n α) := ⟨λ a M i j, a * M i j⟩

instance [ring α] : module α (matrix m n α) :=
{ smul_add := λ a M N, ext $ λ i j, _root_.mul_add a (M i j) (N i j),
  add_smul := λ a b M, ext $ λ i j, _root_.add_mul a b (M i j),
  mul_smul := λ a b M, ext $ λ i j, mul_assoc a b (M i j),
  one_smul := λ M, ext $ λ i j, one_mul (M i j) }

end matrix
