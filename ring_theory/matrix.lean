/-
Copyright (c) 2018 Ellen Arlt. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather, Mario Carneiro, Johan Commelin

Matrices
-/

import algebra.module data.fintype algebra.pi_instances

universes u v

def matrix (m n : Type u) [fintype m] [fintype n] (α : Type v) : Type (max u v) :=
m → n → α

namespace matrix
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {α : Type v}

section ext
variables {M N : matrix m n α}

theorem ext_iff : (∀ i j, M i j = N i j) ↔ M = N :=
⟨λ h, funext $ λ i, funext $ h i, λ h, by simp [h]⟩

@[extensionality] theorem ext : (∀ i j, M i j = N i j) → M = N :=
ext_iff.mp

end ext

instance [has_add α] : has_add (matrix m n α) := pi.has_add
instance [add_semigroup α] : add_semigroup (matrix m n α) := pi.add_semigroup
instance [add_comm_semigroup α] : add_comm_semigroup (matrix m n α) := pi.add_comm_semigroup
instance [has_zero α] : has_zero (matrix m n α) := pi.has_zero
instance [add_monoid α] : add_monoid (matrix m n α) := pi.add_monoid
instance [add_comm_monoid α] : add_comm_monoid (matrix m n α) := pi.add_comm_monoid
instance [has_neg α] : has_neg (matrix m n α) := pi.has_neg
instance [add_group α] : add_group (matrix m n α) := pi.add_group
instance [add_comm_group α] : add_comm_group (matrix m n α) := pi.add_comm_group

@[simp] theorem zero_val [has_zero α] (i j) : (0 : matrix m n α) i j = 0 := rfl
@[simp] theorem neg_val [has_neg α] (M : matrix m n α) (i j) : (- M) i j = - M i j := rfl
@[simp] theorem add_val [has_add α] (M N : matrix m n α) (i j) : (M + N) i j = M i j + N i j := rfl

section diagonal
variables [decidable_eq n]

def diagonal [has_zero α] (d : n → α) : matrix n n α := λ i j, if i = j then d i else 0

@[simp] theorem diagonal_val_eq [has_zero α] {d : n → α} (i : n) : (diagonal d) i i = d i :=
by simp [diagonal]

@[simp] theorem diagonal_val_ne [has_zero α] {d : n → α} {i j : n} (h : i ≠ j) :
  (diagonal d) i j = 0 := by simp [diagonal, h]

theorem diagonal_val_ne' [has_zero α] {d : n → α} {i j : n} (h : j ≠ i) :
  (diagonal d) i j = 0 := diagonal_val_ne h.symm

@[simp] theorem diagonal_zero [has_zero α] : (diagonal (λ _, 0) : matrix n n α) = 0 :=
by simp [diagonal]; refl

section one
variables [has_zero α] [has_one α]

instance : has_one (matrix n n α) := ⟨diagonal (λ _, 1)⟩

@[simp] theorem diagonal_one : (diagonal (λ _, 1) : matrix n n α) = 1 := rfl

theorem one_val {i j} : (1 : matrix n n α) i j = if i = j then 1 else 0 := rfl

@[simp] theorem one_val_eq (i) : (1 : matrix n n α) i i = 1 := diagonal_val_eq i

@[simp] theorem one_val_ne {i j} : i ≠ j → (1 : matrix n n α) i j = 0 :=
diagonal_val_ne

theorem one_val_ne' {i j} : j ≠ i → (1 : matrix n n α) i j = 0 :=
diagonal_val_ne'

end one
end diagonal

@[simp] theorem diagonal_add [decidable_eq n] [add_monoid α] (d₁ d₂ : n → α) :
  diagonal d₁ + diagonal d₂ = diagonal (λ i, d₁ i + d₂ i) :=
by ext i j; by_cases i = j; simp [h]

protected def mul [has_mul α] [add_comm_monoid α] (M : matrix l m α) (N : matrix m n α) :
  matrix l n α :=
λ i k, finset.univ.sum (λ j, M i j * N j k)

theorem mul_val [has_mul α] [add_comm_monoid α] {M : matrix l m α} {N : matrix m n α} {i k} :
  (M.mul N) i k = finset.univ.sum (λ j, M i j * N j k) := rfl

local attribute [simp] mul_val

instance [has_mul α] [add_comm_monoid α] : has_mul (matrix n n α) := ⟨matrix.mul⟩

@[simp] theorem mul_eq_mul [has_mul α] [add_comm_monoid α] (M N : matrix n n α) :
  M * N = M.mul N := rfl

theorem mul_val' [has_mul α] [add_comm_monoid α] {M N : matrix n n α} {i k} :
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

@[simp] theorem diagonal_neg [decidable_eq n] [add_group α] (d : n → α) :
  -diagonal d = diagonal (λ i, -d i) :=
by ext i j; by_cases i = j; simp [h]

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

@[simp] theorem diagonal_mul [decidable_eq m]
  (d : m → α) (M : matrix m n α) (i j) : (diagonal d).mul M i j = d i * M i j :=
by simp; rw finset.sum_eq_single i; simp [diagonal_val_ne'] {contextual := tt}

@[simp] theorem mul_diagonal [decidable_eq n]
  (d : n → α) (M : matrix m n α) (i j) : M.mul (diagonal d) i j = M i j * d j :=
by simp; rw finset.sum_eq_single j; simp {contextual := tt}

protected theorem one_mul [decidable_eq m] (M : matrix m n α) : (1 : matrix m m α).mul M = M :=
by ext i j; rw [← diagonal_one, diagonal_mul, one_mul]

protected theorem mul_one [decidable_eq n] (M : matrix m n α) : M.mul (1 : matrix n n α) = M :=
by ext i j; rw [← diagonal_one, mul_diagonal, mul_one]

instance [decidable_eq n] : monoid (matrix n n α) :=
{ one_mul := matrix.one_mul,
  mul_one := matrix.mul_one,
  ..matrix.has_one, ..matrix.semigroup }

instance [decidable_eq n] : semiring (matrix n n α) :=
{ mul_zero := mul_zero,
  zero_mul := zero_mul,
  left_distrib := mul_add,
  right_distrib := add_mul,
  ..matrix.add_comm_monoid,
  ..matrix.monoid }

@[simp] theorem diagonal_mul_diagonal' [decidable_eq n] (d₁ d₂ : n → α) :
  (diagonal d₁).mul (diagonal d₂) = diagonal (λ i, d₁ i * d₂ i) :=
by ext i j; by_cases i = j; simp [h]

theorem diagonal_mul_diagonal [decidable_eq n] (d₁ d₂ : n → α) :
  diagonal d₁ * diagonal d₂ = diagonal (λ i, d₁ i * d₂ i) :=
diagonal_mul_diagonal' _ _

end semiring

instance [decidable_eq n] [ring α] : ring (matrix n n α) :=
{ ..matrix.add_comm_group, ..matrix.semiring }

instance [has_mul α] : has_scalar α (matrix m n α) := ⟨λ a M i j, a * M i j⟩

instance [ring α] : module α (matrix m n α) :=
module.of_core
{ smul_add := λ a M N, ext $ λ i j, _root_.mul_add a (M i j) (N i j),
  add_smul := λ a b M, ext $ λ i j, _root_.add_mul a b (M i j),
  mul_smul := λ a b M, ext $ λ i j, mul_assoc a b (M i j),
  one_smul := λ M, ext $ λ i j, one_mul (M i j),
  .. (infer_instance : has_scalar α (matrix m n α)) }

end matrix
