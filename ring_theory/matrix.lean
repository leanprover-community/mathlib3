/-
Copyright (c) 2018 Ellen Arlt, Blair Shi, Sean Leather. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ellen Arlt, Blair Shi, Sean Leather

Matrices
-/

import algebra.module data.fintype category_theory.category

universes u v

def matrix (m n : Type u) [fintype m] [fintype n] (α : Type v) : Type (max u v) :=
m → n → α

namespace matrix
variables {l m n o : Type u} [fintype l] [fintype m] [fintype n] [fintype o]
variables {α : Type v}

section ext
variables {M N : matrix m n α}

def ext : (∀ i j, M i j = N i j) ↔ M = N :=
⟨λ h, funext $ λ i, funext $ λ j, h i j, λ h, by simp [h]⟩

@[extensionality] theorem ext' : (∀ i j, M i j = N i j) → M = N :=
ext.mp

end ext

section zero
variables [has_zero α]

instance : has_zero (matrix m n α) :=
⟨λ _ _, 0⟩

@[simp] theorem zero_val {i j} : (0 : matrix m n α) i j = 0 :=
rfl

end zero

section one
variables [decidable_eq n] [has_zero α] [has_one α]

instance : has_one (matrix n n α) :=
⟨λ i j, if i = j then 1 else 0⟩

theorem one_val {i j} : (1 : matrix n n α) i j = if i = j then 1 else 0 :=
rfl

@[simp] theorem one_val_eq {i} : (1 : matrix n n α) i i = 1 :=
by simp [one_val]

@[simp] theorem one_val_ne {i j} (h : i ≠ j) : (1 : matrix n n α) i j = 0 :=
by simp [one_val, h]

end one

section neg
variables [has_neg α]

instance : has_neg (matrix m n α) :=
⟨λ M i j, - M i j⟩

@[simp] theorem neg_val {M : matrix m n α} {i j} : (- M) i j = - M i j :=
rfl

end neg

section add
variables [has_add α]

instance : has_add (matrix m n α) :=
⟨λ M N i j, M i j + N i j⟩

@[simp] theorem add_val {M N : matrix m n α} {i j} :
  (M + N) i j = M i j + N i j :=
rfl

end add

instance [add_semigroup α] : add_semigroup (matrix m n α) :=
{ add_assoc := λ L M N, ext' $ by simp,
  ..matrix.has_add }

instance [add_comm_semigroup α] : add_comm_semigroup (matrix m n α) :=
{ add_comm := λ M N, ext' $ by simp,
  ..matrix.add_semigroup }

instance [add_monoid α] : add_monoid (matrix m n α) :=
{ zero_add := λ M, show 0 + M = M, from ext' $ by simp,
  add_zero := λ M, ext' $ by simp,
  ..matrix.has_zero,
  ..matrix.add_semigroup }

instance [add_comm_monoid α] : add_comm_monoid (matrix m n α) :=
{ ..matrix.add_monoid,
  ..matrix.add_comm_semigroup }

protected def mul [has_mul α] [add_comm_monoid α] (M : matrix l m α) (N : matrix m n α) :
  matrix l n α :=
λ i k, finset.univ.sum (λ j, M i j * N j k)

@[simp] theorem mul_val [has_mul α] [add_comm_monoid α] {M : matrix l m α} {N : matrix m n α} {i k} :
  (M.mul N) i k = finset.univ.sum (λ j, M i j * N j k) :=
rfl

instance [has_mul α] [add_comm_monoid α] : has_mul (matrix n n α) :=
⟨matrix.mul⟩

@[simp] theorem mul_val' [has_mul α] [add_comm_monoid α] {M N : matrix n n α} {i k} :
  (M * N) i k = finset.univ.sum (λ j, M i j * N j k) :=
rfl

section semigroup
variables [decidable_eq m] [decidable_eq n] [semiring α]

protected theorem mul_assoc (L : matrix l m α) (M : matrix m n α) (N : matrix n o α) :
  (L.mul M).mul N = L.mul (M.mul N) :=
funext $ λ i, funext $ λ k,
  calc finset.univ.sum (λ (j₂ : n), finset.univ.sum (λ (j₁ : m), L i j₁ * M j₁ j₂) * N j₂ k)
    = finset.univ.sum (λ (j₂ : n), finset.univ.sum (λ (j₁ : m), L i j₁ * M j₁ j₂ * N j₂ k)) :
      by congr; funext; rw finset.sum_mul
    ... = finset.univ.sum (λ (j₁ : m), finset.univ.sum (λ (j₂ : n), L i j₁ * M j₁ j₂ * N j₂ k)) :
      by rw finset.sum_comm
    ... = finset.univ.sum (λ (j₁ : m), L i j₁ * finset.univ.sum (λ (j₂ : n), M j₁ j₂ * N j₂ k)) :
      by congr; funext; rw finset.mul_sum; congr; funext; rw mul_assoc

instance : semigroup (matrix n n α) :=
{ mul_assoc := matrix.mul_assoc,
  ..matrix.has_mul }

end semigroup

section monoid
variables [decidable_eq n] [decidable_eq m] [semiring α]

protected theorem one_mul (M : matrix n m α) : (1 : matrix n n α).mul M = M :=
ext' $ λ i j,
have h : ∀ (j' : n), j' ∈ (finset.univ : finset n) → j' ∉ finset.singleton i → (1 : matrix n n α) i j' * M j' j = 0 :=
  λ j' h₁ h₂, by simp at h₂; simp [ne.symm h₂],
calc finset.univ.sum (λ i', (1 : matrix n n α) i i' * M i' j)
  = (finset.singleton i).sum (λ i', (1 : matrix n n α) i i' * M i' j) :
    (finset.sum_subset (finset.subset_univ (finset.singleton i)) h).symm
  ... = M i j :
    by simp

protected theorem mul_one (M : matrix n m α) : M.mul (1 : matrix m m α) = M :=
ext' $ λ i j,
have h : ∀ (j' : m), j' ∈ (finset.univ : finset m) → j' ∉ finset.singleton j → M i j' * (1 : matrix m m α) j' j = 0 :=
  λ j' h₁ h₂, by simp at h₂; simp [h₂],
calc finset.univ.sum (λ j',  M i j' * (1 : matrix m m α) j' j)
  = (finset.singleton j).sum (λ j', M i j' * (1 : matrix m m α) j' j) :
    (finset.sum_subset (finset.subset_univ (finset.singleton j)) h).symm
  ... = M i j :
    by simp

instance : monoid (matrix n n α) :=
{ one_mul := matrix.one_mul,
  mul_one := matrix.mul_one,
  ..matrix.has_one,
  ..matrix.semigroup }

end monoid

instance [add_group α] : add_group (matrix m n α) :=
{ add_left_neg := λ M, show - M + M = 0, from ext' $ by simp,
  ..matrix.add_monoid,
  ..matrix.has_neg }

instance [add_comm_group α] : add_comm_group (matrix m n α) :=
{ ..matrix.add_group,
  ..matrix.add_comm_monoid }

section distrib
variables [semiring α]

theorem left_distrib (L M N : matrix n n α) : L * (M + N) = (L * M) + (L * N) :=
ext' $ λ i j,
calc finset.univ.sum (λ j', L i j' * (M j' j + N j' j))
  = finset.univ.sum (λ j', (λ j', L i j' * M j' j) j' + (λ j', L i j' * N j' j) j') :
    by simp [left_distrib]
  ... = finset.univ.sum (λ j', L i j' * M j' j) + finset.univ.sum (λ j', L i j' * N j' j) :
    finset.sum_add_distrib

theorem right_distrib (L M N : matrix n n α) : (L + M) * N = (L * N) + (M * N) :=
ext' $ λ i j,
calc finset.univ.sum (λ i', (L i i' + M i i') * N i' j)
  = finset.univ.sum (λ i', (λ i', L i i' * N i' j) i' + (λ i', M i i' * N i' j) i') :
    by simp [right_distrib]
  ... = finset.univ.sum (λ i', L i i' * N i' j) + finset.univ.sum (λ i', M i i' * N i' j) :
    finset.sum_add_distrib

instance : distrib (matrix n n α) :=
{ left_distrib := left_distrib,
  right_distrib := right_distrib,
  ..matrix.has_mul,
  ..matrix.has_add }

end distrib

instance [decidable_eq n] [ring α] : ring (matrix n n α) :=
{ ..matrix.add_comm_group,
  ..matrix.monoid,
  ..matrix.distrib }

instance [has_mul α] : has_scalar α (matrix m n α) :=
⟨λ a M i j, a * M i j⟩

instance [ring α] : module α (matrix m n α) :=
{ smul_add := λ a M N, ext' $ λ i j, mul_add a (M i j) (N i j),
  add_smul := λ a b M, ext' $ λ i j, add_mul a b (M i j),
  mul_smul := λ a b M, ext' $ λ i j, mul_assoc a b (M i j),
  one_smul := λ M, ext' $ λ i j, one_mul (M i j) }

section free_module

structure free_module (α : Type v) [semiring α] : Type (v+1) :=
(carrier : Type v)
[fin : fintype carrier]
[deceq : decidable_eq carrier]

instance (α) [semiring α] : has_coe_to_sort (free_module α) := ⟨_, free_module.carrier⟩
instance {α} [semiring α] (n : free_module α) : fintype n := free_module.fin _
instance {α} [semiring α] (n : free_module α) : decidable_eq n := free_module.deceq _

variables [semiring α]

open category_theory

instance : large_category (free_module α) :=
{ hom  := λ m n, matrix m n α,
  id   := λ m, 1,
  comp := λ _ _ _, matrix.mul,
  comp_id' := λ _ _, matrix.mul_one,
  id_comp' := λ _ _, matrix.one_mul,
  assoc'   := λ _ _ _ _, matrix.mul_assoc }

end free_module

section diagonal
variables [decidable_eq n]

def diagonal [has_zero α] (d : n → α) : matrix n n α := λ i j, if i = j then d i else 0

@[simp] theorem diagonal_val_eq  [has_zero α] {d : n → α} {i : n} : (diagonal d) i i = d i :=
by simp [diagonal]

@[simp] theorem diagonal_val_ne  [has_zero α] {d : n → α} {i j : n} (h : i ≠ j) :
(diagonal d) i j = 0 := by simp [diagonal, h]

@[simp] theorem diagonal_zero [has_zero α] : (diagonal (λ _, 0) : matrix n n α) = 0 :=
by simp [diagonal]; refl

@[simp] theorem diagonal_one [has_zero α] [has_one α] : (diagonal (λ _, 1) : matrix n n α) = 1 :=
by simp [diagonal]; refl

@[simp] lemma ite_mul [semiring α] (P Q : Prop) [decidable P] [decidable Q] (a b : α) :
  (ite P a 0) * (ite Q b 0) = ite (P ∧ Q) (a * b) 0 :=
by split_ifs; simp * at *

@[simp] lemma eq_and_eq_symm {α : Type u} (a b : α) : (a = b ∧ b = a) ↔ a = b :=
by simp [eq_comm]

@[simp] theorem diagonal_mul [ring α] {d₁ d₂ : n → α} : 
  (diagonal d₁) * (diagonal d₂) = (diagonal (λ i, d₁ i * d₂ i)) :=
begin
  funext i j,
  dsimp [diagonal],
  split_ifs,
  { subst h,
    transitivity finset.sum (finset.singleton i) _,
    { symmetry,
      apply finset.sum_subset,
      { intros _ _, simp },
      intros j h1 h2,
      simp at h2,
      simp [h2] },
    simp },
  { convert finset.sum_const_zero,
    ext k,
    split_ifs; cc <|> simp }
end

@[simp] theorem diagonal_add [ring α] {d₁ d₂ : n → α} : 
  (diagonal d₁) + (diagonal d₂) = (diagonal (λ i, d₁ i + d₂ i)) :=
begin
  tidy,
  dsimp [diagonal],
  split_ifs,
  tidy, -- TODO tidy should try split_ifs!
end

end diagonal

section scalar
variables [decidable_eq n] [has_zero α]

def scalar (a : α) : matrix n n α := diagonal (λ _, a)

@[simp] theorem scalar_val_eq {a : α} {i : n} : (scalar a) i i = a :=
diagonal_val_eq

@[simp] theorem scalar_val_ne {a : α} {i j : n} (h : i ≠ j) : (scalar a) i j = 0 :=
diagonal_val_ne h

@[simp] theorem scalar_zero : (scalar 0 : matrix n n α) = 0 := diagonal_zero

@[simp] theorem scalar_one  [has_one α] : (scalar 1 : matrix n n α) = 1 := rfl

end scalar

end matrix
