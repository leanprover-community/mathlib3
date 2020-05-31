/-
Copyright (c) 2020 Oliver Nash. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Nash
-/
import algebra.lie_algebra
import linear_algebra.matrix

/-!
# Classical Lie algebras

This file is the place to find definitions and basic properties of the classical Lie algebras:
  * Aₙ sl(n+1)
  * Bₙ so(2n+1)
  * Cₙ sp(2n)
  * Dₙ so(2n)

As of April 2020, the definition of Aₙ is in place while the others still need to be provided.

## Tags

classical lie algebra, special linear
-/

universes u₁ u₂

namespace lie_algebra
open_locale matrix

variables (n : Type u₁) (R : Type u₂)
variables [fintype n] [decidable_eq n] [comm_ring R]

local attribute [instance] matrix.lie_ring
local attribute [instance] matrix.lie_algebra

@[simp] lemma matrix_trace_commutator_zero (X Y : matrix n n R) : matrix.trace n R R ⁅X, Y⁆ = 0 :=
begin
  change matrix.trace n R R (X ⬝ Y - Y ⬝ X) = 0,
  simp only [matrix.trace_mul_comm, linear_map.map_sub, sub_self],
end

namespace special_linear

/-- The special linear Lie algebra: square matrices of trace zero. -/
def sl : lie_subalgebra R (matrix n n R) :=
{ lie_mem := λ X Y _ _, linear_map.mem_ker.2 $ matrix_trace_commutator_zero _ _ _ _,
  ..linear_map.ker (matrix.trace n R R) }

lemma sl_bracket (A B : sl n R) : ⁅A, B⁆.val = A.val ⬝ B.val - B.val ⬝ A.val := rfl

section elementary_basis

variables {n} (i j : n)

/-- It is useful to define these matrices for explicit calculations in sl n R. -/
abbreviation E : matrix n n R := λ i' j', if i = i' ∧ j = j' then 1 else 0

@[simp] lemma E_apply_one : E R i j i j = 1 := if_pos (and.intro rfl rfl)

@[simp] lemma E_apply_zero (i' j' : n) (h : ¬(i = i' ∧ j = j')) : E R i j i' j' = 0 := if_neg h

@[simp] lemma E_diag_zero (h : j ≠ i) : matrix.diag n R R (E R i j) = 0 :=
begin
  ext k, rw matrix.diag_apply,
  suffices : ¬(i = k ∧ j = k), by exact if_neg this,
  rintros ⟨e₁, e₂⟩, apply h, subst e₁, exact e₂,
end

lemma E_trace_zero (h : j ≠ i) : matrix.trace n R R (E R i j) = 0 := by simp [h]

/-- When j ≠ i, the elementary matrices are elements of sl n R, in fact they are part of a natural
basis of sl n R. -/
def Eb (h : j ≠ i) : sl n R :=
⟨E R i j, by { change E R i j ∈ linear_map.ker (matrix.trace n R R), simp [E_trace_zero R i j h], }⟩

@[simp] lemma Eb_val (h : j ≠ i) : (Eb R i j h).val = E R i j := rfl

end elementary_basis

lemma sl_non_abelian [nonzero R] (h : 1 < fintype.card n) : ¬lie_algebra.is_abelian ↥(sl n R) :=
begin
  rcases fintype.exists_pair_of_one_lt_card h with ⟨i, j, hij⟩,
  let A := Eb R i j hij,
  let B := Eb R j i hij.symm,
  intros c,
  have c' : A.val ⬝ B.val = B.val ⬝ A.val := by { rw [←sub_eq_zero, ←sl_bracket, c.abelian], refl, },
  have : (1 : R) = 0 := by simpa [matrix.mul_val, hij] using (congr_fun (congr_fun c' i) i),
  exact one_ne_zero this,
end

end special_linear

end lie_algebra
