/-
Copyright (c) 2022 Scott Morrison. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Morrison
-/
import ring_theory.simple_module.basic
import linear_algebra.finite_dimensional
import algebra.module.submodule.lattice

/-!
# 1-d modules are simple

We prove this for modules over a `k`-algebra, when `k` is a field,
and separately for modules over a division ring.

(Finding the common generalisation would be welcome.)
-/

open finite_dimensional

/-- Any `k`-algebra module with positive dimension over `k`
has a nontrivial submodule lattice, since `⊥ ≠ ⊤`. -/
lemma submodule_nontrivial_of_finrank_pos {k : Type*} [field k] {A : Type*} [ring A] [algebra k A]
  {M : Type*} [add_comm_group M] [module k M] [module A M] [is_scalar_tower k A M]
  (h : 0 < finrank k M) : nontrivial (submodule A M) :=
⟨⟨⊥, ⊤, begin
      apply_fun (λ m : submodule A M, finrank k (submodule.restrict_scalars k m)),
      dsimp,
      simp [h.ne],
    end⟩⟩

/-- Any module over a division ring with positive dimension over `k`
has a nontrivial submodule lattice, since `⊥ ≠ ⊤`. -/
lemma submodule_nontrivial_of_finrank_pos' {k : Type*} [division_ring k]
  {M : Type*} [add_comm_group M] [module k M]
  (h : 0 < finrank k M) : nontrivial (submodule k M) :=
⟨⟨⊥, ⊤, begin
      apply_fun (λ m : submodule k M, finrank k m),
      dsimp,
      simp [h.ne],
    end⟩⟩

example (a : ℕ) (h : a = 1) : 0 < a := nat.lt_of_sub_eq_succ h

/-- Any `k`-algebra module which is 1-dimensional over `k` is simple. -/
lemma is_simple_module_of_finrank_eq_one {k : Type*} [field k] {A : Type*} [ring A] [algebra k A]
  {M : Type*} [add_comm_group M] [module k M] [module A M] [is_scalar_tower k A M]
  (h : finrank k M = 1) : is_simple_module A M :=
begin
  haveI : finite_dimensional k M := finite_dimensional_of_finrank_eq_succ h,
  haveI : nontrivial (submodule A M) :=
    submodule_nontrivial_of_finrank_pos (nat.lt_of_sub_eq_succ h),
  split,
  intro m,
  have c := (submodule.finrank_le (submodule.restrict_scalars k m)).trans h.le,
  interval_cases finrank k (submodule.restrict_scalars k m) with d,
  { left, simpa using d, },
  { right,
    have d' : finrank k (submodule.restrict_scalars k m) = finrank k M := by simp [h, d],
    simpa using eq_top_of_finrank_eq d', },
end

/-- Any 1-dimensional module over a division ring is simple. -/
lemma is_simple_module_of_finrank_eq_one' {k : Type*} [division_ring k]
  {M : Type*} [add_comm_group M] [module k M] (h : finrank k M = 1) : is_simple_module k M :=
begin
  haveI : finite_dimensional k M := finite_dimensional_of_finrank_eq_succ h,
  haveI : nontrivial (submodule k M) :=
    submodule_nontrivial_of_finrank_pos' (nat.lt_of_sub_eq_succ h),
  split,
  intro m,
  have c := (submodule.finrank_le m).trans h.le,
  interval_cases finrank k m with d,
  { left, simpa using d, },
  { right,
    simpa using eq_top_of_finrank_eq (by simp [h, d] : finrank k m = finrank k M), },
end
