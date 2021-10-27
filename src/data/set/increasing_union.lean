/-
Copyright (c) 2021 Antoine Chambert-Loir. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Antoine Chambert-Loir
-/

/-
# Increasing unions of sets indexed by integers

Given a sequence of sets s : ℕ → set α,
we construct its increasing Union by
λ n:ℕ, Union (set restrict s { j : ℕ | j ≤ n}) -/


import data.set.basic
import data.set.lattice

open set

variables {α : Type* }

namespace set

namespace increasing_Union
/-- Increasing union is increasing -/
lemma is_increasing (s : ℕ → set α) (m n : ℕ ) (h : m ≤ n) :
  Union (set.restrict s { j : ℕ | j ≤ m} ) ⊆ Union (set.restrict s { j : ℕ | j ≤ n} )
  :=
begin
  rw subset_def,
  intros x hxm,
  simp at hxm,
  obtain ⟨ j, hjm, hjx ⟩ := hxm,
  have hjn: j ≤ n , by exact le_trans hjm h,
  simp,
  apply exists.intro  j,
  split, exact hjn, exact hjx,
end

/-- Union of increasing_Union is Union -/
lemma Union_of (s : ℕ → set α) :
  Union (λ n:ℕ, Union (set.restrict s { j : ℕ | j ≤ n})) = Union s
  :=
begin
  rw ext_iff, intro x, split,

  intro hx, simp at hx,
  obtain ⟨ m, j, hjm, hjx ⟩ := hx,
  apply mem_Union.2, apply exists.intro j, assumption,

  intro hx, simp at hx,
  obtain ⟨ j, hjx ⟩ := hx,
  simp,
  apply exists.intro j, apply exists.intro j,
  split, exact rfl.ge, assumption,
end

/-- sets are ultimately members of their increasing union -/
lemma subset_of (s : ℕ → set α) (m n : ℕ) (hmn : m ≤ n ):
  s m ⊆ Union ( set.restrict s { j : ℕ | j ≤ n })
  :=
begin
  rw  subset_def, intros x hx,
  simp,
  apply exists.intro m, split, assumption, assumption,
end

/-- increasing Union can be defined by induction -/
lemma init (s : ℕ → set α) :
  Union ( set.restrict s { j : ℕ | j ≤ 0}) = s 0
  :=
begin
  rw ext_iff, intro x, split,
  intro hx, simp at hx, assumption,
  intro hx, simp, assumption,
end

/-- Inductive relation for increasing union -/
lemma ind (s : ℕ → set α) :
  ∀ n : ℕ, Union ( set.restrict s { j : ℕ | j ≤ n}) ∪ (s n.succ)
    = Union ( set.restrict s { j : ℕ | j ≤ n.succ} )
  :=
begin
  intro n, rw subset.antisymm_iff,
  split,
  apply union_subset,
  apply is_increasing s n n.succ (nat.le_succ n),

  apply subset_of , exact rfl.ge,

  rw subset_def, intros x hx,
  simp at hx,
  obtain ⟨ m, hm ⟩ := hx,
  simp,

  cases le_or_lt m n with H1 H2,
  apply or.inl,
  apply exists.intro m, split, assumption, exact hm.right,
  apply or.inr,

  suffices : n.succ = m ,
  rw this, exact hm.right,
  /- It remains to prove that n.succ = m -/
    apply nat.eq_of_le_of_lt_succ,
    exact hm.left,
    apply nat.lt_succ_iff.2,
    apply nat.lt_iff_add_one_le.1, assumption,
end

end increasing_Union

end set
