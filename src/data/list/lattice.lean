/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro
-/
import data.list.basic

/-!
# Lattice structure of lists

This files prove basic properties about `list.union`, `list.inter` and `list.disjoint`, which are
defined in core Lean and `data.list.defs`.

`l₁ ∪ l₂` is the list where all elements of `l₁` have been inserted in `l₂` in order. For example,
`[0, 1, 2, 3] ∪ [7, 3, 0] = [1, 2, 7, 3, 0]`

`l₁ ∩ l₂` is the list of elements of `l₁` in order which are in `l₂`. For example,
`[0, 1, 2, 3] ∪ [7, 3, 0] = [0, 3]`
-/

open nat

namespace list
variables {α : Type*} {l l₁ l₂ : list α} {p : α → Prop} {a : α}

/-! ### disjoint -/

section disjoint

lemma disjoint.symm (d : disjoint l₁ l₂) : disjoint l₂ l₁ := λ a i₂ i₁, d i₁ i₂

lemma disjoint_comm : disjoint l₁ l₂ ↔ disjoint l₂ l₁ := ⟨disjoint.symm, disjoint.symm⟩

lemma disjoint_left : disjoint l₁ l₂ ↔ ∀ {a}, a ∈ l₁ → a ∉ l₂ := iff.rfl

lemma disjoint_right : disjoint l₁ l₂ ↔ ∀ {a}, a ∈ l₂ → a ∉ l₁ := disjoint_comm

lemma disjoint_iff_ne : disjoint l₁ l₂ ↔ ∀ a ∈ l₁, ∀ b ∈ l₂, a ≠ b :=
by simp only [disjoint_left, imp_not_comm, forall_eq']

lemma disjoint_of_subset_left (ss : l₁ ⊆ l) (d : disjoint l l₂) : disjoint l₁ l₂ := λ x m, d (ss m)

lemma disjoint_of_subset_right (ss : l₂ ⊆ l) (d : disjoint l₁ l) : disjoint l₁ l₂ :=
λ x m m₁, d m (ss m₁)

lemma disjoint_of_disjoint_cons_left {l₁ l₂} : disjoint (a :: l₁) l₂ → disjoint l₁ l₂ :=
disjoint_of_subset_left (list.subset_cons _ _)

lemma disjoint_of_disjoint_cons_right {l₁ l₂} : disjoint l₁ (a :: l₂) → disjoint l₁ l₂ :=
disjoint_of_subset_right (list.subset_cons _ _)

@[simp] lemma disjoint_nil_left (l : list α) : disjoint [] l := λ a, (not_mem_nil a).elim

@[simp] lemma disjoint_nil_right (l : list α) : disjoint l [] :=
by { rw disjoint_comm, exact disjoint_nil_left _ }

@[simp, priority 1100] lemma singleton_disjoint : disjoint [a] l ↔ a ∉ l :=
by { simp only [disjoint, mem_singleton, forall_eq], refl }

@[simp, priority 1100] lemma disjoint_singleton : disjoint l [a] ↔ a ∉ l :=
by rw [disjoint_comm, singleton_disjoint]

@[simp] lemma disjoint_append_left : disjoint (l₁ ++ l₂) l ↔ disjoint l₁ l ∧ disjoint l₂ l :=
by simp only [disjoint, mem_append, or_imp_distrib, forall_and_distrib]

@[simp] lemma disjoint_append_right : disjoint l (l₁ ++ l₂) ↔ disjoint l l₁ ∧ disjoint l l₂ :=
disjoint_comm.trans $ by simp only [disjoint_comm, disjoint_append_left]

@[simp] lemma disjoint_cons_left : disjoint (a :: l₁) l₂ ↔ a ∉ l₂ ∧ disjoint l₁ l₂ :=
(@disjoint_append_left _ l₂ [a] l₁).trans $ by simp only [singleton_disjoint]

@[simp] lemma disjoint_cons_right : disjoint l₁ (a :: l₂) ↔ a ∉ l₁ ∧ disjoint l₁ l₂ :=
disjoint_comm.trans $ by simp only [disjoint_comm, disjoint_cons_left]

lemma disjoint_of_disjoint_append_left_left (d : disjoint (l₁ ++ l₂) l) : disjoint l₁ l :=
(disjoint_append_left.1 d).1

lemma disjoint_of_disjoint_append_left_right (d : disjoint (l₁ ++ l₂) l) : disjoint l₂ l :=
(disjoint_append_left.1 d).2

lemma disjoint_of_disjoint_append_right_left (d : disjoint l (l₁ ++ l₂)) : disjoint l l₁ :=
(disjoint_append_right.1 d).1

lemma disjoint_of_disjoint_append_right_right (d : disjoint l (l₁ ++ l₂)) : disjoint l l₂ :=
(disjoint_append_right.1 d).2

lemma disjoint_take_drop {m n : ℕ} (hl : l.nodup) (h : m ≤ n) : disjoint (l.take m) (l.drop n) :=
begin
  induction l generalizing m n,
  case list.nil : m n
  { simp },
  case list.cons : x xs xs_ih m n
  { cases m; cases n; simp only [disjoint_cons_left, mem_cons_iff, disjoint_cons_right, drop,
                                 true_or, eq_self_iff_true, not_true, false_and,
                                 disjoint_nil_left, take],
    { cases h },
    cases hl with _ _ h₀ h₁, split,
    { intro h, exact h₀ _ (mem_of_mem_drop h) rfl, },
    solve_by_elim [le_of_succ_le_succ] { max_depth := 4 } },
end

end disjoint

variable [decidable_eq α]

/-! ### union -/

section union

@[simp] lemma nil_union (l : list α) : [] ∪ l = l := rfl

@[simp] lemma cons_union (l₁ l₂ : list α) (a : α) : a :: l₁ ∪ l₂ = insert a (l₁ ∪ l₂) := rfl

@[simp] lemma mem_union : a ∈ l₁ ∪ l₂ ↔ a ∈ l₁ ∨ a ∈ l₂ :=
by induction l₁; simp only [nil_union, not_mem_nil, false_or, cons_union, mem_insert_iff,
  mem_cons_iff, or_assoc, *]

lemma mem_union_left (h : a ∈ l₁) (l₂ : list α) : a ∈ l₁ ∪ l₂ := mem_union.2 (or.inl h)

lemma mem_union_right (l₁ : list α) (h : a ∈ l₂) : a ∈ l₁ ∪ l₂ := mem_union.2 (or.inr h)

lemma sublist_suffix_of_union : ∀ l₁ l₂ : list α, ∃ t, t <+ l₁ ∧ t ++ l₂ = l₁ ∪ l₂
| [] l₂ := ⟨[], by refl, rfl⟩
| (a :: l₁) l₂ := let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂ in
  if h : a ∈ l₁ ∪ l₂
  then ⟨t, sublist_cons_of_sublist _ s, by simp only [e, cons_union, insert_of_mem h]⟩
  else ⟨a::t, cons_sublist_cons _ s, by simp only [cons_append, cons_union, e, insert_of_not_mem h];
    split; refl⟩

lemma suffix_union_right (l₁ l₂ : list α) : l₂ <:+ l₁ ∪ l₂ :=
(sublist_suffix_of_union l₁ l₂).imp (λ a, and.right)

lemma union_sublist_append (l₁ l₂ : list α) : l₁ ∪ l₂ <+ l₁ ++ l₂ :=
let ⟨t, s, e⟩ := sublist_suffix_of_union l₁ l₂ in
e ▸ (append_sublist_append_right _).2 s

lemma forall_mem_union : (∀ x ∈ l₁ ∪ l₂, p x) ↔ (∀ x ∈ l₁, p x) ∧ (∀ x ∈ l₂, p x) :=
by simp only [mem_union, or_imp_distrib, forall_and_distrib]

lemma forall_mem_of_forall_mem_union_left (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₁, p x :=
(forall_mem_union.1 h).1

lemma forall_mem_of_forall_mem_union_right
   (h : ∀ x ∈ l₁ ∪ l₂, p x) : ∀ x ∈ l₂, p x :=
(forall_mem_union.1 h).2

end union

/-! ### inter -/

section inter

@[simp] lemma inter_nil (l : list α) : [] ∩ l = [] := rfl

@[simp] lemma inter_cons_of_mem (l₁ : list α) (h : a ∈ l₂) :
  (a :: l₁) ∩ l₂ = a :: (l₁ ∩ l₂) :=
if_pos h

@[simp] lemma inter_cons_of_not_mem (l₁ : list α) (h : a ∉ l₂) :
  (a :: l₁) ∩ l₂ = l₁ ∩ l₂ :=
if_neg h

lemma mem_of_mem_inter_left : a ∈ l₁ ∩ l₂ → a ∈ l₁ := mem_of_mem_filter

lemma mem_of_mem_inter_right : a ∈ l₁ ∩ l₂ → a ∈ l₂ := of_mem_filter

lemma mem_inter_of_mem_of_mem : a ∈ l₁ → a ∈ l₂ → a ∈ l₁ ∩ l₂ :=
mem_filter_of_mem

@[simp] lemma mem_inter : a ∈ l₁ ∩ l₂ ↔ a ∈ l₁ ∧ a ∈ l₂ := mem_filter

lemma inter_subset_left (l₁ l₂ : list α) : l₁ ∩ l₂ ⊆ l₁ := filter_subset _

lemma inter_subset_right (l₁ l₂ : list α) : l₁ ∩ l₂ ⊆ l₂ := λ a, mem_of_mem_inter_right

lemma subset_inter {l l₁ l₂ : list α} (h₁ : l ⊆ l₁) (h₂ : l ⊆ l₂) : l ⊆ l₁ ∩ l₂ :=
λ a h, mem_inter.2 ⟨h₁ h, h₂ h⟩

lemma inter_eq_nil_iff_disjoint : l₁ ∩ l₂ = [] ↔ disjoint l₁ l₂ :=
by { simp only [eq_nil_iff_forall_not_mem, mem_inter, not_and], refl }

lemma forall_mem_inter_of_forall_left (h : ∀ x ∈ l₁, p x)
  (l₂ : list α) :
  ∀ x, x ∈ l₁ ∩ l₂ → p x :=
ball.imp_left (λ x, mem_of_mem_inter_left) h

lemma forall_mem_inter_of_forall_right (l₁ : list α)
  (h : ∀ x ∈ l₂, p x) :
  ∀ x, x ∈ l₁ ∩ l₂ → p x :=
ball.imp_left (λ x, mem_of_mem_inter_right) h

@[simp] lemma inter_reverse {xs ys : list α} : xs.inter ys.reverse = xs.inter ys :=
by { simp only [list.inter, mem_reverse], congr }

end inter
end list
