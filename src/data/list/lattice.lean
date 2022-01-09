/-
Copyright (c) 2014 Parikshit Khanna. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Parikshit Khanna, Jeremy Avigad, Leonardo de Moura, Floris van Doorn, Mario Carneiro,
Scott Morrison
-/
import data.list.count
import data.list.infix

/-!
# Lattice structure of lists

This files prove basic properties about `list.disjoint`, `list.union`, `list.inter` and
`list.bag_inter`, which are defined in core Lean and `data.list.defs`.

`l₁ ∪ l₂` is the list where all elements of `l₁` have been inserted in `l₂` in order. For example,
`[0, 0, 1, 2, 2, 3] ∪ [4, 3, 3, 0] = [1, 2, 4, 3, 3, 0]`

`l₁ ∩ l₂` is the list of elements of `l₁` in order which are in `l₂`. For example,
`[0, 0, 1, 2, 2, 3] ∪ [4, 3, 3, 0] = [0, 0, 3]`

`bag_inter l₁ l₂` is the list of elements that are in both `l₁` and `l₂`, counted with multiplicity
and in the order they appear in `l₁`. As opposed to `list.inter`, `list.bag_inter` copes well with
multiplicity. For example,
`bag_inter [0, 1, 2, 3, 2, 1, 0] [1, 0, 1, 4, 3] = [0, 1, 3, 1]`
-/

open nat

namespace list
variables {α : Type*} {l l₁ l₂ : list α} {p : α → Prop} {a : α}

/-! ### `disjoint` -/

section disjoint

lemma disjoint.symm (d : disjoint l₁ l₂) : disjoint l₂ l₁ := λ a i₂ i₁, d i₁ i₂

lemma disjoint_comm : disjoint l₁ l₂ ↔ disjoint l₂ l₁ := ⟨disjoint.symm, disjoint.symm⟩

lemma disjoint_left : disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₁ → a ∉ l₂ := iff.rfl

lemma disjoint_right : disjoint l₁ l₂ ↔ ∀ ⦃a⦄, a ∈ l₂ → a ∉ l₁ := disjoint_comm

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

/-! ### `union` -/

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
  else ⟨a::t, s.cons_cons _, by simp only [cons_append, cons_union, e, insert_of_not_mem h];
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

/-! ### `inter` -/

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

/-! ### `bag_inter` -/

section bag_inter

@[simp] lemma nil_bag_inter (l : list α) : [].bag_inter l = [] :=
by cases l; refl

@[simp] lemma bag_inter_nil (l : list α) : l.bag_inter [] = [] :=
by cases l; refl

@[simp] lemma cons_bag_inter_of_pos (l₁ : list α) (h : a ∈ l₂) :
  (a :: l₁).bag_inter l₂ = a :: l₁.bag_inter (l₂.erase a) :=
by cases l₂; exact if_pos h

@[simp] lemma cons_bag_inter_of_neg (l₁ : list α) (h : a ∉ l₂) :
  (a :: l₁).bag_inter l₂ = l₁.bag_inter l₂ :=
begin
  cases l₂, {simp only [bag_inter_nil]},
  simp only [erase_of_not_mem h, list.bag_inter, if_neg h]
end

@[simp] lemma mem_bag_inter {a : α} : ∀ {l₁ l₂ : list α}, a ∈ l₁.bag_inter l₂ ↔ a ∈ l₁ ∧ a ∈ l₂
| []        l₂ := by simp only [nil_bag_inter, not_mem_nil, false_and]
| (b :: l₁) l₂ := begin
    by_cases b ∈ l₂,
    { rw [cons_bag_inter_of_pos _ h, mem_cons_iff, mem_cons_iff, mem_bag_inter],
      by_cases ba : a = b,
      { simp only [ba, h, eq_self_iff_true, true_or, true_and] },
      { simp only [mem_erase_of_ne ba, ba, false_or] } },
    { rw [cons_bag_inter_of_neg _ h, mem_bag_inter, mem_cons_iff, or_and_distrib_right],
      symmetry, apply or_iff_right_of_imp,
      rintro ⟨rfl, h'⟩, exact h.elim h' }
  end

@[simp] lemma count_bag_inter {a : α} :
  ∀ {l₁ l₂ : list α}, count a (l₁.bag_inter l₂) = min (count a l₁) (count a l₂)
| []         l₂         := by simp
| l₁         []         := by simp
| (h₁ :: l₁) (h₂ :: l₂) :=
begin
  simp only [list.bag_inter, list.mem_cons_iff],
  by_cases p₁ : h₂ = h₁; by_cases p₂ : h₁ = a,
  { simp only [p₁, p₂, count_bag_inter, min_succ_succ, erase_cons_head, if_true, mem_cons_iff,
               count_cons_self, true_or, eq_self_iff_true] },
  { simp only [p₁, ne.symm p₂, count_bag_inter, count_cons, erase_cons_head, if_true, mem_cons_iff,
               true_or, eq_self_iff_true, if_false] },
  { rw p₂ at p₁,
    by_cases p₃ : a ∈ l₂,
    { simp only [p₁, ne.symm p₁, p₂, p₃, erase_cons, count_bag_inter, eq.symm (min_succ_succ _ _),
                 succ_pred_eq_of_pos (count_pos.2 p₃), if_true, mem_cons_iff, false_or,
                 count_cons_self, eq_self_iff_true, if_false, ne.def, not_false_iff,
                 count_erase_self, list.count_cons_of_ne] },
    { simp [ne.symm p₁, p₂, p₃] } },
  { by_cases p₄ : h₁ ∈ l₂; simp only [ne.symm p₁, ne.symm p₂, p₄, count_bag_inter, if_true,
      if_false, mem_cons_iff, false_or, eq_self_iff_true, ne.def, not_false_iff,count_erase_of_ne,
      count_cons_of_ne] }
end

lemma bag_inter_sublist_left : ∀ l₁ l₂ : list α, l₁.bag_inter l₂ <+ l₁
| []        l₂ := by simp [nil_sublist]
| (b :: l₁) l₂ := begin
  by_cases b ∈ l₂; simp [h],
  { exact (bag_inter_sublist_left _ _).cons_cons _ },
  { apply sublist_cons_of_sublist, apply bag_inter_sublist_left }
end

lemma bag_inter_nil_iff_inter_nil : ∀ l₁ l₂ : list α, l₁.bag_inter l₂ = [] ↔ l₁ ∩ l₂ = []
| []        l₂ := by simp
| (b :: l₁) l₂ :=
begin
  by_cases h : b ∈ l₂; simp [h],
  exact bag_inter_nil_iff_inter_nil l₁ l₂
end

end bag_inter
end list
