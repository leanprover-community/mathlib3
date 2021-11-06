/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import order.basic

/-!
# Comparison

This file provides basic results about orderings and comparison in linear orders.


## Definitions

* `cmp_le`: An `ordering` from `≤`.
* `ordering.compares`: Turns an `ordering` into `<` and `=` propositions.
* `linear_order_of_compares`: Constructs a `linear_order` instance from the fact that any two
  elements that are not one strictly less than the other either way are equal.
-/

variables {α : Type*}

/-- Like `cmp`, but uses a `≤` on the type instead of `<`. Given two elements `x` and `y`, returns a
three-way comparison result `ordering`. -/
def cmp_le {α} [has_le α] [@decidable_rel α (≤)] (x y : α) : ordering :=
if x ≤ y then
  if y ≤ x then ordering.eq else ordering.lt
else ordering.gt

lemma cmp_le_swap {α} [has_le α] [is_total α (≤)] [@decidable_rel α (≤)] (x y : α) :
  (cmp_le x y).swap = cmp_le y x :=
begin
  by_cases xy : x ≤ y; by_cases yx : y ≤ x; simp [cmp_le, *, ordering.swap],
  cases not_or xy yx (total_of _ _ _)
end

lemma cmp_le_eq_cmp {α} [preorder α] [is_total α (≤)]
  [@decidable_rel α (≤)] [@decidable_rel α (<)] (x y : α) : cmp_le x y = cmp x y :=
begin
  by_cases xy : x ≤ y; by_cases yx : y ≤ x;
    simp [cmp_le, lt_iff_le_not_le, *, cmp, cmp_using],
  cases not_or xy yx (total_of _ _ _)
end

namespace ordering

/-- `compares o a b` means that `a` and `b` have the ordering relation `o` between them, assuming
that the relation `a < b` is defined. -/
@[simp] def compares [has_lt α] : ordering → α → α → Prop
| lt a b := a < b
| eq a b := a = b
| gt a b := a > b

lemma compares_swap [has_lt α] {a b : α} {o : ordering} :
  o.swap.compares a b ↔ o.compares b a :=
by { cases o, exacts [iff.rfl, eq_comm, iff.rfl] }

alias compares_swap ↔ ordering.compares.of_swap ordering.compares.swap

lemma swap_eq_iff_eq_swap {o o' : ordering} : o.swap = o' ↔ o = o'.swap :=
⟨λ h, by rw [← swap_swap o, h], λ h, by rw [← swap_swap o', h]⟩

lemma compares.eq_lt [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = lt ↔ a < b)
| lt a b h := ⟨λ _, h, λ _, rfl⟩
| eq a b h := ⟨λ h, by injection h, λ h', (ne_of_lt h' h).elim⟩
| gt a b h := ⟨λ h, by injection h, λ h', (lt_asymm h h').elim⟩

lemma compares.ne_lt [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o ≠ lt ↔ b ≤ a)
| lt a b h := ⟨absurd rfl, λ h', (not_le_of_lt h h').elim⟩
| eq a b h := ⟨λ _, ge_of_eq h, λ _ h, by injection h⟩
| gt a b h := ⟨λ _, le_of_lt h, λ _ h, by injection h⟩

lemma compares.eq_eq [preorder α] :
  ∀ {o} {a b : α}, compares o a b → (o = eq ↔ a = b)
| lt a b h := ⟨λ h, by injection h, λ h', (ne_of_lt h h').elim⟩
| eq a b h := ⟨λ _, h, λ _, rfl⟩
| gt a b h := ⟨λ h, by injection h, λ h', (ne_of_gt h h').elim⟩

lemma compares.eq_gt [preorder α] {o} {a b : α} (h : compares o a b) : (o = gt ↔ b < a) :=
swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt

lemma compares.ne_gt [preorder α] {o} {a b : α} (h : compares o a b) : (o ≠ gt ↔ a ≤ b) :=
(not_congr swap_eq_iff_eq_swap.symm).trans h.swap.ne_lt

lemma compares.le_total [preorder α] {a b : α} :
  ∀ {o}, compares o a b → a ≤ b ∨ b ≤ a
| lt h := or.inl (le_of_lt h)
| eq h := or.inl (le_of_eq h)
| gt h := or.inr (le_of_lt h)

lemma compares.le_antisymm [preorder α] {a b : α} :
  ∀ {o}, compares o a b → a ≤ b → b ≤ a → a = b
| lt h _ hba := (not_le_of_lt h hba).elim
| eq h _ _   := h
| gt h hab _ := (not_le_of_lt h hab).elim

lemma compares.inj [preorder α] {o₁} :
  ∀ {o₂} {a b : α}, compares o₁ a b → compares o₂ a b → o₁ = o₂
| lt a b h₁ h₂ := h₁.eq_lt.2 h₂
| eq a b h₁ h₂ := h₁.eq_eq.2 h₂
| gt a b h₁ h₂ := h₁.eq_gt.2 h₂

lemma compares_iff_of_compares_impl {β : Type*} [linear_order α] [preorder β] {a b : α}
  {a' b' : β} (h : ∀ {o}, compares o a b → compares o a' b') (o) :
  compares o a b ↔ compares o a' b' :=
begin
  refine ⟨h, λ ho, _⟩,
  cases lt_trichotomy a b with hab hab,
  { change compares ordering.lt a b at hab,
    rwa [ho.inj (h hab)] },
  { cases hab with hab hab,
    { change compares ordering.eq a b at hab,
      rwa [ho.inj (h hab)] },
    { change compares ordering.gt a b at hab,
      rwa [ho.inj (h hab)] } }
end

lemma swap_or_else (o₁ o₂) : (or_else o₁ o₂).swap = or_else o₁.swap o₂.swap :=
by cases o₁; try {refl}; cases o₂; refl

lemma or_else_eq_lt (o₁ o₂) : or_else o₁ o₂ = lt ↔ o₁ = lt ∨ (o₁ = eq ∧ o₂ = lt) :=
by cases o₁; cases o₂; exact dec_trivial

end ordering

lemma order_dual.dual_compares [has_lt α] {a b : α} {o : ordering} :
  @ordering.compares (order_dual α) _ o a b ↔ @ordering.compares α _ o b a :=
by { cases o, exacts [iff.rfl, eq_comm, iff.rfl] }

lemma cmp_compares [linear_order α] (a b : α) : (cmp a b).compares a b :=
begin
  unfold cmp cmp_using,
  by_cases a < b; simp [h],
  by_cases h₂ : b < a; simp [h₂, gt],
  exact (decidable.lt_or_eq_of_le (le_of_not_gt h₂)).resolve_left h
end

lemma cmp_swap [preorder α] [@decidable_rel α (<)] (a b : α) : (cmp a b).swap = cmp b a :=
begin
  unfold cmp cmp_using,
  by_cases a < b; by_cases h₂ : b < a; simp [h, h₂, gt, ordering.swap],
  exact lt_asymm h h₂
end

lemma order_dual.cmp_le_flip {α} [has_le α] [@decidable_rel α (≤)] (x y : α) :
  @cmp_le (order_dual α) _ _ x y = cmp_le y x := rfl

/-- Generate a linear order structure from a preorder and `cmp` function. -/
def linear_order_of_compares [preorder α] (cmp : α → α → ordering)
  (h : ∀ a b, (cmp a b).compares a b) :
  linear_order α :=
{ le_antisymm := λ a b, (h a b).le_antisymm,
  le_total := λ a b, (h a b).le_total,
  decidable_le := λ a b, decidable_of_iff _ (h a b).ne_gt,
  decidable_lt := λ a b, decidable_of_iff _ (h a b).eq_lt,
  decidable_eq := λ a b, decidable_of_iff _ (h a b).eq_eq,
  .. ‹preorder α› }

variables [linear_order α] (x y : α)

@[simp] lemma cmp_eq_lt_iff : cmp x y = ordering.lt ↔ x < y :=
ordering.compares.eq_lt (cmp_compares x y)

@[simp] lemma cmp_eq_eq_iff : cmp x y = ordering.eq ↔ x = y :=
ordering.compares.eq_eq (cmp_compares x y)

@[simp] lemma cmp_eq_gt_iff : cmp x y = ordering.gt ↔ y < x :=
ordering.compares.eq_gt (cmp_compares x y)

@[simp] lemma cmp_self_eq_eq : cmp x x = ordering.eq :=
by rw cmp_eq_eq_iff

variables {x y} {β : Type*} [linear_order β] {x' y' : β}

lemma cmp_eq_cmp_symm : cmp x y = cmp x' y' ↔ cmp y x = cmp y' x' :=
by { split, rw [←cmp_swap _ y, ←cmp_swap _ y'], cc,
  rw [←cmp_swap _ x, ←cmp_swap _ x'], cc, }

lemma lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x < y ↔ x' < y' :=
by rw [←cmp_eq_lt_iff, ←cmp_eq_lt_iff, h]

lemma le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x ≤ y ↔ x' ≤ y' :=
by { rw [←not_lt, ←not_lt], apply not_congr,
  apply lt_iff_lt_of_cmp_eq_cmp, rwa cmp_eq_cmp_symm }
