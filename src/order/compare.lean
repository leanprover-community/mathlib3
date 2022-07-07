/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Violeta Hernández Palacios
-/

import order.basic_rels
import order.synonym

/-!
# Comparison

This file provides basic results about orderings and comparison in linear orders and preorders.


## Definitions

### Linear orders

* `cmp_le`: An `ordering` from `≤`.
* `ordering.compares`: Turns an `ordering` into `<` and `=` propositions.
* `linear_order_of_compares`: Constructs a `linear_order` instance from the fact that any two
  elements that are not one strictly less than the other either way are equal.

### Preorders

* `preordering`: One of the four outcome classes for comparison on a preorder: less than,
  equivalent, greater than, incomparable.
* `precmp`: Compares two values in a `preorder`.
* `preordering.precompares`: Turns an `preordering` into its corresponding proposition.

### Conversion

* `ordering.to_preordering`: Converts the outcome classes for linear orders to the corresponding
  outcome classes on linear orders.
-/

variables {α : Type*}

open order_dual

section linear_order

/-! ### Linear orders -/

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

alias compares_swap ↔ compares.of_swap compares.swap

@[simp] theorem swap_inj (o₁ o₂ : ordering) : o₁.swap = o₂.swap ↔ o₁ = o₂ :=
by cases o₁; cases o₂; dec_trivial

lemma swap_eq_iff_eq_swap {o o' : ordering} : o.swap = o' ↔ o = o'.swap :=
by rw [←swap_inj, swap_swap]

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

lemma compares.le_total [preorder α] {a b : α} : ∀ {o}, compares o a b → a ≤ b ∨ b ≤ a
| lt h := or.inl (le_of_lt h)
| eq h := or.inl (le_of_eq h)
| gt h := or.inr (le_of_lt h)

lemma compares.le_antisymm [preorder α] {a b : α} : ∀ {o}, compares o a b → a ≤ b → b ≤ a → a = b
| lt h _ hba := (not_le_of_lt h hba).elim
| eq h _ _   := h
| gt h hab _ := (not_le_of_lt h hab).elim

lemma compares.inj [preorder α] {o₁} : ∀ {o₂} {a b : α}, compares o₁ a b → compares o₂ a b → o₁ = o₂
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

open ordering

@[simp] lemma to_dual_compares_to_dual [has_lt α] {a b : α} {o : ordering} :
  compares o (to_dual a) (to_dual b) ↔ compares o b a :=
by { cases o, exacts [iff.rfl, eq_comm, iff.rfl] }

@[simp] lemma of_dual_compares_of_dual [has_lt α] {a b : αᵒᵈ} {o : ordering} :
  compares o (of_dual a) (of_dual b) ↔ compares o b a :=
by { cases o, exacts [iff.rfl, eq_comm, iff.rfl] }

lemma cmp_compares [linear_order α] (a b : α) : (cmp a b).compares a b :=
by obtain h | h | h := lt_trichotomy a b; simp [cmp, cmp_using, h, h.not_lt]

lemma ordering.compares.cmp_eq [linear_order α] {a b : α} {o : ordering} (h : o.compares a b) :
  cmp a b = o :=
(cmp_compares a b).inj h

@[simp] lemma cmp_swap [preorder α] [@decidable_rel α (<)] (a b : α) : (cmp a b).swap = cmp b a :=
begin
  unfold cmp cmp_using,
  by_cases a < b; by_cases h₂ : b < a; simp [h, h₂, ordering.swap],
  exact lt_asymm h h₂
end

@[simp] lemma cmp_le_to_dual [has_le α] [@decidable_rel α (≤)] (x y : α) :
  cmp_le (to_dual x) (to_dual y) = cmp_le y x := rfl

@[simp] lemma cmp_le_of_dual [has_le α] [@decidable_rel α (≤)] (x y : αᵒᵈ) :
  cmp_le (of_dual x) (of_dual y) = cmp_le y x := rfl

@[simp] lemma cmp_to_dual [has_lt α] [@decidable_rel α (<)] (x y : α) :
  cmp (to_dual x) (to_dual y) = cmp y x := rfl

@[simp] lemma cmp_of_dual [has_lt α] [@decidable_rel α (<)] (x y : αᵒᵈ) :
  cmp (of_dual x) (of_dual y) = cmp y x := rfl

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
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rwa [←cmp_swap _ y, ←cmp_swap _ y', swap_inj] },
  { rwa [←cmp_swap _ x, ←cmp_swap _ x', swap_inj] }
end

lemma lt_iff_lt_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x < y ↔ x' < y' :=
by rw [←cmp_eq_lt_iff, ←cmp_eq_lt_iff, h]

lemma le_iff_le_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x ≤ y ↔ x' ≤ y' :=
by { rw [←not_lt, ←not_lt], apply not_congr,
  apply lt_iff_lt_of_cmp_eq_cmp, rwa cmp_eq_cmp_symm }

lemma eq_iff_eq_of_cmp_eq_cmp (h : cmp x y = cmp x' y') : x = y ↔ x' = y' :=
by rw [le_antisymm_iff, le_antisymm_iff, le_iff_le_of_cmp_eq_cmp h,
  le_iff_le_of_cmp_eq_cmp (cmp_eq_cmp_symm.1 h)]

lemma has_lt.lt.cmp_eq_lt (h : x < y) : cmp x y = ordering.lt := (cmp_eq_lt_iff _ _).2 h
lemma has_lt.lt.cmp_eq_gt (h : x < y) : cmp y x = ordering.gt := (cmp_eq_gt_iff _ _).2 h
lemma eq.cmp_eq_eq (h : x = y) : cmp x y = ordering.eq := (cmp_eq_eq_iff _ _).2 h
lemma eq.cmp_eq_eq' (h : x = y) : cmp y x = ordering.eq := h.symm.cmp_eq_eq

end linear_order

/-! ### Preorders -/

section preorder

/-- The type representing the possible outcomes for the comparison of two elements in a preorder. -/
inductive preordering
| lt | equiv | gt | incomp

namespace preordering

instance : inhabited preordering := ⟨equiv⟩

instance : has_repr preordering :=
⟨(λ s, match s with
  | lt     := "lt"
  | equiv  := "equiv"
  | gt     := "gt"
  | incomp := "incomp"
end)⟩

instance : decidable_eq preordering :=
λ a b, begin
  cases a; cases b;
  try { exact is_true rfl };
  try { exact is_false (λ h, preordering.no_confusion h) }
end

/-- If `a` and `b` compare as `o`, then `b` and `a` compare as `o.swap`. -/
def swap : preordering → preordering
| lt     := gt
| equiv  := equiv
| gt     := lt
| incomp := incomp

@[simp] lemma swap_swap (o : preordering) : o.swap.swap = o := by cases o; refl

@[simp] lemma swap_lt : lt.swap = gt := rfl
@[simp] lemma swap_equiv : preordering.equiv.swap = equiv := rfl
@[simp] lemma swap_gt : gt.swap = lt := rfl
@[simp] lemma swap_incomp : incomp.swap = incomp := rfl

@[simp] lemma swap_inj (o₁ o₂ : preordering) : o₁.swap = o₂.swap ↔ o₁ = o₂ :=
by cases o₁; cases o₂; dec_trivial

end preordering

open preordering

/-- Compares two values in a preorder using a specified `≤` relation. -/
def precmp_using {α : Type*} (le : α → α → Prop) [decidable_rel le] (a b : α) : preordering :=
if le a b then
  if le b a then equiv else lt
else
  if le b a then gt else incomp

/-- Compares two values in a preorder. -/
def precmp {α : Type*} [has_le α] [decidable_rel ((≤) : α → α → Prop)] (a b : α) : preordering :=
precmp_using (≤) a b

variable [preorder α]

namespace preordering

/-- `precompares o a b` means that `a` and `b` have the ordering relation `o` between them. -/
@[simp] def precompares : preordering → α → α → Prop
| lt     a b := a < b
| equiv  a b := antisymm_rel (≤) a b
| gt     a b := a > b
| incomp a b := incomp_rel (≤) a b

lemma precompares_swap {a b : α} : ∀ {o : preordering}, o.swap.precompares a b ↔ o.precompares b a
| lt     := iff.rfl
| equiv  := and.comm
| gt     := iff.rfl
| incomp := and.comm

alias precompares_swap ↔ precompares.of_swap precompares.swap

lemma swap_eq_iff_eq_swap {o o' : preordering} : o.swap = o' ↔ o = o'.swap :=
by rw [←swap_inj, swap_swap]

lemma precompares.eq_lt : ∀ {o} {a b : α}, precompares o a b → (o = lt ↔ a < b)
| lt     a b h := ⟨λ _, h, λ _, rfl⟩
| equiv  a b h := ⟨λ h, by injection h, λ h', (h'.not_le h.2).elim⟩
| gt     a b h := ⟨λ h, by injection h, λ h', (lt_asymm h h').elim⟩
| incomp a b h := ⟨λ h, by injection h, λ h', (h.1 h'.le).elim⟩

lemma precompares.eq_equiv : ∀ {o} {a b : α}, precompares o a b → (o = equiv ↔ antisymm_rel (≤) a b)
| lt     a b h := ⟨λ h, by injection h, λ h', (h'.2.not_lt h).elim⟩
| equiv  a b h := ⟨λ _, h, λ _, rfl⟩
| gt     a b h := ⟨λ h, by injection h, λ h', (h'.1.not_lt h).elim⟩
| incomp a b h := ⟨λ h, by injection h, λ h', (h.1 h'.1).elim⟩

lemma precompares.eq_gt {o} {a b : α} (h : precompares o a b) : (o = gt ↔ b < a) :=
swap_eq_iff_eq_swap.symm.trans h.swap.eq_lt

lemma precompares.eq_incomp : ∀ {o} {a b : α}, precompares o a b → (o = incomp ↔ incomp_rel (≤) a b)
| lt     a b h := ⟨λ h, by injection h, λ h', (h'.1 $ le_of_lt h).elim⟩
| equiv  a b h := ⟨λ h, by injection h, λ h', (h'.1 $ h.1).elim⟩
| gt     a b h := ⟨λ h, by injection h, λ h', (h'.2 $ le_of_lt h).elim⟩
| incomp a b h := ⟨λ _, h, λ _, rfl⟩

lemma precompares.inj {o₁} : ∀ {o₂} {a b : α}, precompares o₁ a b → precompares o₂ a b → o₁ = o₂
| lt     a b h₁ h₂ := h₁.eq_lt.2 h₂
| equiv  a b h₁ h₂ := h₁.eq_equiv.2 h₂
| gt     a b h₁ h₂ := h₁.eq_gt.2 h₂
| incomp a b h₁ h₂ := h₁.eq_incomp.2 h₂

end preordering

open preordering

@[simp] lemma to_dual_precompares_to_dual {a b : α} {o : preordering} :
  precompares o (to_dual a) (to_dual b) ↔ precompares o b a :=
by cases o; exact iff.rfl

@[simp] lemma of_dual_precompares_of_dual {a b : αᵒᵈ} {o : preordering} :
  precompares o (of_dual a) (of_dual b) ↔ precompares o b a :=
by cases o; exact iff.rfl

variable [@decidable_rel α (≤)]

lemma precmp_precompares (a b : α) : (precmp a b).precompares a b :=
begin
  unfold precmp precmp_using,
  split_ifs with h₁ h₂ h₂,
  exacts [⟨h₁, h₂⟩, lt_of_le_not_le h₁ h₂, lt_of_le_not_le h₂ h₁, ⟨h₁, h₂⟩]
end

lemma precompares.precmp_eq {a b : α} {o : preordering} (h : o.precompares a b) : precmp a b = o :=
(precmp_precompares a b).inj h

@[simp] lemma precmp_swap (a b : α) : (precmp a b).swap = precmp b a :=
by { unfold precmp precmp_using, split_ifs; refl }

variables {x y : α}

@[simp] lemma precmp_eq_lt_iff : precmp x y = lt ↔ x < y :=
precompares.eq_lt (precmp_precompares x y)

@[simp] lemma precmp_eq_equiv_iff : precmp x y = equiv ↔ antisymm_rel (≤) x y :=
precompares.eq_equiv (precmp_precompares x y)

@[simp] lemma precmp_eq_gt_iff : precmp x y = gt ↔ y < x :=
precompares.eq_gt (precmp_precompares x y)

@[simp] lemma precmp_eq_incomp_iff : precmp x y = incomp ↔ incomp_rel (≤) x y :=
precompares.eq_incomp (precmp_precompares x y)

@[simp] lemma precmp_self_eq_equiv : precmp x x = equiv :=
by rw precmp_eq_equiv_iff

lemma precmp_eq_lt_or_equiv_iff : precmp x y = lt ∨ precmp x y = equiv ↔ x ≤ y :=
by rw [le_iff_lt_or_antisymm_rel, precmp_eq_lt_iff, precmp_eq_equiv_iff]

lemma precmp_eq_gt_or_equiv_iff : precmp x y = gt ∨ precmp x y = equiv ↔ y ≤ x :=
by rw [le_iff_lt_or_antisymm_rel, precmp_eq_gt_iff, precmp_eq_equiv_iff, antisymm_rel.comm]

variables {β : Type*} [preorder β] [@decidable_rel β (≤)] {x' y' : β}

lemma precmp_eq_precmp_symm : precmp x y = precmp x' y' ↔ precmp y x = precmp y' x' :=
begin
  refine ⟨λ h, _, λ h, _⟩,
  { rwa [←precmp_swap _ y, ←precmp_swap _ y', swap_inj] },
  { rwa [←precmp_swap _ x, ←precmp_swap _ x', swap_inj] }
end

lemma lt_iff_lt_of_precmp_eq_precmp (h : precmp x y = precmp x' y') : x < y ↔ x' < y' :=
by rw [←precmp_eq_lt_iff, ←precmp_eq_lt_iff, h]

lemma le_iff_le_of_precmp_eq_precmp (h : precmp x y = precmp x' y') : x ≤ y ↔ x' ≤ y' :=
by rw [←precmp_eq_lt_or_equiv_iff, ←precmp_eq_lt_or_equiv_iff, h]

lemma equiv_iff_equiv_of_precmp_eq_precmp (h : precmp x y = precmp x' y') :
  antisymm_rel (≤) x y ↔ antisymm_rel (≤) x' y' :=
by rw [←precmp_eq_equiv_iff, ←precmp_eq_equiv_iff, h]

lemma incomp_iff_incomp_of_precmp_eq_precmp (h : precmp x y = precmp x' y') :
  incomp_rel (≤) x y ↔ incomp_rel (≤) x' y' :=
by rw [←precmp_eq_incomp_iff, ←precmp_eq_incomp_iff, h]

lemma _root_.has_lt.lt.precmp_eq_lt (h : x < y) : precmp x y = lt := precmp_eq_lt_iff.2 h
lemma _root_.has_lt.lt.precmp_eq_gt (h : x < y) : precmp y x = gt := precmp_eq_gt_iff.2 h
lemma _root_.antisymm_rel.precmp_eq_equiv (h : antisymm_rel (≤) x y) : precmp x y = equiv :=
precmp_eq_equiv_iff.2 h
lemma _root_.antisymm_rel.precmp_eq_equiv' (h : antisymm_rel (≤) x y) : precmp y x = equiv :=
h.symm.precmp_eq_equiv
lemma _root_.eq.precmp_eq_equiv (h : x = y) : precmp x y = equiv :=
(h.antisymm_rel _).precmp_eq_equiv
lemma _root_.eq.precmp_eq_equiv' (h : x = y) : precmp y x = equiv :=
h.symm.precmp_eq_equiv
lemma _root_.incomp_rel.precmp_eq_incomp (h : incomp_rel (≤) x y) : precmp x y = incomp :=
precmp_eq_incomp_iff.2 h
lemma _root_.incomp_rel.precmp_eq_incomp' (h : incomp_rel (≤) x y) : precmp y x = incomp :=
h.symm.precmp_eq_incomp

end preorder

/-! ### Conversion -/

namespace ordering

/-- Converts a comparison outcome in linear orders to one in preorders. -/
def to_preordering : ordering → preordering
| lt := preordering.lt
| eq := preordering.equiv
| gt := preordering.gt

@[simp] lemma lt_to_preordering : lt.to_preordering = preordering.lt := rfl
@[simp] lemma eq_to_preordering : eq.to_preordering = preordering.equiv := rfl
@[simp] lemma gt_to_preordering : gt.to_preordering = preordering.gt := rfl

@[simp] lemma cmp_to_precmp [linear_order α] (a b : α) : (cmp a b).to_preordering = precmp a b :=
begin
  rcases lt_trichotomy a b with h | h | h,
  { rw [h.cmp_eq_lt, h.precmp_eq_lt], refl },
  { rw [h.cmp_eq_eq, h.precmp_eq_equiv], refl },
  { rw [h.cmp_eq_gt, h.precmp_eq_gt], refl }
end

end ordering
