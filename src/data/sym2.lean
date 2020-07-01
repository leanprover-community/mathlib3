/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/

import data.quot
import tactic
open function

/-!
# The symmetric square

This file defines symmetric squares, which is `α × α` modulo swapping.
This is also known as the type of unordered pairs.


## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs
-/

namespace sym2
universe u
variables {α : Type u}

/--
This is the relation capturing the notion of pairs equivalent up to permutations.
-/
inductive rel (α : Type u) : (α × α) → (α × α) → Prop
| refl (x y : α) : rel (x, y) (x, y)
| swap (x y : α) : rel (x, y) (y, x)

attribute [refl] rel.refl

@[symm] lemma rel.symm {x y : α × α} : rel α x y → rel α y x :=
by { tidy, cases a, exact a, apply rel.swap }

@[trans] lemma rel.trans {x y z : α × α} : rel α x y → rel α y z → rel α x z :=
by { tidy, cases_matching* rel _ _ _; apply rel.refl <|> apply rel.swap }

instance rel.setoid (α : Type u) : setoid (α × α) :=
by { use rel α, tidy, apply rel.trans a a_1 }

/--
This is the type for the symmetric square (i.e., the type of unordered pairs).
-/
@[reducible]
def sym2 (α : Type u) [h : setoid (α × α)] := quotient h

lemma eq_swap {a b : α} : ⟦(a, b)⟧ = ⟦(b, a)⟧ :=
by { rw quotient.eq, apply rel.swap }

lemma other_unique (a b c : α) : ⟦(a, b)⟧ = ⟦(a, c)⟧ ↔ b = c :=
begin
  split,
  intro h, rw quotient.eq at h, cases h; refl,
  intro h, apply congr_arg _ h,
end

/--
A type `α` is naturally included in the diagonal of `α × α`, this function gives the image
of this diagonal in `sym2 α`.
-/
def incl (x : α) : sym2 α := ⟦(x, x)⟧

/--
Checks whether a given element of `sym2 α` is in the image of `incl`.
-/
def is_diag (z : sym2 α) : Prop :=
quotient.rec_on z (λ y, y.1 = y.2) (by { tidy, cases p; refl, cases p; refl })

def image_incl_is_diag (z : sym2 α) (h : is_diag z) : ∃ x, z = incl x :=
by tidy

lemma diag_to_eq (x y : α) (h : is_diag ⟦(x, y)⟧) : x = y :=
by tidy

/--
The functor `sym2` is functorial, and this constructs induced maps.
-/
def induce {α β : Type u} (f : α → β) : sym2 α → sym2 β :=
λ z, quotient.rec_on z (λ x, ⟦(f x.1, f x.2)⟧)
begin
  intros, rw [eq_rec_constant, quotient.eq],
  cases p, refl, apply rel.swap,
end

@[simp]
def induce.id : sym2.induce (@id α) = id :=
by tidy

def induce.functorial {α β γ: Type u} {g : β → γ} {f : α → β} : sym2.induce (g ∘ f) = sym2.induce g ∘ sym2.induce f :=
by tidy

instance is_diag.decidable_pred (α : Type u) [decidable_eq α] : decidable_pred (@is_diag α) :=
begin
  intro x,
  induction x,
  solve_by_elim,
  cases x_p,
  simp only [],
  apply subsingleton.elim,
end

section membership

/-! ### Declarations about membership -/

/--
This is a predicate that determines whether a given term is a member of a term of the symmetric square.
From this point of view, the symmetric square is the subtype of cardinality-two multisets on `α`.
-/
def mem (x : α) (z : sym2 α) : Prop :=
∃ (y : α), z = ⟦(x, y)⟧

def mk_has_mem (x y : α) : mem x ⟦(x, y)⟧ :=
⟨y, rfl⟩

/--
This is a type-valued version of the membership predicate `mem` that contains the other
element `y` of `z` such that `z = ⟦(x, y)⟧`.  It is a subsingleton already,
so there is no need to apply `trunc` to the type.
-/
def vmem (x : α) (z : sym2 α) : Type u :=
{y : α // z = ⟦(x, y)⟧}

instance (x : α) (z : sym2 α) : subsingleton {y : α // z = ⟦(x, y)⟧} :=
⟨by { rintros ⟨a, ha⟩ ⟨b, hb⟩, rw ha at hb, rw other_unique at hb, tidy, }⟩

def mk_has_vmem (x y : α) : vmem x ⟦(x, y)⟧ :=
⟨y, rfl⟩

instance {a : α} {z : sym2 α} : has_lift (vmem a z) (mem a z) := ⟨λ h, ⟨h.val, h.property⟩⟩

/--
Given an element of a term of the symmetric square (using `vmem`), retrieve the other element.
-/
lemma other {a : α} {p : sym2 α} (h : vmem a p) : α := h.val

/--
The defining property of the other element is that it can be used to
reconstruct the term of the symmetric square.
-/
lemma other_spec (a : α) (z : sym2 α) (h : vmem a z) : z = ⟦(a, other h)⟧ :=
by { dunfold other, tidy, }

/--
This is the `mem`-based version of `other`.
-/
noncomputable
lemma mem_other {a : α} {z : sym2 α} (h : mem a z) : α :=
classical.some h

lemma mem_other_spec (a : α) (z : sym2 α) (h : mem a z) : ⟦(a, mem_other h)⟧ = z :=
begin
  dunfold mem_other,
  exact (classical.some_spec h).symm,
end

lemma other_is_mem_other {a : α} {z : sym2 α} (h : vmem a z) (h' : mem a z) :
  other h = mem_other h' :=
by rw [←other_unique a, ←other_spec a z, mem_other_spec]

lemma eq {x y z w : α} (h : ⟦(x, y)⟧ = ⟦(z, w)⟧):
  (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
by { rw quotient.eq at h, cases h; tidy }

lemma is_one_of {a b c : α} (h : mem a ⟦(b, c)⟧) : a = b ∨ a = c :=
by { cases h, have p := eq h_h, tidy }

end membership


section relations

/-! ### Declarations about symmetric relations -/

variables {r : α → α → Prop}

def in_rel (sym : symmetric r) (z : sym2 α) : Prop :=
quotient.rec_on z (λ z, r z.1 z.2) (begin
  intros z w p,
  cases p,
  simp,
  simp,
  split; apply sym,
end)

@[simp]
lemma in_rel_prop {sym : symmetric r} {a b : α} : in_rel sym ⟦(a, b)⟧ ↔ r a b :=
by tidy

end relations

end sym2
