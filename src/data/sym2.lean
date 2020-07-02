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

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two, we have `sym2.mem` (the `has_mem`
instance), which is a `Prop`-valued membership test.  Given `a ∈ z`
for `z : sym2 α`, it does not appear to be possible, in general, to
*computably* give the other element in the pair.  For this,
`sym2.vmem a z` is a `Type`-valued predicate that contains this other
element.

## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs
-/

namespace sym2
variables {α : Type*}

/--
This is the relation capturing the notion of pairs equivalent up to permutations.
-/
inductive rel (α : Type*) : (α × α) → (α × α) → Prop
| refl (x y : α) : rel (x, y) (x, y)
| swap (x y : α) : rel (x, y) (y, x)

attribute [refl] rel.refl

@[symm] lemma rel.symm {x y : α × α} : rel α x y → rel α y x :=
by { intro a, cases a, exact a, apply rel.swap }

@[trans] lemma rel.trans {x y z : α × α} : rel α x y → rel α y z → rel α x z :=
by { intros a b, cases_matching* rel _ _ _; apply rel.refl <|> apply rel.swap }

instance rel.setoid (α : Type*) : setoid (α × α) :=
by { use rel α,
     split, { intros x, cases x, refl },
     split, { apply rel.symm },
     { intros x y z a b, apply rel.trans a b } }

end sym2

/--
This is the type for the symmetric square (i.e., the type of unordered pairs).
-/
@[reducible]
def sym2 (α : Type*) := quotient (sym2.rel.setoid α)

namespace sym2
universe u
variables {α : Type u}

lemma eq_swap {a b : α} : ⟦(a, b)⟧ = ⟦(b, a)⟧ :=
by { rw quotient.eq, apply rel.swap }

lemma congr_right (a b c : α) : ⟦(a, b)⟧ = ⟦(a, c)⟧ ↔ b = c :=
begin
  split,
  intro h, rw quotient.eq at h, cases h; refl,
  intro h, apply congr_arg _ h,
end


/--
The functor `sym2` is functorial, and this function constructs the induced maps.
-/
def map {α β : Type*} (f : α → β) : sym2 α → sym2 β :=
quotient.map (prod.map f f) begin
  rintros ⟨a₁, a₂⟩ ⟨b₁, b₂⟩ h,
  cases h,
  apply rel.refl,
  apply rel.swap,
end

@[simp]
lemma map_id : sym2.map (@id α) = id :=
by tidy

lemma map_comp {α β γ: Type*} {g : β → γ} {f : α → β} : sym2.map (g ∘ f) = sym2.map g ∘ sym2.map f :=
by tidy

section membership

/-! ### Declarations about membership -/

/--
This is a predicate that determines whether a given term is a member of a term of the
symmetric square.  From this point of view, the symmetric square is the subtype of
cardinality-two multisets on `α`.
-/
def mem (x : α) (z : sym2 α) : Prop :=
∃ (y : α), z = ⟦(x, y)⟧

instance : has_mem α (sym2 α) := ⟨mem⟩

lemma mk_has_mem (x y : α) : x ∈ ⟦(x, y)⟧ :=
⟨y, rfl⟩

/--
This is a type-valued version of the membership predicate `mem` that contains the other
element `y` of `z` such that `z = ⟦(x, y)⟧`.  It is a subsingleton already,
so there is no need to apply `trunc` to the type.
-/
def vmem (x : α) (z : sym2 α) : Type u :=
{y : α // z = ⟦(x, y)⟧}

instance (x : α) (z : sym2 α) : subsingleton {y : α // z = ⟦(x, y)⟧} :=
⟨by { rintros ⟨a, ha⟩ ⟨b, hb⟩, rw ha at hb, rw congr_right at hb, tidy, }⟩

/--
The `vmem` version of `mk_has_mem`.
-/
def mk_has_vmem (x y : α) : vmem x ⟦(x, y)⟧ :=
⟨y, rfl⟩

instance {a : α} {z : sym2 α} : has_lift (vmem a z) (mem a z) := ⟨λ h, ⟨h.val, h.property⟩⟩

/--
Given an element of a term of the symmetric square (using `vmem`), retrieve the other element.
-/
def vmem.other {a : α} {p : sym2 α} (h : vmem a p) : α := h.val

/--
The defining property of the other element is that it can be used to
reconstruct the term of the symmetric square.
-/
lemma vmem_other_spec {a : α} {z : sym2 α} (h : vmem a z) : z = ⟦(a, h.other)⟧ :=
by { dunfold vmem.other, tidy, }

/--
This is the `mem`-based version of `other`.
-/
noncomputable def mem.other {a : α} {z : sym2 α} (h : a ∈ z) : α :=
classical.some h

lemma mem_other_spec {a : α} {z : sym2 α} (h : a ∈ z) :
  ⟦(a, h.other)⟧ = z :=
begin
  dunfold mem.other,
  exact (classical.some_spec h).symm,
end

lemma other_is_mem_other {a : α} {z : sym2 α} (h : vmem a z) (h' : a ∈ z) :
  h.other = mem.other h' :=
by rw [←congr_right a, ←vmem_other_spec h, mem_other_spec]

lemma eq_pairs {x y z w : α} :
  ⟦(x, y)⟧ = ⟦(z, w)⟧ ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
by { split; intro h,
     { rw quotient.eq at h, cases h; tidy, },
     { cases h; rw [h.1, h.2], rw eq_swap, } }

lemma mem_iff {a b c : α} : a ∈ ⟦(b, c)⟧ ↔ a = b ∨ a = c :=
begin
  split,
  { intro h, cases h, rw eq_pairs at h_h, tidy },
  { intro h, cases h, rw h, apply mk_has_mem,
    rw h, rw eq_swap, apply mk_has_mem, }
end

end membership

/--
A type `α` is naturally included in the diagonal of `α × α`, this function gives the image
of this diagonal in `sym2 α`.
-/
def diag (x : α) : sym2 α := ⟦(x, x)⟧

/--
A predicate for testing whether an element of `sym2 α` is on the diagonal.
-/
def is_diag (z : sym2 α) : Prop :=
z ∈ set.range (@diag α)

lemma is_diag_iff_proj_eq (z : α × α) : is_diag ⟦z⟧ ↔ z.1 = z.2 :=
begin
  cases z with a b,
  split,
  { intro h, cases h with x h, dsimp [diag] at h,
    cases eq_pairs.mp h with h h; rw [←h.1, ←h.2], },
  { intro h, dsimp at h, rw h, use b, simp [diag], },
end

instance is_diag.decidable_pred (α : Type u) [decidable_eq α] : decidable_pred (@is_diag α) :=
begin
  intro z,
  induction z,
  change decidable (is_diag ⟦z⟧),
  rw is_diag_iff_proj_eq,
  apply_instance,
  apply subsingleton.elim,
end

section relations

/-! ### Declarations about symmetric relations -/

variables {r : α → α → Prop}

/--
Symmetric relations define a set on `sym2 α` by taking all those elements that are related.
-/
def from_rel (sym : symmetric r) : set (sym2 α) :=
(λ z, quotient.rec_on z (λ z, r z.1 z.2) (begin
  intros z w p,
  cases p,
  simp,
  simp,
  split; apply sym,
end))

@[simp]
lemma from_rel_prop {sym : symmetric r} {a b : α} : ⟦(a, b)⟧ ∈ from_rel sym  ↔ r a b :=
by tidy

end relations

end sym2
