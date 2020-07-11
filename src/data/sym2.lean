/-
Copyright (c) 2020 Kyle Miller All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Kyle Miller.
-/
import tactic.linarith
import data.sym

open function
open sym

/-!
# The symmetric square

This file defines the symmetric square, which is `α × α` modulo
swapping.  This is also known as the type of unordered pairs.

More generally, the symmetric square is the second symmetric power
(see `data.sym`). The equivalence is `sym2.equiv_sym`.

From the point of view that an unordered pair is equivalent to a
multiset of cardinality two (see `sym2.equiv_multiset`), there is a
`has_mem` instance `sym2.mem`, which is a `Prop`-valued membership
test.  Given `a ∈ z` for `z : sym2 α`, it does not appear to be
possible, in general, to *computably* give the other element in the
pair.  For this, `sym2.vmem a z` is a `Type`-valued membership test
that gives a way to obtain the other element with `sym2.vmem.other`.

Recall that an undirected graph (allowing self loops, but no multiple
edges) is equivalent to a symmetric relation on the vertex type `α`.
Given a symmetric relation on `α`, the corresponding edge set is
constructed by `sym2.from_rel`.

## Notation

The symmetric square has a setoid instance, so `⟦(a, b)⟧` denotes a
term of the symmetric square.

## Tags

symmetric square, unordered pairs, symmetric powers
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

lemma rel.is_equivalence : equivalence (rel α) :=
begin
  split, { intros x, cases x, refl },
  split, { apply rel.symm },
  { intros x y z a b, apply rel.trans a b },
end

instance rel.setoid (α : Type*) : setoid (α × α) :=
⟨rel α, rel.is_equivalence⟩

end sym2

/--
`sym2 α` is the symmetric square of `α`, which, in other words, is the
type of unordered pairs.

It is equivalent in a natural way to multisets of cardinality 2 (see
`sym2.equiv_multiset`).
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
@[nolint has_inhabited_instance]
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

lemma eq_iff {x y z w : α} :
  ⟦(x, y)⟧ = ⟦(z, w)⟧ ↔ (x = z ∧ y = w) ∨ (x = w ∧ y = z) :=
begin
  split; intro h,
  { rw quotient.eq at h, cases h; tidy, },
  { cases h; rw [h.1, h.2], rw eq_swap, }
end

lemma mem_iff {a b c : α} : a ∈ ⟦(b, c)⟧ ↔ a = b ∨ a = c :=
begin
  split,
  { intro h, cases h, rw eq_iff at h_h, tidy },
  { intro h, cases h, rw h, apply mk_has_mem,
    rw h, rw eq_swap, apply mk_has_mem, }
end

end membership

/--
A type `α` is naturally included in the diagonal of `α × α`, and this function gives the image
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
    cases eq_iff.mp h with h h; rw [←h.1, ←h.2], },
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
Symmetric relations define a set on `sym2 α` by taking all those pairs
of elements that are related.
-/
def from_rel (sym : symmetric r) : set (sym2 α) :=
λ z, quotient.rec_on z (λ z, r z.1 z.2)
begin
  intros z w p,
  cases p,
  simp,
  simp,
  split; apply sym,
end

@[simp]
lemma from_rel_proj_prop {sym : symmetric r} {z : α × α} : ⟦z⟧ ∈ from_rel sym ↔ r z.1 z.2 :=
by tidy

@[simp]
lemma from_rel_prop {sym : symmetric r} {a b : α} : ⟦(a, b)⟧ ∈ from_rel sym ↔ r a b :=
by simp only [from_rel_proj_prop]

lemma from_rel_irreflexive {sym : symmetric r} :
  irreflexive r ↔ ∀ {z}, z ∈ from_rel sym → ¬is_diag z :=
begin
  split,
  { intros h z hr hd,
    induction z,
    have hd' := (is_diag_iff_proj_eq _).mp hd,
    have hr' := from_rel_proj_prop.mp hr,
    rw hd' at hr',
    exact h _ hr',
    refl, },
  { intros h x hr,
    rw ← @from_rel_prop _ _ sym at hr,
    exact h hr ⟨x, rfl⟩, }
end

end relations

section sym_equiv

/-! ### Equivalence to the second symmetric power -/

local attribute [instance] vector.perm.is_setoid

private def from_vector {α : Type*} : vector α 2 → α × α
| ⟨[a, b], h⟩ := (a, b)

private lemma perm_card_two_iff {α : Type*} {a₁ b₁ a₂ b₂ : α} :
  [a₁, b₁].perm [a₂, b₂] ↔ (a₁ = a₂ ∧ b₁ = b₂) ∨ (a₁ = b₂ ∧ b₁ = a₂) :=
begin
  split, swap,
  intro h, cases h; rw [h.1, h.2], apply list.perm.swap', refl,
  intro h,
  rw ←multiset.coe_eq_coe at h,
  repeat {rw ←multiset.cons_coe at h},
  repeat {rw multiset.cons_eq_cons at h},
  cases h,
  { cases h, cases h_right,
    left, simp [h_left, h_right.1],
    simp at h_right, tauto, },
  { rcases h.2 with ⟨cs, h'⟩,
    repeat {rw multiset.cons_eq_cons at h'},
    simp only [multiset.zero_ne_cons, multiset.coe_nil_eq_zero, exists_false, or_false, and_false, false_and] at h',
    right, simp [h'.1.1, h'.2.1], },
end

/--
The symmetric square is equivalent to length-2 vectors up to permutations.
-/
def sym2_equiv_sym' {α : Type*} : equiv (sym2 α) (sym' α 2) :=
{ to_fun := quotient.map (λ (x : α × α), ⟨[x.1, x.2], rfl⟩) (begin
    intros x y h, cases h, refl, apply list.perm.swap', refl,
  end),
  inv_fun := quotient.map from_vector (begin
    rintros ⟨x, hx⟩ ⟨y, hy⟩ h,
    cases x with x0 x, simp at hx, tauto,
    cases x with x1 x, simp at hx, exfalso, linarith [hx],
    cases x with x2 x, swap, simp at hx, exfalso, linarith [hx],
    cases y with y0 y, simp at hy, tauto,
    cases y with y1 y, simp at hy, exfalso, linarith [hy],
    cases y with y2 y, swap, simp at hy, exfalso, linarith [hy],
    cases perm_card_two_iff.mp h; rw [h_1.1, h_1.2],
    refl,
    apply sym2.rel.swap,
  end),
  left_inv := by tidy,
  right_inv := begin
    intro x,
    induction x,
    cases x with x hx,
    cases x with x0 x, simp at hx, tauto,
    cases x with x1 x, simp at hx, exfalso, linarith [hx],
    cases x with x2 x, swap, simp at hx, exfalso, linarith [hx],
    refl,
    refl,
  end }

/--
The symmetric square is equivalent to the second symmetric power.
-/
def equiv_sym (α : Type*) : sym2 α ≃ sym α 2 :=
equiv.trans sym2_equiv_sym' (sym_equiv_sym' α 2).symm

/--
The symmetric square is equivalent to multisets of cardinality
two. (This is currently a synonym for `equiv_sym`, but it's provided
in case the definition for `sym` changes.)
-/
def equiv_multiset (α : Type*) : sym2 α ≃ {s : multiset α // s.card = 2} :=
equiv_sym α

end sym_equiv

end sym2
