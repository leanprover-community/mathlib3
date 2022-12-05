/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import data.subtype
import logic.function.iterate
import logic.unique
import order.bounded_order
import order.rel_classes
import tactic.alias
import tactic.lift

/-!
# Basic properties of sets

Sets in Lean are homogeneous; all their elements have the same type. Sets whose elements
have type `X` are thus defined as `set X := X → Prop`. Note that this function need not
be decidable. The definition is in the core library.

This file provides some basic definitions related to sets and functions not present in the core
library, as well as extra lemmas for functions in the core library (empty set, univ, union,
intersection, insert, singleton, set-theoretic difference, complement, and powerset).

Note that a set is a term, not a type. There is a coercion from `set α` to `Type*` sending
`s` to the corresponding subtype `↥s`.

See also the file `set_theory/zfc.lean`, which contains an encoding of ZFC set theory in Lean.

## Main definitions

Notation used here:

-  `f : α → β` is a function,

-  `s : set α` and `s₁ s₂ : set α` are subsets of `α`

-  `t : set β` is a subset of `β`.

Definitions in the file:

* `nonempty s : Prop` : the predicate `s ≠ ∅`. Note that this is the preferred way to express the
  fact that `s` has an element (see the Implementation Notes).

* `preimage f t : set α` : the preimage f⁻¹(t) (written `f ⁻¹' t` in Lean) of a subset of β.

* `subsingleton s : Prop` : the predicate saying that `s` has at most one element.

* `nontrivial s : Prop` : the predicate saying that `s` has at least two distinct elements.

* `range f : set β` : the image of `univ` under `f`.
  Also works for `{p : Prop} (f : p → α)` (unlike `image`)

* `inclusion s₁ s₂ : ↥s₁ → ↥s₂` : the map `↥s₁ → ↥s₂` induced by an inclusion `s₁ ⊆ s₂`.

## Notation

* `f ⁻¹' t` for `preimage f t`

* `f '' s` for `image f s`

* `sᶜ` for the complement of `s`

## Implementation notes

* `s.nonempty` is to be preferred to `s ≠ ∅` or `∃ x, x ∈ s`. It has the advantage that
the `s.nonempty` dot notation can be used.

* For `s : set α`, do not use `subtype s`. Instead use `↥s` or `(s : Type*)` or `s`.

## Tags

set, sets, subset, subsets, image, preimage, pre-image, range, union, intersection, insert,
singleton, complement, powerset

-/

open function

universes u v w x
variables {α : Type*} {s t u : set α} {p q : α → Prop} {a b x : α}

namespace set

/-! ### Set coercion to a type -/

/-- Coercion from a set to the corresponding subtype. -/
instance : has_coe_to_sort (set α) Type* := ⟨λ s, {x // x ∈ s}⟩

lemma coe_eq_subtype (s : set α) : ↥s = {x // x ∈ s} := rfl
@[simp] lemma coe_set_of (p : α → Prop) : ↥{x | p x} = {x // p x} := rfl

instance pi_set_coe.can_lift (ι : Type u) (α : Π i : ι, Type v) [Π i, nonempty (α i)] (s : set ι) :
  can_lift (Π i : s, α i) (Π i, α i) (λ f i, f i) (λ _, true) :=
pi_subtype.can_lift ι α s

instance pi_set_coe.can_lift' (ι : Type u) (α : Type v) [nonempty α] (s : set ι) :
  can_lift (s → α) (ι → α) (λ f i, f i) (λ _, true) :=
pi_set_coe.can_lift ι (λ _, α) s

end set

namespace set_coe

@[simp] lemma «forall» {p : s → Prop} : (∀ x : s, p x) ↔ ∀ x h, p ⟨x, h⟩ := subtype.forall
@[simp] lemma «exists» {p : s → Prop} : (∃ x : s, p x) ↔ ∃ x h, p ⟨x, h⟩ := subtype.exists

lemma exists' {p : Π x, x ∈ s → Prop} : (∃ x (h : x ∈ s), p x h) ↔ ∃ x : s, p x x.2 :=
(@set_coe.exists _ _ $ λ x, p x.1 x.2).symm

lemma forall' {p : Π x, x ∈ s → Prop} : (∀ x (h : x ∈ s), p x h) ↔ ∀ x : s, p x x.2 :=
(@set_coe.forall _ _ $ λ x, p x.1 x.2).symm

@[simp] lemma cast : ∀ {s t : set α} (H' : s = t) (H : ↥s = ↥t) (x : s), cast H x = ⟨x.1, H' ▸ x.2⟩
| s _ rfl _ ⟨x, h⟩ := rfl

lemma ext {a b : s} : (↑a : α) = ↑b → a = b := subtype.eq
lemma ext_iff {a b : s} : (↑a : α) = ↑b ↔ a = b := subtype.coe_inj

end set_coe

/-- See also `subtype.prop` -/
lemma subtype.mem (p : s) : (p : α) ∈ s := p.prop

namespace set

/-! ### Order -/

instance : has_le (set α) := ⟨λ s t, ∀ ⦃x⦄, x ∈ s → x ∈ t⟩
instance : has_lt (set α) := ⟨λ s t, s ≤ t ∧ ¬ t ≤ s⟩
instance : has_subset (set α) := ⟨(≤)⟩
instance : has_ssubset (set α) := ⟨(<)⟩
instance : has_union (set α) := ⟨λ s t, {x | x ∈ s ∨ x ∈ t}⟩
instance : has_inter (set α) := ⟨λ s t, {x | x ∈ s ∧ x ∈ t}⟩
instance : has_compl (set α) := ⟨λ s, {x | x ∉ s}⟩

@[simp] lemma le_eq_subset : ((≤) : set α → set α → Prop) = (⊆) := rfl
@[simp] lemma lt_eq_ssubset : ((<) : set α → set α → Prop) = (⊂) := rfl

lemma le_iff_subset : s ≤ t ↔ s ⊆ t := iff.rfl
lemma lt_iff_ssubset : s < t ↔ s ⊂ t := iff.rfl

alias le_iff_subset ↔ _root_.has_le.le.subset _root_.has_subset.subset.le
alias lt_iff_ssubset ↔ _root_.has_lt.lt.ssubset _root_.has_ssubset.ssubset.lt

instance : partial_order (set α) :=
{ le := (≤),
  lt := (<),
  ..(infer_instance : partial_order (α → Prop)) }

instance : bounded_order (set α) :=
{ bot := ∅,
  top := univ,
  ..(infer_instance : bounded_order (α → Prop)) }

instance : is_refl (set α) (⊆) := has_le.le.is_refl
instance : is_trans (set α) (⊆) := has_le.le.is_trans
instance : is_antisymm (set α) (⊆) := has_le.le.is_antisymm
instance : is_irrefl (set α) (⊂) := has_lt.lt.is_irrefl
instance : is_trans (set α) (⊂) := has_lt.lt.is_trans
instance : is_asymm (set α) (⊂) := has_lt.lt.is_asymm
instance : is_nonstrict_strict_order (set α) (⊆) (⊂) := ⟨λ _ _, iff.rfl⟩

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
lemma subset_def : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl
lemma ssubset_def : s ⊂ t = (s ⊆ t ∧ ¬ t ⊆ s) := rfl

@[refl] lemma subset.refl (a : set α) : a ⊆ a := assume x, id
lemma subset.rfl : s ⊆ s := subset.refl s

@[trans] lemma subset.trans : s ⊆ t → t ⊆ u → s ⊆ u := has_subset.subset.trans

@[trans] lemma mem_of_eq_of_mem (h : a = b) (hb : b ∈ s) : a ∈ s := h.symm ▸ hb

@[ext] lemma ext (h : ∀ x, x ∈ s ↔ x ∈ t) : s = t := funext $ λ x, propext $ h x

lemma ext_iff : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := ⟨λ h x, by rw h, ext⟩

lemma subset.antisymm (h₁ : s ⊆ t) (h₂ : t ⊆ s) : s = t := le_antisymm h₁ h₂
lemma subset.antisymm_iff : s = t ↔ s ⊆ t ∧ t ⊆ s := le_antisymm_iff

alias subset.antisymm ← eq_of_subset_of_subset

lemma mem_of_subset_of_mem (h : s ⊆ t) : a ∈ s → a ∈ t := @h _

lemma not_mem_subset (h : s ⊆ t) : a ∉ t → a ∉ s := mt $ mem_of_subset_of_mem h

lemma not_subset : ¬ s ⊆ t ↔ ∃ a ∈ s, a ∉ t := by simp only [subset_def, not_forall]

/-! ### Definition of strict subsets `s ⊂ t` and basic properties. -/

protected lemma eq_or_ssubset_of_subset (h : s ⊆ t) : s = t ∨ s ⊂ t := eq_or_lt_of_le h
protected lemma ssubset_iff_subset_ne : s ⊂ t ↔ s ⊆ t ∧ s ≠ t := @lt_iff_le_and_ne (set α) _ s t
protected lemma ssubset_of_ssubset_of_subset : s ⊂ t → t ⊆ u → s ⊂ u := @lt_of_lt_of_le _ _ s _ _
protected lemma ssubset_of_subset_of_ssubset : s ⊆ t → t ⊂ u → s ⊂ u := @lt_of_le_of_lt _ _ s _ _

lemma exists_of_ssubset (h : s ⊂ t) : ∃ x ∈ t, x ∉ s := not_subset.1 h.2

lemma ssubset_iff_of_subset (h : s ⊆ t) : s ⊂ t ↔ ∃ x ∈ t, x ∉ s :=
⟨exists_of_ssubset, λ ⟨x, hxt, hxs⟩, ⟨h, λ h, hxs $ h hxt⟩⟩

end set

namespace set

variables {β : Type v} {γ : Type w} {ι : Sort x}

instance : inhabited (set α) := ⟨∅⟩

@[trans] lemma mem_of_mem_of_subset (ha : a ∈ s) (h : s ⊆ t) : a ∈ t := h ha

lemma forall_in_swap {p : α → β → Prop} : (∀ (a ∈ s) b, p a b) ↔ ∀ b (a ∈ s), p a b :=
⟨λ h b a ha, h _ ha _, λ h a ha b, h _ _ ha⟩

/-! ### Lemmas about `mem` and `set_of` -/

lemma mem_set_of : a ∈ {x | p x} ↔ p a := iff.rfl
lemma nmem_set_of_iff : a ∉ {x | p x} ↔ ¬ p a := iff.rfl

/-- If `h : a ∈ {x | p x}` then `h.out : p x`. These are definitionally equal, but this can
nevertheless be useful for various reasons, e.g. to apply further projection notation or in an
argument to `simp`. -/
lemma _root_.has_mem.mem.out {p : α → Prop} (h : a ∈ {x | p x}) : p a := h

@[simp] lemma set_of_mem_eq : {x | x ∈ s} = s := rfl

lemma set_of_set : set_of s = s := rfl

lemma set_of_app_iff : {x | p x} a ↔ p a := iff.rfl

lemma mem_def : a ∈ s ↔ s a := iff.rfl

lemma set_of_bijective : bijective (set_of : (α → Prop) → set α) := bijective_id

@[simp] lemma set_of_subset_set_of : {a | p a} ⊆ {a | q a} ↔ ∀ a, p a → q a := iff.rfl

/-! ### Subset and strict subset relations -/

lemma not_mem_empty (x : α) : x ∉ (∅ : set α) := id

@[simp] lemma not_not_mem : ¬ a ∉ s ↔ a ∈ s := not_not

/-! ### Non-empty sets -/

/-- The property `s.nonempty` expresses the fact that the set `s` is not empty. It should be used
in lemma assumptions instead of `∃ x, x ∈ s` or `s ≠ ∅` as it gives access to a nice API thanks to
the dot notation. -/
protected def nonempty (s : set α) : Prop := ∃ x, x ∈ s

lemma nonempty_def : s.nonempty ↔ ∃ x, x ∈ s := iff.rfl

lemma nonempty_of_mem (h : a ∈ s) : s.nonempty := ⟨a, h⟩

lemma nonempty.not_subset_empty : s.nonempty → ¬ s ⊆ ∅ := λ ⟨x, hx⟩ hs, hs hx

lemma nonempty.mono (ht : s ⊆ t) (hs : s.nonempty) : t.nonempty := hs.imp ht

lemma nonempty_iff_univ_nonempty : nonempty α ↔ (univ : set α).nonempty :=
⟨λ ⟨x⟩, ⟨x, trivial⟩, λ ⟨x, _⟩, ⟨x⟩⟩

@[simp] lemma univ_nonempty : ∀ [h : nonempty α], (univ : set α).nonempty
| ⟨x⟩ := ⟨x, trivial⟩

@[simp] lemma nonempty_coe_sort : nonempty s ↔ s.nonempty := nonempty_subtype
lemma nonempty_of_nonempty_subtype [nonempty s] : s.nonempty := nonempty_coe_sort.1 ‹_›

alias nonempty_coe_sort ↔ _ nonempty.coe_sort
alias nonempty.coe_sort ← nonempty.to_subtype

lemma nonempty.to_type : s.nonempty → nonempty α := λ ⟨x, hx⟩, ⟨x⟩

instance [nonempty α] : nonempty (set.univ : set α) := set.univ_nonempty.to_subtype

/-- Extract a witness from `s.nonempty`. This function might be used instead of case analysis
on the argument. Note that it makes a proof depend on the `classical.choice` axiom. -/
protected noncomputable def nonempty.some : s.nonempty → α := classical.some

protected lemma nonempty.some_mem (h : s.nonempty) : h.some ∈ s := classical.some_spec h

/-! ### Empty set -/

lemma empty_def : (∅ : set α) = {x | false} := rfl

@[simp] lemma mem_empty_iff_false (x : α) : x ∈ (∅ : set α) ↔ false := iff.rfl

@[simp] lemma set_of_false : {a : α | false} = ∅ := rfl

@[simp] lemma empty_subset (s : set α) : ∅ ⊆ s.

lemma subset_empty_iff : s ⊆ ∅ ↔ s = ∅ :=
(subset.antisymm_iff.trans $ and_iff_left (empty_subset _)).symm

lemma eq_empty_iff_forall_not_mem : s = ∅ ↔ ∀ x, x ∉ s := subset_empty_iff.symm

lemma eq_empty_of_forall_not_mem (h : ∀ x, x ∉ s) : s = ∅ := subset_empty_iff.1 h

lemma eq_empty_of_subset_empty : s ⊆ ∅ → s = ∅ := subset_empty_iff.1

lemma eq_empty_of_is_empty [is_empty α] (s : set α) : s = ∅ :=
eq_empty_of_subset_empty $ λ x hx, is_empty_elim x

/-- There is exactly one set of a type that is empty. -/
instance unique_empty [is_empty α] : unique (set α) :=
{ default := ∅, uniq := eq_empty_of_is_empty }

/-- See also `set.nonempty_iff_ne_empty`. -/
lemma not_nonempty_iff_eq_empty : ¬s.nonempty ↔ s = ∅ :=
by simp only [set.nonempty, eq_empty_iff_forall_not_mem, not_exists]

/-- See also `set.not_nonempty_iff_eq_empty`. -/
lemma nonempty_iff_ne_empty : s.nonempty ↔ s ≠ ∅ := not_nonempty_iff_eq_empty.not_right

alias nonempty_iff_ne_empty ↔ nonempty.ne_empty _

@[simp] lemma not_nonempty_empty : ¬(∅ : set α).nonempty := λ ⟨x, hx⟩, hx

@[simp] lemma is_empty_coe_sort : is_empty s ↔ s = ∅ :=
not_iff_not.1 $ by simpa using nonempty_iff_ne_empty

lemma eq_empty_or_nonempty (s : set α) : s = ∅ ∨ s.nonempty :=
or_iff_not_imp_left.2 nonempty_iff_ne_empty.2

lemma subset_eq_empty (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
subset_empty_iff.1 $ e ▸ h

lemma ball_empty_iff {p : α → Prop} : (∀ x ∈ (∅ : set α), p x) ↔ true :=
iff_true_intro $ λ x, false.elim

instance (α : Type u) : is_empty.{u+1} (∅ : set α) := ⟨λ x, x.2⟩

@[simp] lemma empty_ssubset : ∅ ⊂ s ↔ s.nonempty :=
(@bot_lt_iff_ne_bot (set α) _ _ _).trans nonempty_iff_ne_empty.symm

alias empty_ssubset ↔ _ nonempty.empty_ssubset

/-!
### Universal set

In Lean `@univ α` (or `univ : set α`) is the set that contains all elements of type `α`.
Mathematically it is the same as `α` but it has a different type.
-/

@[simp] lemma set_of_true : {x : α | true} = univ := rfl

@[simp] lemma mem_univ (x : α) : x ∈ @univ α := trivial

@[simp] lemma univ_eq_empty_iff : (univ : set α) = ∅ ↔ is_empty α :=
eq_empty_iff_forall_not_mem.trans ⟨λ H, ⟨λ x, H x trivial⟩, λ H x _, @is_empty.false α H x⟩

lemma empty_ne_univ [nonempty α] : (∅ : set α) ≠ univ :=
λ e, not_is_empty_of_nonempty α $ univ_eq_empty_iff.1 e.symm

@[simp] lemma subset_univ (s : set α) : s ⊆ univ := λ x H, trivial

lemma univ_subset_iff : univ ⊆ s ↔ s = univ := @top_le_iff _ _ _ s

alias univ_subset_iff ↔ eq_univ_of_univ_subset _

lemma eq_univ_iff_forall : s = univ ↔ ∀ x, x ∈ s :=
univ_subset_iff.symm.trans $ forall_congr $ λ x, imp_iff_right trivial

alias eq_univ_iff_forall ↔ _ eq_univ_of_forall

lemma nonempty.eq_univ [subsingleton α] : s.nonempty → s = univ :=
by { rintro ⟨x, hx⟩, refine eq_univ_of_forall (λ y, by rwa subsingleton.elim y x) }

lemma eq_univ_of_subset (h : s ⊆ t) (hs : s = univ) : t = univ :=
eq_univ_of_univ_subset $ hs ▸ h

lemma exists_mem_of_nonempty (α) : ∀ [nonempty α], ∃x:α, x ∈ (univ : set α)
| ⟨x⟩ := ⟨x, trivial⟩

lemma ne_univ_iff_exists_not_mem (s : set α) : s ≠ univ ↔ ∃ a, a ∉ s :=
by rw [←not_forall, ←eq_univ_iff_forall]

lemma not_subset_iff_exists_mem_not_mem : ¬ s ⊆ t ↔ ∃ x, x ∈ s ∧ x ∉ t :=
by simp [subset_def]

lemma univ_unique [unique α] : @set.univ α = {default} :=
set.ext $ λ x, iff_of_true trivial $ subsingleton.elim x default

lemma ssubset_univ_iff : s ⊂ univ ↔ s ≠ univ := @lt_top_iff_ne_top _ _ _ s

instance nontrivial_of_nonempty [nonempty α] : nontrivial (set α) := ⟨⟨∅, univ, empty_ne_univ⟩⟩

/-!
### Lemmas about `insert`

`insert α s` is the set `{α} ∪ s`.
-/

lemma insert_def (x : α) (s : set α) : insert x s = { y | y = x ∨ y ∈ s } := rfl

@[simp] lemma subset_insert (x : α) (s : set α) : s ⊆ insert x s := λ y, or.inr

lemma mem_insert (x : α) (s : set α) : x ∈ insert x s := or.inl rfl

lemma mem_insert_of_mem (y : α) : a ∈ s → a ∈ insert y s := or.inr

lemma eq_or_mem_of_mem_insert {x a : α} : x ∈ insert a s → x = a ∨ x ∈ s := id

lemma mem_of_mem_insert_of_ne : b ∈ insert a s → b ≠ a → b ∈ s := or.resolve_left
lemma eq_of_not_mem_of_mem_insert : b ∈ insert a s → b ∉ s → b = a := or.resolve_right

@[simp] lemma mem_insert_iff {x a : α} : x ∈ insert a s ↔ x = a ∨ x ∈ s := iff.rfl

@[simp] lemma insert_eq_of_mem (h : a ∈ s) : insert a s = s :=
ext $ λ x, or_iff_right_of_imp $ λ e, e.symm ▸ h

lemma ne_insert_of_not_mem (t : set α) : a ∉ s → s ≠ insert a t :=
mt $ λ e, e.symm ▸ mem_insert _ _

@[simp] lemma insert_eq_self : insert a s = s ↔ a ∈ s := ⟨λ h, h ▸ mem_insert _ _, insert_eq_of_mem⟩

lemma insert_ne_self : insert a s ≠ s ↔ a ∉ s := insert_eq_self.not

lemma insert_subset : insert a s ⊆ t ↔ (a ∈ t ∧ s ⊆ t) :=
by simp only [subset_def, or_imp_distrib, forall_and_distrib, forall_eq, mem_insert_iff]

lemma insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t := λ x, or.imp_right (@h _)

lemma insert_subset_insert_iff (ha : a ∉ s) : insert a s ⊆ insert a t ↔ s ⊆ t :=
begin
  refine ⟨λ h x hx, _, insert_subset_insert⟩,
  rcases h (subset_insert _ _ hx) with (rfl|hxt),
  exacts [(ha hx).elim, hxt]
end

lemma ssubset_iff_insert : s ⊂ t ↔ ∃ a ∉ s, insert a s ⊆ t :=
begin
  simp only [insert_subset, exists_and_distrib_right, ssubset_def, not_subset],
  simp only [exists_prop, and_comm]
end

lemma ssubset_insert (h : a ∉ s) : s ⊂ insert a s := ssubset_iff_insert.2 ⟨a, h, subset.rfl⟩

lemma insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
ext $ λ x, or.left_comm

@[simp] lemma insert_idem (a : α) (s : set α) : insert a (insert a s) = insert a s :=
insert_eq_of_mem $ mem_insert _ _

lemma insert_union : insert a s ∪ t = insert a (s ∪ t) := ext $ λ x, or.assoc

@[simp] lemma union_insert : s ∪ insert a t = insert a (s ∪ t) := ext $ λ x, or.left_comm

@[simp] lemma insert_nonempty (a : α) (s : set α) : (insert a s).nonempty := ⟨a, mem_insert a s⟩

instance (a : α) (s : set α) : nonempty (insert a s : set α) := (insert_nonempty a s).to_subtype

lemma insert_inter_distrib (a : α) (s t : set α) : insert a (s ∩ t) = insert a s ∩ insert a t :=
ext $ λ y, or_and_distrib_left

lemma insert_union_distrib (a : α) (s t : set α) : insert a (s ∪ t) = insert a s ∪ insert a t :=
ext $ λ _, or_or_distrib_left _ _ _

lemma insert_inj (ha : a ∉ s) : insert a s = insert b s ↔ a = b :=
⟨λ h, eq_of_not_mem_of_mem_insert (h.subst $ mem_insert a s) ha, congr_arg _⟩

-- useful in proofs by induction
lemma forall_of_forall_insert {P : α → Prop} {s : set α}
  (H : ∀ x, x ∈ insert a s → P x) (x) (h : x ∈ s) : P x := H _ (or.inr h)

lemma forall_insert_of_forall {P : α → Prop} {s : set α}
  (H : ∀ x, x ∈ s → P x) (ha : P a) (x) (h : x ∈ insert a s) : P x :=
h.elim (λ e, e.symm ▸ ha) (H _)

lemma bex_insert_iff {P : α → Prop} : (∃ x ∈ insert a s, P x) ↔ P a ∨ ∃ x ∈ s, P x :=
bex_or_left_distrib.trans $ or_congr_left' bex_eq_left

lemma ball_insert_iff {P : α → Prop} : (∀ x ∈ insert a s, P x) ↔ P a ∧ ∀ x ∈ s, P x :=
ball_or_left_distrib.trans $ and_congr_left' forall_eq

/-! ### Lemmas about singletons -/

lemma singleton_def (a : α) : ({a} : set α) = insert a ∅ := (insert_emptyc_eq _).symm

@[simp] lemma mem_singleton_iff {a b : α} : a ∈ ({b} : set α) ↔ a = b := iff.rfl

alias mem_singleton_iff ↔ eq_of_mem_singleton mem_singleton_of_eq

@[simp] lemma set_of_eq_eq_singleton : {n | n = a} = {a} := rfl
@[simp] lemma set_of_eq_eq_singleton' : {x | a = x} = {a} := ext $ λ x, eq_comm

-- TODO: again, annotation needed
@[simp] lemma mem_singleton (a : α) : a ∈ ({a} : set α) := @rfl _ _

@[simp] lemma singleton_eq_singleton_iff : {a} = ({b} : set α) ↔ a = b :=
ext_iff.trans eq_iff_eq_cancel_left

lemma singleton_injective : injective (singleton : α → set α) := λ _ _, singleton_eq_singleton_iff.1

lemma insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s := rfl

@[simp] lemma singleton_nonempty (a : α) : ({a} : set α).nonempty := ⟨a, rfl⟩
@[simp] lemma singleton_ne_empty (a : α) : ({a} : set α) ≠ ∅ := (singleton_nonempty _).ne_empty

@[simp] lemma empty_ssubset_singleton : (∅ : set α) ⊂ {a} := (singleton_nonempty _).empty_ssubset

@[simp] lemma singleton_subset_iff : {a} ⊆ s ↔ a ∈ s := forall_eq

lemma set_compr_eq_eq_singleton : {b | b = a} = {a} := rfl

@[simp] lemma singleton_union : {a} ∪ s = insert a s := rfl

@[simp] lemma union_singleton : s ∪ {a} = insert a s := union_comm _ _

@[simp] lemma singleton_inter_nonempty : ({a} ∩ s).nonempty ↔ a ∈ s :=
by simp only [set.nonempty, mem_inter_iff, mem_singleton_iff, exists_eq_left]

@[simp] lemma inter_singleton_nonempty : (s ∩ {a}).nonempty ↔ a ∈ s :=
by rw [inter_comm, singleton_inter_nonempty]

@[simp] lemma singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
not_nonempty_iff_eq_empty.symm.trans singleton_inter_nonempty.not

@[simp] lemma inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s :=
by rw [inter_comm, singleton_inter_eq_empty]

lemma nmem_singleton_empty : s ∉ ({∅} : set (set α)) ↔ s.nonempty :=
nonempty_iff_ne_empty.symm

instance unique_singleton (a : α) : unique ↥({a} : set α) :=
⟨⟨⟨a, mem_singleton a⟩⟩, λ ⟨x, h⟩, subtype.eq h⟩

lemma eq_singleton_iff_unique_mem : s = {a} ↔ a ∈ s ∧ ∀ x ∈ s, x = a :=
subset.antisymm_iff.trans $ and.comm.trans $ and_congr_left' singleton_subset_iff

lemma eq_singleton_iff_nonempty_unique_mem : s = {a} ↔ s.nonempty ∧ ∀ x ∈ s, x = a :=
eq_singleton_iff_unique_mem.trans $ and_congr_left $ λ H, ⟨λ h', ⟨_, h'⟩, λ ⟨x, h⟩, H x h ▸ h⟩

-- while `simp` is capable of proving this, it is not capable of turning the LHS into the RHS.
@[simp] lemma default_coe_singleton (x : α) : (default : ({x} : set α)) = ⟨x, rfl⟩ := rfl

/-! ### Lemmas about pairs -/

@[simp] lemma pair_eq_singleton (a : α) : ({a, a} : set α) = {a} := union_self _

lemma pair_comm (a b : α) : ({a, b} : set α) = {b, a} := union_comm _ _

lemma pair_eq_pair_iff {x y z w : α} :
  ({x, y} : set α) = {z, w} ↔ x = z ∧ y = w ∨ x = w ∧ y = z :=
begin
  simp only [set.subset.antisymm_iff, set.insert_subset, set.mem_insert_iff, set.mem_singleton_iff,
    set.singleton_subset_iff],
  split,
  { tauto! },
  { rintro (⟨rfl,rfl⟩|⟨rfl,rfl⟩); simp }
end

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/

section sep
variables {p q : α → Prop}

lemma mem_sep (xs : x ∈ s) (px : p x) : x ∈ {x ∈ s | p x} := ⟨xs, px⟩

@[simp] lemma sep_mem_eq : {x ∈ s | x ∈ t} = s ∩ t := rfl

@[simp] lemma mem_sep_iff : x ∈ {x ∈ s | p x} ↔ x ∈ s ∧ p x := iff.rfl

lemma sep_ext_iff : {x ∈ s | p x} = {x ∈ s | q x} ↔ ∀ x ∈ s, (p x ↔ q x) :=
by simp_rw [ext_iff, mem_sep_iff, and.congr_right_iff]

lemma sep_eq_of_subset (h : s ⊆ t) : {x ∈ t | x ∈ s} = s :=
inter_eq_self_of_subset_right h

@[simp] lemma sep_subset (s : set α) (p : α → Prop) : {x ∈ s | p x} ⊆ s := λ x, and.left

@[simp] lemma sep_eq_self_iff_mem_true : {x ∈ s | p x} = s ↔ ∀ x ∈ s, p x :=
by simp_rw [ext_iff, mem_sep_iff, and_iff_left_iff_imp]

@[simp] lemma sep_eq_empty_iff_mem_false : {x ∈ s | p x} = ∅ ↔ ∀ x ∈ s, ¬ p x :=
by simp_rw [ext_iff, mem_sep_iff, mem_empty_iff_false, iff_false, not_and]

@[simp] lemma sep_true : {x ∈ s | true} = s := inter_univ s

@[simp] lemma sep_false : {x ∈ s | false} = ∅ := inter_empty s

@[simp] lemma sep_empty (p : α → Prop) : {x ∈ (∅ : set α) | p x} = ∅ := empty_inter p

@[simp] lemma sep_univ : {x ∈ (univ : set α) | p x} = {x | p x} := univ_inter p

@[simp] lemma sep_union : {x ∈ s ∪ t | p x} = {x ∈ s | p x} ∪ {x ∈ t | p x} :=
union_inter_distrib_right

@[simp] lemma sep_inter : {x ∈ s ∩ t | p x} = {x ∈ s | p x} ∩ {x ∈ t | p x} :=
inter_inter_distrib_right s t p

@[simp] lemma sep_and : {x ∈ s | p x ∧ q x} = {x ∈ s | p x} ∩ {x ∈ s | q x} :=
inter_inter_distrib_left s p q

@[simp] lemma sep_or : {x ∈ s | p x ∨ q x} = {x ∈ s | p x} ∪ {x ∈ s | q x} :=
inter_union_distrib_left

@[simp] lemma sep_set_of : {x ∈ {y | p y} | q x} = {x | p x ∧ q x} := rfl

end sep

@[simp] lemma subset_singleton_iff : s ⊆ {a} ↔ ∀ b ∈ s, b = a := iff.rfl

lemma subset_singleton_iff_eq : s ⊆ {a} ↔ s = ∅ ∨ s = {a} :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { exact ⟨λ _, or.inl rfl, λ _, empty_subset _⟩ },
  { simp [eq_singleton_iff_nonempty_unique_mem, hs, hs.ne_empty] }
end

lemma nonempty.subset_singleton_iff (h : s.nonempty) : s ⊆ {a} ↔ s = {a} :=
subset_singleton_iff_eq.trans $ or_iff_right h.ne_empty

lemma ssubset_singleton_iff : s ⊂ {a} ↔ s = ∅ :=
begin
  rw [ssubset_iff_subset_ne, subset_singleton_iff_eq, or_and_distrib_right, and_not_self, or_false,
    and_iff_left_iff_imp],
  exact λ h, ne_of_eq_of_ne h (singleton_ne_empty _).symm,
end

alias ssubset_singleton_iff ↔ eq_empty_of_ssubset_singleton _

/-! ### Lemmas about complement -/

lemma compl_def (s : set α) : sᶜ = {x | x ∉ s} := rfl

lemma mem_compl (h : a ∉ s) : a ∈ sᶜ := h

lemma compl_set_of (p : α → Prop) : {a | p a}ᶜ = { a | ¬ p a } := rfl

lemma not_mem_of_mem_compl (h : x ∈ sᶜ) : x ∉ s := h

@[simp] lemma mem_compl_iff (s : set α) (x : α) : x ∈ sᶜ ↔ (x ∉ s) := iff.rfl

lemma not_mem_compl_iff : x ∉ sᶜ ↔ x ∈ s := not_not

@[simp] lemma inter_compl_self (s : set α) : s ∩ sᶜ = ∅ := inf_compl_eq_bot

@[simp] lemma compl_inter_self (s : set α) : sᶜ ∩ s = ∅ := compl_inf_eq_bot

@[simp] lemma compl_empty : (∅ : set α)ᶜ = univ := compl_bot

@[simp] lemma compl_union (s t : set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := compl_sup

lemma compl_inter (s t : set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := compl_inf

@[simp] lemma compl_univ : (univ : set α)ᶜ = ∅ := compl_top

@[simp] lemma compl_empty_iff : sᶜ = ∅ ↔ s = univ := compl_eq_bot

@[simp] lemma compl_univ_iff : sᶜ = univ ↔ s = ∅ := compl_eq_top

lemma compl_ne_univ : sᶜ ≠ univ ↔ s.nonempty := compl_univ_iff.not.trans nonempty_iff_ne_empty.symm
lemma nonempty_compl : sᶜ.nonempty ↔ s ≠ univ := (ne_univ_iff_exists_not_mem s).symm

lemma mem_compl_singleton_iff {a x : α} : x ∈ ({a} : set α)ᶜ ↔ x ≠ a := iff.rfl

lemma compl_singleton_eq (a : α) : ({a} : set α)ᶜ = {x | x ≠ a} := rfl

@[simp] lemma compl_ne_eq_singleton (a : α) : ({x | x ≠ a} : set α)ᶜ = {a} := compl_compl _

lemma union_eq_compl_compl_inter_compl (s t : set α) : s ∪ t = (sᶜ ∩ tᶜ)ᶜ :=
ext $ λ x, or_iff_not_and_not

lemma inter_eq_compl_compl_union_compl (s t : set α) : s ∩ t = (sᶜ ∪ tᶜ)ᶜ :=
ext $ λ x, and_iff_not_or_not

@[simp] lemma union_compl_self (s : set α) : s ∪ sᶜ = univ := eq_univ_iff_forall.2 $ λ x, em _

@[simp] lemma compl_union_self (s : set α) : sᶜ ∪ s = univ := by rw [union_comm, union_compl_self]

lemma compl_subset_comm : sᶜ ⊆ t ↔ tᶜ ⊆ s := @compl_le_iff_compl_le _ s _ _
lemma subset_compl_comm : s ⊆ tᶜ ↔ t ⊆ sᶜ := @le_compl_iff_le_compl _ _ _ t

@[simp] lemma compl_subset_compl : sᶜ ⊆ tᶜ ↔ t ⊆ s := @compl_le_compl_iff_le (set α) _ _ _

lemma subset_compl_iff_disjoint_left : s ⊆ tᶜ ↔ disjoint t s :=
@le_compl_iff_disjoint_left (set α) _ _ _

lemma subset_compl_iff_disjoint_right : s ⊆ tᶜ ↔ disjoint s t :=
@le_compl_iff_disjoint_right (set α) _ _ _

lemma disjoint_compl_left_iff_subset : disjoint sᶜ t ↔ t ⊆ s := disjoint_compl_left_iff
lemma disjoint_compl_right_iff_subset : disjoint s tᶜ ↔ s ⊆ t := disjoint_compl_right_iff

alias subset_compl_iff_disjoint_right ↔ _ _root_.disjoint.subset_compl_right
alias subset_compl_iff_disjoint_left ↔ _ _root_.disjoint.subset_compl_left
alias disjoint_compl_left_iff_subset ↔ _ _root_.has_subset.subset.disjoint_compl_left
alias disjoint_compl_right_iff_subset ↔ _ _root_.has_subset.subset.disjoint_compl_right

lemma subset_union_compl_iff_inter_subset {s t u : set α} : s ⊆ t ∪ uᶜ ↔ s ∩ u ⊆ t :=
(@is_compl_compl _ u _).le_sup_right_iff_inf_left_le

lemma compl_subset_iff_union : sᶜ ⊆ t ↔ s ∪ t = univ :=
iff.symm $ eq_univ_iff_forall.trans $ forall_congr $ λ a, or_iff_not_imp_left

@[simp] lemma subset_compl_singleton_iff : s ⊆ {a}ᶜ ↔ a ∉ s :=
subset_compl_comm.trans singleton_subset_iff

lemma inter_subset (a b c : set α) : a ∩ b ⊆ c ↔ a ⊆ bᶜ ∪ c :=
forall_congr $ λ x, and_imp.trans $ imp_congr_right $ λ _, imp_iff_not_or

lemma inter_compl_nonempty_iff : (s ∩ tᶜ).nonempty ↔ ¬ s ⊆ t :=
(not_subset.trans $ exists_congr $ by exact λ x, by simp [mem_compl]).symm

/-! ### Lemmas about set difference -/

lemma diff_eq (s t : set α) : s \ t = s ∩ tᶜ := rfl

@[simp] lemma mem_diff (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := iff.rfl

lemma mem_diff_of_mem (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
⟨h1, h2⟩

lemma not_mem_diff_of_mem (hx : x ∈ t) : x ∉ s \ t :=
λ h, h.2 hx

lemma mem_of_mem_diff (h : x ∈ s \ t) : x ∈ s :=
h.left

lemma not_mem_of_mem_diff (h : x ∈ s \ t) : x ∉ t :=
h.right

lemma diff_eq_compl_inter : s \ t = tᶜ ∩ s :=
by rw [diff_eq, inter_comm]

lemma nonempty_diff : (s \ t).nonempty ↔ ¬ (s ⊆ t) := inter_compl_nonempty_iff

lemma diff_subset (s t : set α) : s \ t ⊆ s := show s \ t ≤ s, from sdiff_le

lemma union_diff_cancel' {s t u : set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ (u \ s) = u :=
sup_sdiff_cancel' h₁ h₂

lemma union_diff_cancel (h : s ⊆ t) : s ∪ (t \ s) = t :=
sup_sdiff_cancel_right h

lemma union_diff_cancel_left (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
disjoint.sup_sdiff_cancel_left $ disjoint_iff_inf_le.2 h

lemma union_diff_cancel_right (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
disjoint.sup_sdiff_cancel_right $ disjoint_iff_inf_le.2 h

@[simp] lemma union_diff_left : (s ∪ t) \ s = t \ s :=
sup_sdiff_left_self

@[simp] lemma union_diff_right : (s ∪ t) \ t = s \ t :=
sup_sdiff_right_self

lemma union_diff_distrib {s t u : set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
sup_sdiff

lemma inter_diff_assoc (a b c : set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
inf_sdiff_assoc

@[simp] lemma inter_diff_self (a b : set α) : a ∩ (b \ a) = ∅ :=
inf_sdiff_self_right

@[simp] lemma inter_union_diff (s t : set α) : (s ∩ t) ∪ (s \ t) = s :=
sup_inf_sdiff s t

@[simp] lemma diff_union_inter (s t : set α) : (s \ t) ∪ (s ∩ t) = s :=
by { rw union_comm, exact sup_inf_sdiff _ _ }

@[simp] lemma inter_union_compl (s t : set α) : (s ∩ t) ∪ (s ∩ tᶜ) = s := inter_union_diff _ _

lemma diff_subset_diff {s₁ s₂ t₁ t₂ : set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
show s₁ ≤ s₂ → t₂ ≤ t₁ → s₁ \ t₁ ≤ s₂ \ t₂, from sdiff_le_sdiff

lemma diff_subset_diff_left {s₁ s₂ t : set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
sdiff_le_sdiff_right ‹s₁ ≤ s₂›

lemma diff_subset_diff_right {s t u : set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
sdiff_le_sdiff_left ‹t ≤ u›

lemma compl_eq_univ_diff (s : set α) : sᶜ = univ \ s :=
top_sdiff.symm

@[simp] lemma empty_diff (s : set α) : (∅ \ s : set α) = ∅ :=
bot_sdiff

lemma diff_eq_empty : s \ t = ∅ ↔ s ⊆ t :=
sdiff_eq_bot_iff

@[simp] lemma diff_empty : s \ ∅ = s :=
sdiff_bot

@[simp] lemma diff_univ (s : set α) : s \ univ = ∅ := diff_eq_empty.2 (subset_univ s)

lemma diff_diff {u : set α} : s \ t \ u = s \ (t ∪ u) :=
sdiff_sdiff_left

-- the following statement contains parentheses to help the reader
lemma diff_diff_comm {s t u : set α} : (s \ t) \ u = (s \ u) \ t :=
sdiff_sdiff_comm

lemma diff_subset_iff {s t u : set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
show s \ t ≤ u ↔ s ≤ t ∪ u, from sdiff_le_iff

lemma subset_diff_union (s t : set α) : s ⊆ (s \ t) ∪ t :=
show s ≤ (s \ t) ∪ t, from le_sdiff_sup

lemma diff_union_of_subset (h : t ⊆ s) :
  (s \ t) ∪ t = s :=
subset.antisymm (union_subset (diff_subset _ _) h) (subset_diff_union _ _)

@[simp] lemma diff_singleton_subset_iff : s \ {x} ⊆ t ↔ s ⊆ insert x t :=
by { rw [←union_singleton, union_comm], apply diff_subset_iff }

lemma subset_diff_singleton (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
subset_inter h $ subset_compl_comm.1 $ singleton_subset_iff.2 hx

lemma subset_insert_diff_singleton (x : α) (s : set α) : s ⊆ insert x (s \ {x}) :=
by rw [←diff_singleton_subset_iff]

lemma diff_subset_comm {s t u : set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
show s \ t ≤ u ↔ s \ u ≤ t, from sdiff_le_comm

lemma diff_inter {s t u : set α} : s \ (t ∩ u) = (s \ t) ∪ (s \ u) :=
sdiff_inf

lemma diff_inter_diff {s t u : set α} : s \ t ∩ (s \ u) = s \ (t ∪ u) :=
sdiff_sup.symm

lemma diff_compl : s \ tᶜ = s ∩ t := sdiff_compl

lemma diff_diff_right {s t u : set α} : s \ (t \ u) = (s \ t) ∪ (s ∩ u) :=
sdiff_sdiff_right'

@[simp] lemma insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t :=
by { ext, split; simp [or_imp_distrib, h] {contextual := tt} }

lemma insert_diff_of_not_mem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) :=
begin
  classical,
  ext x,
  by_cases h' : x ∈ t,
  { have : x ≠ a,
    { assume H,
      rw H at h',
      exact h h' },
    simp [h, h', this] },
  { simp [h, h'] }
end

lemma insert_diff_self_of_not_mem (h : a ∉ s) :
  insert a s \ {a} = s :=
by { ext, simp [and_iff_left_of_imp (λ hx : x ∈ s, show x ≠ a, from λ hxa, h $ hxa ▸ hx)] }

@[simp] lemma insert_diff_eq_singleton (h : a ∉ s) :
  insert a s \ s = {a} :=
begin
  ext,
  rw [set.mem_diff, set.mem_insert_iff, set.mem_singleton_iff, or_and_distrib_right,
    and_not_self, or_false, and_iff_left_iff_imp],
  rintro rfl,
  exact h,
end

lemma inter_insert_of_mem (h : a ∈ s) : s ∩ insert a t = insert a (s ∩ t) :=
by rw [insert_inter_distrib, insert_eq_of_mem h]

lemma insert_inter_of_mem (h : a ∈ t) : insert a s ∩ t = insert a (s ∩ t) :=
by rw [insert_inter_distrib, insert_eq_of_mem h]

lemma inter_insert_of_not_mem (h : a ∉ s) : s ∩ insert a t = s ∩ t :=
ext $ λ x, and_congr_right $ λ hx, or_iff_right $ ne_of_mem_of_not_mem hx h

lemma insert_inter_of_not_mem (h : a ∉ t) : insert a s ∩ t = s ∩ t :=
ext $ λ x, and_congr_left $ λ hx, or_iff_right $ ne_of_mem_of_not_mem hx h

@[simp] lemma union_diff_self : s ∪ (t \ s) = s ∪ t := sup_sdiff_self _ _
@[simp] lemma diff_union_self : (s \ t) ∪ t = s ∪ t := sdiff_sup_self _ _

@[simp] lemma diff_inter_self : (b \ a) ∩ a = ∅ :=
inf_sdiff_self_left

@[simp] lemma diff_inter_self_eq_diff : s \ (t ∩ s) = s \ t :=
sdiff_inf_self_right _ _

@[simp] lemma diff_self_inter : s \ (s ∩ t) = s \ t := sdiff_inf_self_left _ _

@[simp] lemma diff_eq_self : s \ t = s ↔ t ∩ s ⊆ ∅ :=
show s \ t = s ↔ t ⊓ s ≤ ⊥, from sdiff_eq_self_iff_disjoint.trans disjoint_iff_inf_le

@[simp] lemma diff_singleton_eq_self (h : a ∉ s) : s \ {a} = s :=
diff_eq_self.2 $ by simp [singleton_inter_eq_empty.2 h]

@[simp] lemma insert_diff_singleton :
  insert a (s \ {a}) = insert a s :=
by simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

@[simp] lemma diff_self : s \ s = ∅ := sdiff_self

lemma diff_diff_right_self (s t : set α)  : s \ (s \ t) = s ∩ t := sdiff_sdiff_right_self

lemma diff_diff_cancel_left (h : s ⊆ t) : t \ (t \ s) = s :=
sdiff_sdiff_eq_self h

lemma mem_diff_singleton {x y : α} : x ∈ s \ {y} ↔ (x ∈ s ∧ x ≠ y) :=
iff.rfl

lemma mem_diff_singleton_empty {t : set (set α)} : s ∈ t \ {∅} ↔ s ∈ t ∧ s.nonempty :=
mem_diff_singleton.trans $ and_congr_right' nonempty_iff_ne_empty.symm

lemma union_eq_diff_union_diff_union_inter (s t : set α) :
  s ∪ t = (s \ t) ∪ (t \ s) ∪ (s ∩ t) :=
sup_eq_sdiff_sup_sdiff_sup_inf

/-! ### Symmetric difference -/

lemma mem_symm_diff : a ∈ s ∆ t ↔ a ∈ s ∧ a ∉ t ∨ a ∈ t ∧ a ∉ s := iff.rfl

protected lemma symm_diff_def (s t : set α) : s ∆ t = s \ t ∪ t \ s := rfl

lemma symm_diff_subset_union : s ∆ t ⊆ s ∪ t := @symm_diff_le_sup (set α) _ _ _

@[simp] lemma symm_diff_eq_empty : s ∆ t = ∅ ↔ s = t := symm_diff_eq_bot

@[simp] lemma symm_diff_nonempty : (s ∆ t).nonempty ↔ s ≠ t :=
nonempty_iff_ne_empty.trans symm_diff_eq_empty.not

lemma inter_symm_diff_distrib_left (s t u : set α) : s ∩ t ∆ u = (s ∩ t) ∆ (s ∩ u) :=
inf_symm_diff_distrib_left _ _ _

lemma inter_symm_diff_distrib_right (s t u : set α) : s ∆ t ∩ u = (s ∩ u) ∆ (t ∩ u) :=
inf_symm_diff_distrib_right _ _ _

lemma subset_symm_diff_union_symm_diff_left (h : disjoint s t) : u ⊆ s ∆ u ∪ t ∆ u :=
h.le_symm_diff_sup_symm_diff_left

lemma subset_symm_diff_union_symm_diff_right (h : disjoint t u) : s ⊆ s ∆ t ∪ s ∆ u :=
h.le_symm_diff_sup_symm_diff_right

/-! ### Powerset -/

/-- `𝒫 s = set.powerset s` is the set of all subsets of `s`. -/
def powerset (s : set α) : set (set α) := {t | t ⊆ s}

prefix `𝒫`:100 := powerset

lemma mem_powerset {x s : set α} (h : x ⊆ s) : x ∈ 𝒫 s := h

lemma subset_of_mem_powerset {x s : set α} (h : x ∈ 𝒫 s) : x ⊆ s := h

@[simp] lemma mem_powerset_iff (x s : set α) : x ∈ 𝒫 s ↔ x ⊆ s := iff.rfl

lemma powerset_inter (s t : set α) : 𝒫 (s ∩ t) = 𝒫 s ∩ 𝒫 t :=
ext $ λ u, subset_inter_iff

@[simp] lemma powerset_mono : 𝒫 s ⊆ 𝒫 t ↔ s ⊆ t :=
⟨λ h, h (subset.refl s), λ h u hu, subset.trans hu h⟩

lemma monotone_powerset : monotone (powerset : set α → set (set α)) :=
λ s t, powerset_mono.2

@[simp] lemma powerset_nonempty : (𝒫 s).nonempty :=
⟨∅, empty_subset s⟩

@[simp] lemma powerset_empty : 𝒫 (∅ : set α) = {∅} :=
ext $ λ s, subset_empty_iff

@[simp] lemma powerset_univ : 𝒫 (univ : set α) = univ :=
eq_univ_of_forall subset_univ

/-! ### Sets defined as an if-then-else -/

lemma mem_dite_univ_right (p : Prop) [decidable p] (t : p → set α) (x : α) :
  (x ∈ if h : p then t h else univ) ↔ (∀ h : p, x ∈ t h) :=
by split_ifs; simp [h]

@[simp] lemma mem_ite_univ_right (p : Prop) [decidable p] (t : set α) (x : α) :
  x ∈ ite p t set.univ ↔ (p → x ∈ t) :=
mem_dite_univ_right p (λ _, t) x

lemma mem_dite_univ_left (p : Prop) [decidable p] (t : ¬ p → set α) (x : α) :
  (x ∈ if h : p then univ else t h) ↔ (∀ h : ¬ p, x ∈ t h)  :=
by split_ifs; simp [h]

@[simp] lemma mem_ite_univ_left (p : Prop) [decidable p] (t : set α) (x : α) :
  x ∈ ite p set.univ t ↔ (¬ p → x ∈ t) :=
mem_dite_univ_left p (λ _, t) x

lemma mem_dite_empty_right (p : Prop) [decidable p] (t : p → set α) (x : α) :
  (x ∈ if h : p then t h else ∅) ↔ (∃ h : p, x ∈ t h) :=
by split_ifs; simp [h]

@[simp] lemma mem_ite_empty_right (p : Prop) [decidable p] (t : set α) (x : α) :
  x ∈ ite p t ∅ ↔ p ∧ x ∈ t :=
by split_ifs; simp [h]

lemma mem_dite_empty_left (p : Prop) [decidable p] (t : ¬ p → set α) (x : α) :
  (x ∈ if h : p then ∅ else t h) ↔ (∃ h : ¬ p, x ∈ t h) :=
by split_ifs; simp [h]

@[simp] lemma mem_ite_empty_left (p : Prop) [decidable p] (t : set α) (x : α) :
  x ∈ ite p ∅ t ↔ ¬ p ∧ x ∈ t :=
by split_ifs; simp [h]

/-! ### If-then-else for sets -/

/-- `ite` for sets: `set.ite t s s' ∩ t = s ∩ t`, `set.ite t s s' ∩ tᶜ = s' ∩ tᶜ`.
Defined as `s ∩ t ∪ s' \ t`. -/
protected def ite (t s s' : set α) : set α := s ∩ t ∪ s' \ t

@[simp] lemma ite_inter_self (t s s' : set α) : t.ite s s' ∩ t = s ∩ t :=
by rw [set.ite, union_inter_distrib_right, diff_inter_self, inter_assoc, inter_self, union_empty]

@[simp] lemma ite_compl (t s s' : set α) : tᶜ.ite s s' = t.ite s' s :=
by rw [set.ite, set.ite, diff_compl, union_comm, diff_eq]

@[simp] lemma ite_inter_compl_self (t s s' : set α) : t.ite s s' ∩ tᶜ = s' ∩ tᶜ :=
by rw [← ite_compl, ite_inter_self]

@[simp] lemma ite_diff_self (t s s' : set α) : t.ite s s' \ t = s' \ t :=
ite_inter_compl_self t s s'

@[simp] lemma ite_same (t s : set α) : t.ite s s = s := inter_union_diff _ _

@[simp] lemma ite_left (s t : set α) : s.ite s t = s ∪ t := by simp [set.ite]

@[simp] lemma ite_right (s t : set α) : s.ite t s = t ∩ s := by simp [set.ite]

@[simp] lemma ite_empty (s s' : set α) : set.ite ∅ s s' = s' :=
by simp [set.ite]

@[simp] lemma ite_univ (s s' : set α) : set.ite univ s s' = s :=
by simp [set.ite]

@[simp] lemma ite_empty_left (t s : set α) : t.ite ∅ s = s \ t :=
by simp [set.ite]

@[simp] lemma ite_empty_right (t s : set α) : t.ite s ∅ = s ∩ t :=
by simp [set.ite]

lemma ite_mono (t : set α) {s₁ s₁' s₂ s₂' : set α} (h : s₁ ⊆ s₂) (h' : s₁' ⊆ s₂') :
  t.ite s₁ s₁' ⊆ t.ite s₂ s₂' :=
union_subset_union (inter_subset_inter_left _ h) (inter_subset_inter_left _ h')

lemma ite_subset_union (t s s' : set α) : t.ite s s' ⊆ s ∪ s' :=
union_subset_union (inter_subset_left _ _) (diff_subset _ _)

lemma inter_subset_ite (t s s' : set α) : s ∩ s' ⊆ t.ite s s' :=
ite_same t (s ∩ s') ▸ ite_mono _ (inter_subset_left _ _) (inter_subset_right _ _)

lemma ite_inter_inter (t s₁ s₂ s₁' s₂' : set α) :
  t.ite (s₁ ∩ s₂) (s₁' ∩ s₂') = t.ite s₁ s₁' ∩ t.ite s₂ s₂' :=
by { ext x, simp only [set.ite, set.mem_inter_iff, set.mem_diff, set.mem_union], itauto }

lemma ite_inter (t s₁ s₂ s : set α) :
  t.ite (s₁ ∩ s) (s₂ ∩ s) = t.ite s₁ s₂ ∩ s :=
by rw [ite_inter_inter, ite_same]

lemma ite_inter_of_inter_eq (t : set α) {s₁ s₂ s : set α} (h : s₁ ∩ s = s₂ ∩ s) :
  t.ite s₁ s₂ ∩ s = s₁ ∩ s :=
by rw [← ite_inter, ← h, ite_same]

lemma subset_ite {t s s' u : set α} : u ⊆ t.ite s s' ↔ u ∩ t ⊆ s ∧ u \ t ⊆ s' :=
begin
  simp only [subset_def, ← forall_and_distrib],
  refine forall_congr (λ x, _),
  by_cases hx : x ∈ t; simp [*, set.ite]
end

/-! ### Subsingleton -/

/-- A set `s` is a `subsingleton` if it has at most one element. -/
protected def subsingleton (s : set α) : Prop :=
∀ ⦃x⦄ (hx : x ∈ s) ⦃y⦄ (hy : y ∈ s), x = y

lemma subsingleton.anti (ht : t.subsingleton) (hst : s ⊆ t) : s.subsingleton :=
λ x hx y hy, ht (hst hx) (hst hy)

lemma subsingleton.eq_singleton_of_mem (hs : s.subsingleton) {x:α} (hx : x ∈ s) : s = {x} :=
ext $ λ y, ⟨λ hy, (hs hx hy) ▸ mem_singleton _, λ hy, (eq_of_mem_singleton hy).symm ▸ hx⟩

@[simp] lemma subsingleton_empty : (∅ : set α).subsingleton := λ x, false.elim

@[simp] lemma subsingleton_singleton {a} : ({a} : set α).subsingleton :=
λ x hx y hy, (eq_of_mem_singleton hx).symm ▸ (eq_of_mem_singleton hy).symm ▸ rfl

lemma subsingleton_of_subset_singleton (h : s ⊆ {a}) : s.subsingleton :=
subsingleton_singleton.anti h

lemma subsingleton_of_forall_eq (a : α) (h : ∀ b ∈ s, b = a) : s.subsingleton :=
λ b hb c hc, (h _ hb).trans (h _ hc).symm

lemma subsingleton_iff_singleton {x} (hx : x ∈ s) : s.subsingleton ↔ s = {x} :=
⟨λ h, h.eq_singleton_of_mem hx, λ h,h.symm ▸ subsingleton_singleton⟩

lemma subsingleton.eq_empty_or_singleton (hs : s.subsingleton) :
  s = ∅ ∨ ∃ x, s = {x} :=
s.eq_empty_or_nonempty.elim or.inl (λ ⟨x, hx⟩, or.inr ⟨x, hs.eq_singleton_of_mem hx⟩)

lemma subsingleton.induction_on {p : set α → Prop} (hs : s.subsingleton) (he : p ∅)
  (h₁ : ∀ x, p {x}) : p s :=
by { rcases hs.eq_empty_or_singleton with rfl|⟨x, rfl⟩, exacts [he, h₁ _] }

lemma subsingleton_univ [subsingleton α] : (univ : set α).subsingleton :=
λ x hx y hy, subsingleton.elim x y

lemma subsingleton_of_univ_subsingleton (h : (univ : set α).subsingleton) : subsingleton α :=
⟨λ a b, h (mem_univ a) (mem_univ b)⟩

@[simp] lemma subsingleton_univ_iff : (univ : set α).subsingleton ↔ subsingleton α :=
⟨subsingleton_of_univ_subsingleton, λ h, @subsingleton_univ _ h⟩

lemma subsingleton_of_subsingleton [subsingleton α] : set.subsingleton s :=
subsingleton_univ.anti (subset_univ s)

lemma subsingleton_is_top (α : Type*) [partial_order α] : set.subsingleton {x : α | is_top x} :=
λ x hx y hy, hx.is_max.eq_of_le (hy x)

lemma subsingleton_is_bot (α : Type*) [partial_order α] : set.subsingleton {x : α | is_bot x} :=
λ x hx y hy, hx.is_min.eq_of_ge (hy x)

lemma exists_eq_singleton_iff_nonempty_subsingleton :
  (∃ a : α, s = {a}) ↔ s.nonempty ∧ s.subsingleton :=
begin
  refine ⟨_, λ h, _⟩,
  { rintros ⟨a, rfl⟩,
    exact ⟨singleton_nonempty a, subsingleton_singleton⟩ },
  { exact h.2.eq_empty_or_singleton.resolve_left h.1.ne_empty },
end

/-- `s`, coerced to a type, is a subsingleton type if and only if `s` is a subsingleton set. -/
@[simp, norm_cast] lemma subsingleton_coe (s : set α) : subsingleton s ↔ s.subsingleton :=
begin
  split,
  { refine λ h, (λ a ha b hb, _),
    exact set_coe.ext_iff.2 (@subsingleton.elim s h ⟨a, ha⟩ ⟨b, hb⟩) },
  { exact λ h, subsingleton.intro (λ a b, set_coe.ext (h a.property b.property)) }
end

lemma subsingleton.coe_sort : s.subsingleton → subsingleton s := s.subsingleton_coe.2

/-- The `coe_sort` of a set `s` in a subsingleton type is a subsingleton.
For the corresponding result for `subtype`, see `subtype.subsingleton`. -/
instance subsingleton_coe_of_subsingleton [subsingleton α] : subsingleton s :=
by { rw [s.subsingleton_coe], exact subsingleton_of_subsingleton }

/-- The image of a subsingleton is a subsingleton. -/
lemma subsingleton.image (hs : s.subsingleton) (f : α → β) : (f '' s).subsingleton :=
λ _ ⟨x, hx, Hx⟩ _ ⟨y, hy, Hy⟩, Hx ▸ Hy ▸ congr_arg f (hs hx hy)

/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
lemma subsingleton.preimage {s : set β} (hs : s.subsingleton) {f : α → β}
  (hf : injective f) : (f ⁻¹' s).subsingleton := λ a ha b hb, hf $ hs ha hb

/-- If the image of a set under an injective map is a subsingleton, the set is a subsingleton. -/
lemma subsingleton_of_image {α β : Type*} {f : α → β} (hf : injective f)
  (s : set α) (hs : (f '' s).subsingleton) : s.subsingleton :=
(hs.preimage hf).anti $ subset_preimage_image _ _

/-- If the preimage of a set under an surjective map is a subsingleton,
the set is a subsingleton. -/
lemma subsingleton_of_preimage {α β : Type*} {f : α → β} (hf : surjective f)
  (s : set β) (hs : (f ⁻¹' s).subsingleton) : s.subsingleton :=
λ fx hx fy hy, by { rcases ⟨hf fx, hf fy⟩ with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩, exact congr_arg f (hs hx hy) }

/-! ### Nontrivial -/

/-- A set `s` is `nontrivial` if it has at least two distinct elements. -/
protected def nontrivial (s : set α) : Prop := ∃ x y ∈ s, x ≠ y

lemma nontrivial_of_mem_mem_ne {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x ≠ y) : s.nontrivial :=
⟨x, hx, y, hy, hxy⟩

/-- Extract witnesses from s.nontrivial. This function might be used instead of case analysis on the
argument. Note that it makes a proof depend on the classical.choice axiom. -/
protected noncomputable def nontrivial.some (hs : s.nontrivial) : α × α :=
(hs.some, hs.some_spec.some_spec.some)

protected lemma nontrivial.some_fst_mem (hs : s.nontrivial) : hs.some.fst ∈ s := hs.some_spec.some

protected lemma nontrivial.some_snd_mem (hs : s.nontrivial) : hs.some.snd ∈ s :=
hs.some_spec.some_spec.some_spec.some

protected lemma nontrivial.some_fst_ne_some_snd (hs : s.nontrivial) : hs.some.fst ≠ hs.some.snd :=
hs.some_spec.some_spec.some_spec.some_spec

lemma nontrivial.mono (hs : s.nontrivial) (hst : s ⊆ t) : t.nontrivial :=
let ⟨x, hx, y, hy, hxy⟩ := hs in ⟨x, hst hx, y, hst hy, hxy⟩

lemma nontrivial_pair {x y} (hxy : x ≠ y) : ({x, y} : set α).nontrivial :=
⟨x, mem_insert _ _, y, mem_insert_of_mem _ (mem_singleton _), hxy⟩

lemma nontrivial_of_pair_subset {x y} (hxy : x ≠ y) (h : {x, y} ⊆ s) : s.nontrivial :=
(nontrivial_pair hxy).mono h

lemma nontrivial.pair_subset (hs : s.nontrivial) : ∃ x y (hab : x ≠ y), {x, y} ⊆ s :=
let ⟨x, hx, y, hy, hxy⟩ := hs in ⟨x, y, hxy, insert_subset.2 ⟨hx, (singleton_subset_iff.2 hy)⟩⟩

lemma nontrivial_iff_pair_subset : s.nontrivial ↔ ∃ x y (hxy : x ≠ y), {x, y} ⊆ s :=
⟨nontrivial.pair_subset, λ H, let ⟨x, y, hxy, h⟩ := H in nontrivial_of_pair_subset hxy h⟩

lemma nontrivial_of_exists_ne {x} (hx : x ∈ s) (h : ∃ y ∈ s, y ≠ x) : s.nontrivial :=
let ⟨y, hy, hyx⟩ := h in ⟨y, hy, x, hx, hyx⟩

lemma nontrivial.exists_ne (hs : s.nontrivial) (z) : ∃ x ∈ s, x ≠ z :=
begin
  by_contra H, push_neg at H,
  rcases hs with ⟨x, hx, y, hy, hxy⟩,
  rw [H x hx, H y hy] at hxy,
  exact hxy rfl
end

lemma nontrivial_iff_exists_ne {x} (hx : x ∈ s) : s.nontrivial ↔ ∃ y ∈ s, y ≠ x :=
⟨λ H, H.exists_ne _, nontrivial_of_exists_ne hx⟩

lemma nontrivial_of_lt [preorder α] {x y} (hx : x ∈ s) (hy : y ∈ s) (hxy : x < y) : s.nontrivial :=
⟨x, hx, y, hy, ne_of_lt hxy⟩

lemma nontrivial_of_exists_lt [preorder α] (H : ∃ x y ∈ s, x < y) : s.nontrivial :=
let ⟨x, hx, y, hy, hxy⟩ := H in nontrivial_of_lt hx hy hxy

lemma nontrivial.exists_lt [linear_order α] (hs : s.nontrivial) : ∃ x y ∈ s, x < y :=
let ⟨x, hx, y, hy, hxy⟩ := hs in
or.elim (lt_or_gt_of_ne hxy) (λ H, ⟨x, hx, y, hy, H⟩) (λ H, ⟨y, hy, x, hx, H⟩)

lemma nontrivial_iff_exists_lt [linear_order α] : s.nontrivial ↔ ∃ x y ∈ s, x < y :=
⟨nontrivial.exists_lt, nontrivial_of_exists_lt⟩

protected lemma nontrivial.nonempty (hs : s.nontrivial) : s.nonempty :=
let ⟨x, hx, _⟩ := hs in ⟨x, hx⟩

protected lemma nontrivial.ne_empty (hs : s.nontrivial) : s ≠ ∅ := hs.nonempty.ne_empty

lemma nontrivial.not_subset_empty (hs : s.nontrivial) : ¬ s ⊆ ∅ := hs.nonempty.not_subset_empty

@[simp] lemma not_nontrivial_empty : ¬ (∅ : set α).nontrivial := λ h, h.ne_empty rfl

@[simp] lemma not_nontrivial_singleton {x} : ¬ ({x} : set α).nontrivial :=
λ H, begin
  rw nontrivial_iff_exists_ne (mem_singleton x) at H,
  exact let ⟨y, hy, hya⟩ := H in hya (mem_singleton_iff.1 hy)
end

lemma nontrivial.ne_singleton {x} (hs : s.nontrivial) : s ≠ {x} :=
λ H, by { rw H at hs, exact not_nontrivial_singleton hs }

lemma nontrivial.not_subset_singleton {x} (hs : s.nontrivial) : ¬ s ⊆ {x} :=
(not_congr subset_singleton_iff_eq).2 (not_or hs.ne_empty hs.ne_singleton)

lemma nontrivial_univ [nontrivial α] : (univ : set α).nontrivial :=
let ⟨x, y, hxy⟩ := exists_pair_ne α in ⟨x, mem_univ _, y, mem_univ _, hxy⟩

lemma nontrivial_of_univ_nontrivial (h : (univ : set α).nontrivial) : nontrivial α :=
let ⟨x, _, y, _, hxy⟩ := h in ⟨⟨x, y, hxy⟩⟩

@[simp] lemma nontrivial_univ_iff : (univ : set α).nontrivial ↔ nontrivial α :=
⟨nontrivial_of_univ_nontrivial, λ h, @nontrivial_univ _ h⟩

lemma nontrivial_of_nontrivial (hs : s.nontrivial) : nontrivial α :=
let ⟨x, _, y, _, hxy⟩ := hs in ⟨⟨x, y, hxy⟩⟩

/-- `s`, coerced to a type, is a nontrivial type if and only if `s` is a nontrivial set. -/
@[simp, norm_cast] lemma nontrivial_coe_sort : nontrivial s ↔ s.nontrivial :=
by simp_rw [← nontrivial_univ_iff, set.nontrivial, mem_univ,
            exists_true_left, set_coe.exists, subtype.mk_eq_mk]

alias nontrivial_coe_sort ↔ _ nontrivial.coe_sort

/-- A type with a set `s` whose `coe_sort` is a nontrivial type is nontrivial.
For the corresponding result for `subtype`, see `subtype.nontrivial_iff_exists_ne`. -/
lemma nontrivial_of_nontrivial_coe (hs : nontrivial s) : nontrivial α :=
nontrivial_of_nontrivial $ nontrivial_coe_sort.1 hs

lemma nontrivial_mono (hst : s ⊆ t) (hs : nontrivial s) :
  nontrivial t := nontrivial.coe_sort $ (nontrivial_coe_sort.1 hs).mono hst

@[simp] lemma not_subsingleton_iff : ¬ s.subsingleton ↔ s.nontrivial :=
by simp_rw [set.subsingleton, set.nontrivial, not_forall]

@[simp] lemma not_nontrivial_iff : ¬ s.nontrivial ↔ s.subsingleton :=
iff.not_left not_subsingleton_iff.symm

alias not_nontrivial_iff ↔ _ subsingleton.not_nontrivial
alias not_subsingleton_iff ↔ _ nontrivial.not_subsingleton

lemma univ_eq_true_false : univ = ({true, false} : set Prop) :=
eq.symm $ eq_univ_of_forall $ classical.cases (by simp) (by simp)

end set

open set function

namespace subsingleton
variables [subsingleton α]

lemma eq_univ_of_nonempty : s.nonempty → s = univ :=
λ ⟨x, hx⟩, eq_univ_of_forall $ λ y, subsingleton.elim x y ▸ hx

@[elab_as_eliminator]
lemma set_cases {p : set α → Prop} (h0 : p ∅) (h1 : p univ) (s) : p s :=
s.eq_empty_or_nonempty.elim (λ h, h.symm ▸ h0) $ λ h, (eq_univ_of_nonempty h).symm ▸ h1

lemma mem_iff_nonempty [subsingleton α] :
  x ∈ s ↔ s.nonempty :=
⟨λ hx, ⟨x, hx⟩, λ ⟨y, hy⟩, subsingleton.elim y x ▸ hy⟩

end subsingleton

/-! ### Decidability instances for sets -/

namespace set
variables (s t a)

instance decidable_sdiff [decidable (a ∈ s)] [decidable (a ∈ t)] : decidable (a ∈ s \ t) :=
(by apply_instance : decidable (a ∈ s ∧ a ∉ t))

instance decidable_inter [decidable (a ∈ s)] [decidable (a ∈ t)] : decidable (a ∈ s ∩ t) :=
(by apply_instance : decidable (a ∈ s ∧ a ∈ t))

instance decidable_union [decidable (a ∈ s)] [decidable (a ∈ t)] : decidable (a ∈ s ∪ t) :=
(by apply_instance : decidable (a ∈ s ∨ a ∈ t))

instance decidable_compl [decidable (a ∈ s)] : decidable (a ∈ sᶜ) :=
(by apply_instance : decidable (a ∉ s))

instance decidable_emptyset : decidable_pred (∈ (∅ : set α)) :=
λ _, decidable.is_false (by simp)

instance decidable_univ : decidable_pred (∈ (set.univ : set α)) :=
λ _, decidable.is_true (by simp)

instance decidable_set_of (p : α → Prop) [decidable (p a)] : decidable (a ∈ {a | p a}) :=
by assumption

end set
