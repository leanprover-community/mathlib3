/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import order.symm_diff
import logic.function.iterate
import data.set.n_ary

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

/-! ### Set coercion to a type -/

open function

universes u v w x

namespace set

variables {α : Type*} {s t : set α}

instance {α : Type*} : boolean_algebra (set α) :=
{ sup := λ s t, {x | x ∈ s ∨ x ∈ t},
  le  := (≤),
  lt  := λ s t, s ⊆ t ∧ ¬t ⊆ s,
  inf := λ s t, {x | x ∈ s ∧ x ∈ t},
  bot := ∅,
  compl := λ s, {x | x ∉ s},
  top := univ,
  sdiff := λ s t, {x | x ∈ s ∧ x ∉ t},
  .. (infer_instance : boolean_algebra (α → Prop)) }

@[simp] lemma top_eq_univ : (⊤ : set α) = univ := rfl
@[simp] lemma bot_eq_empty : (⊥ : set α) = ∅ := rfl
@[simp] lemma sup_eq_union : ((⊔) : set α → set α → set α) = (∪) := rfl
@[simp] lemma inf_eq_inter : ((⊓) : set α → set α → set α) = (∩) := rfl

end set

/-- Duplicate of `eq.subset'`, which currently has elaboration problems. -/
lemma eq.subset {α} {s t : set α} : s = t → s ⊆ t := eq.subset'

namespace set

variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a b : α} {s t u : set α}

/-! ### Lemmas about union -/

@[simp] theorem union_eq_left_iff_subset {s t : set α} : s ∪ t = s ↔ t ⊆ s :=
sup_eq_left

@[simp] theorem union_eq_right_iff_subset {s t : set α} : s ∪ t = t ↔ s ⊆ t :=
sup_eq_right

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
union_eq_right_iff_subset.mpr h

theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
union_eq_left_iff_subset.mpr h

lemma union_congr_left (ht : t ⊆ s ∪ u) (hu : u ⊆ s ∪ t) : s ∪ t = s ⊔ u := sup_congr_left ht hu
lemma union_congr_right (hs : s ⊆ t ∪ u) (ht : t ⊆ s ∪ u) : s ∪ u = t ∪ u := sup_congr_right hs ht

lemma union_eq_union_iff_left : s ∪ t = s ∪ u ↔ t ⊆ s ∪ u ∧ u ⊆ s ∪ t := sup_eq_sup_iff_left
lemma union_eq_union_iff_right : s ∪ u = t ∪ u ↔ s ⊆ t ∪ u ∧ t ⊆ s ∪ u := sup_eq_sup_iff_right

@[simp] lemma union_univ {s : set α} : s ∪ univ = univ := sup_top_eq

@[simp] lemma univ_union {s : set α} : univ ∪ s = univ := top_sup_eq

/-! ### Lemmas about intersection -/

@[simp] theorem inter_eq_left_iff_subset {s t : set α} : s ∩ t = s ↔ s ⊆ t :=
inf_eq_left

@[simp] theorem inter_eq_right_iff_subset {s t : set α} : s ∩ t = t ↔ t ⊆ s :=
inf_eq_right

theorem inter_eq_self_of_subset_left {s t : set α} : s ⊆ t → s ∩ t = s :=
inter_eq_left_iff_subset.mpr

theorem inter_eq_self_of_subset_right {s t : set α} : t ⊆ s → s ∩ t = t :=
inter_eq_right_iff_subset.mpr

lemma inter_congr_left (ht : s ∩ u ⊆ t) (hu : s ∩ t ⊆ u) : s ∩ t = s ∩ u := inf_congr_left ht hu
lemma inter_congr_right (hs : t ∩ u ⊆ s) (ht : s ∩ u ⊆ t) : s ∩ u = t ∩ u := inf_congr_right hs ht

lemma inter_eq_inter_iff_left : s ∩ t = s ∩ u ↔ s ∩ u ⊆ t ∧ s ∩ t ⊆ u := inf_eq_inf_iff_left
lemma inter_eq_inter_iff_right : s ∩ u = t ∩ u ↔ t ∩ u ⊆ s ∧ s ∩ u ⊆ t := inf_eq_inf_iff_right

theorem union_inter_cancel_left {s t : set α} : (s ∪ t) ∩ s = s :=
inter_eq_self_of_subset_right $ subset_union_left _ _

theorem union_inter_cancel_right {s t : set α} : (s ∪ t) ∩ t = t :=
inter_eq_self_of_subset_right $ subset_union_right _ _

/-! ### Distributivity laws -/

theorem inter_distrib_left (s t u : set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
inf_sup_left
theorem inter_union_distrib_left {s t u : set α} : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
inf_sup_left

theorem inter_distrib_right (s t u : set α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
inf_sup_right
theorem union_inter_distrib_right {s t u : set α} : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
inf_sup_right

theorem union_distrib_left (s t u : set α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
sup_inf_left
theorem union_inter_distrib_left {s t u : set α} : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
sup_inf_left

theorem union_distrib_right (s t u : set α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
sup_inf_right
theorem inter_union_distrib_right {s t u : set α} : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
sup_inf_right

lemma union_union_distrib_left (s t u : set α) : s ∪ (t ∪ u) = (s ∪ t) ∪ (s ∪ u) :=
sup_sup_distrib_left _ _ _

lemma union_union_distrib_right (s t u : set α) : (s ∪ t) ∪ u = (s ∪ u) ∪ (t ∪ u) :=
sup_sup_distrib_right _ _ _

lemma inter_inter_distrib_left (s t u : set α) : s ∩ (t ∩ u) = (s ∩ t) ∩ (s ∩ u) :=
inf_inf_distrib_left _ _ _

lemma inter_inter_distrib_right (s t u : set α) : (s ∩ t) ∩ u = (s ∩ u) ∩ (t ∩ u) :=
inf_inf_distrib_right _ _ _

lemma union_union_union_comm (s t u v : set α) : (s ∪ t) ∪ (u ∪ v) = (s ∪ u) ∪ (t ∪ v) :=
sup_sup_sup_comm _ _ _ _

lemma inter_inter_inter_comm (s t u v : set α) : (s ∩ t) ∩ (u ∩ v) = (s ∩ u) ∩ (t ∩ v) :=
inf_inf_inf_comm _ _ _ _

/-! ### Lemmas about sets defined as `{x ∈ s | p x}`. -/

section sep
variables {p q : α → Prop} {x : α}

theorem sep_eq_of_subset (h : s ⊆ t) : {x ∈ t | x ∈ s} = s :=
inter_eq_self_of_subset_right h

@[simp] lemma sep_union : {x ∈ s ∪ t | p x} = {x ∈ s | p x} ∪ {x ∈ t | p x} :=
union_inter_distrib_right

@[simp] lemma sep_inter : {x ∈ s ∩ t | p x} = {x ∈ s | p x} ∩ {x ∈ t | p x} :=
inter_inter_distrib_right s t p

@[simp] lemma sep_and : {x ∈ s | p x ∧ q x} = {x ∈ s | p x} ∩ {x ∈ s | q x} :=
inter_inter_distrib_left s p q

@[simp] lemma sep_or : {x ∈ s | p x ∨ q x} = {x ∈ s | p x} ∪ {x ∈ s | q x} :=
inter_union_distrib_left

end sep

/-! ### Disjointness -/

protected theorem disjoint_iff : disjoint s t ↔ s ∩ t ⊆ ∅ := disjoint_iff_inf_le

theorem disjoint_iff_inter_eq_empty : disjoint s t ↔ s ∩ t = ∅ :=
disjoint_iff

lemma _root_.disjoint.inter_eq : disjoint s t → s ∩ t = ∅ := disjoint.eq_bot

lemma disjoint_left : disjoint s t ↔ ∀ ⦃a⦄, a ∈ s → a ∉ t :=
disjoint_iff_inf_le.trans $ forall_congr $ λ _, not_and
lemma disjoint_right : disjoint s t ↔ ∀ ⦃a⦄, a ∈ t → a ∉ s := by rw [disjoint.comm, disjoint_left]

/-! ### Lemmas about complement -/

@[simp] theorem inter_compl_self (s : set α) : s ∩ sᶜ = ∅ := inf_compl_eq_bot

@[simp] theorem compl_inter_self (s : set α) : sᶜ ∩ s = ∅ := compl_inf_eq_bot

@[simp] theorem compl_empty : (∅ : set α)ᶜ = univ := compl_bot

@[simp] theorem compl_union (s t : set α) : (s ∪ t)ᶜ = sᶜ ∩ tᶜ := compl_sup

theorem compl_inter (s t : set α) : (s ∩ t)ᶜ = sᶜ ∪ tᶜ := compl_inf

@[simp] theorem compl_univ : (univ : set α)ᶜ = ∅ := compl_top

@[simp] lemma compl_empty_iff {s : set α} : sᶜ = ∅ ↔ s = univ := compl_eq_bot

@[simp] lemma compl_univ_iff {s : set α} : sᶜ = univ ↔ s = ∅ := compl_eq_top

lemma compl_ne_univ : sᶜ ≠ univ ↔ s.nonempty := compl_univ_iff.not.trans nonempty_iff_ne_empty.symm

@[simp] lemma compl_ne_eq_singleton (a : α) : ({x | x ≠ a} : set α)ᶜ = {a} := compl_compl _

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

theorem subset_union_compl_iff_inter_subset {s t u : set α} : s ⊆ t ∪ uᶜ ↔ s ∩ u ⊆ t :=
(@is_compl_compl _ u _).le_sup_right_iff_inf_left_le

@[simp] lemma subset_compl_singleton_iff {a : α} {s : set α} : s ⊆ {a}ᶜ ↔ a ∉ s :=
subset_compl_comm.trans singleton_subset_iff

/-! ### Lemmas about set difference -/

theorem diff_eq (s t : set α) : s \ t = s ∩ tᶜ := rfl

@[simp] theorem mem_diff {s t : set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := iff.rfl

theorem mem_diff_of_mem {s t : set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
⟨h1, h2⟩

lemma not_mem_diff_of_mem {s t : set α} {x : α} (hx : x ∈ t) : x ∉ s \ t :=
λ h, h.2 hx

theorem mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
h.left

theorem not_mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
h.right

theorem diff_eq_compl_inter {s t : set α} : s \ t = tᶜ ∩ s :=
by rw [diff_eq, inter_comm]

theorem nonempty_diff {s t : set α} : (s \ t).nonempty ↔ ¬ (s ⊆ t) := inter_compl_nonempty_iff

theorem diff_subset (s t : set α) : s \ t ⊆ s := show s \ t ≤ s, from sdiff_le

theorem union_diff_cancel' {s t u : set α} (h₁ : s ⊆ t) (h₂ : t ⊆ u) : t ∪ (u \ s) = u :=
sup_sdiff_cancel' h₁ h₂

theorem union_diff_cancel {s t : set α} (h : s ⊆ t) : s ∪ (t \ s) = t :=
sup_sdiff_cancel_right h

theorem union_diff_cancel_left {s t : set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
disjoint.sup_sdiff_cancel_left $ disjoint_iff_inf_le.2 h

theorem union_diff_cancel_right {s t : set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
disjoint.sup_sdiff_cancel_right $ disjoint_iff_inf_le.2 h

@[simp] theorem union_diff_left {s t : set α} : (s ∪ t) \ s = t \ s :=
sup_sdiff_left_self

@[simp] theorem union_diff_right {s t : set α} : (s ∪ t) \ t = s \ t :=
sup_sdiff_right_self

theorem union_diff_distrib {s t u : set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
sup_sdiff

theorem inter_diff_assoc (a b c : set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
inf_sdiff_assoc

@[simp] theorem inter_diff_self (a b : set α) : a ∩ (b \ a) = ∅ :=
inf_sdiff_self_right

@[simp] theorem inter_union_diff (s t : set α) : (s ∩ t) ∪ (s \ t) = s :=
sup_inf_sdiff s t

@[simp] lemma diff_union_inter (s t : set α) : (s \ t) ∪ (s ∩ t) = s :=
by { rw union_comm, exact sup_inf_sdiff _ _ }

@[simp] theorem inter_union_compl (s t : set α) : (s ∩ t) ∪ (s ∩ tᶜ) = s := inter_union_diff _ _

theorem diff_subset_diff {s₁ s₂ t₁ t₂ : set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
show s₁ ≤ s₂ → t₂ ≤ t₁ → s₁ \ t₁ ≤ s₂ \ t₂, from sdiff_le_sdiff

theorem diff_subset_diff_left {s₁ s₂ t : set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
sdiff_le_sdiff_right ‹s₁ ≤ s₂›

theorem diff_subset_diff_right {s t u : set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
sdiff_le_sdiff_left ‹t ≤ u›

theorem compl_eq_univ_diff (s : set α) : sᶜ = univ \ s :=
top_sdiff.symm

@[simp] lemma empty_diff (s : set α) : (∅ \ s : set α) = ∅ :=
bot_sdiff

theorem diff_eq_empty {s t : set α} : s \ t = ∅ ↔ s ⊆ t :=
sdiff_eq_bot_iff

@[simp] theorem diff_empty {s : set α} : s \ ∅ = s :=
sdiff_bot

@[simp] lemma diff_univ (s : set α) : s \ univ = ∅ := diff_eq_empty.2 (subset_univ s)

theorem diff_diff {u : set α} : s \ t \ u = s \ (t ∪ u) :=
sdiff_sdiff_left

-- the following statement contains parentheses to help the reader
lemma diff_diff_comm {s t u : set α} : (s \ t) \ u = (s \ u) \ t :=
sdiff_sdiff_comm

lemma diff_subset_iff {s t u : set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
show s \ t ≤ u ↔ s ≤ t ∪ u, from sdiff_le_iff

lemma subset_diff_union (s t : set α) : s ⊆ (s \ t) ∪ t :=
show s ≤ (s \ t) ∪ t, from le_sdiff_sup

lemma diff_union_of_subset {s t : set α} (h : t ⊆ s) :
  (s \ t) ∪ t = s :=
subset.antisymm (union_subset (diff_subset _ _) h) (subset_diff_union _ _)

@[simp] lemma diff_singleton_subset_iff {x : α} {s t : set α} : s \ {x} ⊆ t ↔ s ⊆ insert x t :=
by { rw [←union_singleton, union_comm], apply diff_subset_iff }

lemma subset_diff_singleton {x : α} {s t : set α} (h : s ⊆ t) (hx : x ∉ s) : s ⊆ t \ {x} :=
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

@[simp] theorem insert_diff_of_mem (s) (h : a ∈ t) : insert a s \ t = s \ t :=
by { ext, split; simp [or_imp_distrib, h] {contextual := tt} }

theorem insert_diff_of_not_mem (s) (h : a ∉ t) : insert a s \ t = insert a (s \ t) :=
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

lemma insert_diff_self_of_not_mem {a : α} {s : set α} (h : a ∉ s) :
  insert a s \ {a} = s :=
by { ext, simp [and_iff_left_of_imp (λ hx : x ∈ s, show x ≠ a, from λ hxa, h $ hxa ▸ hx)] }

@[simp] lemma insert_diff_eq_singleton {a : α} {s : set α} (h : a ∉ s) :
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

@[simp] lemma union_diff_self {s t : set α} : s ∪ (t \ s) = s ∪ t := sup_sdiff_self _ _
@[simp] lemma diff_union_self {s t : set α} : (s \ t) ∪ t = s ∪ t := sdiff_sup_self _ _

@[simp] theorem diff_inter_self {a b : set α} : (b \ a) ∩ a = ∅ :=
inf_sdiff_self_left

@[simp] theorem diff_inter_self_eq_diff {s t : set α} : s \ (t ∩ s) = s \ t :=
sdiff_inf_self_right _ _

@[simp] theorem diff_self_inter {s t : set α} : s \ (s ∩ t) = s \ t := sdiff_inf_self_left _ _

@[simp] theorem diff_eq_self {s t : set α} : s \ t = s ↔ t ∩ s ⊆ ∅ :=
show s \ t = s ↔ t ⊓ s ≤ ⊥, from sdiff_eq_self_iff_disjoint.trans disjoint_iff_inf_le

@[simp] theorem diff_singleton_eq_self {a : α} {s : set α} (h : a ∉ s) : s \ {a} = s :=
diff_eq_self.2 $ by simp [singleton_inter_eq_empty.2 h]

@[simp] theorem insert_diff_singleton {a : α} {s : set α} :
  insert a (s \ {a}) = insert a s :=
by simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

@[simp] lemma diff_self {s : set α} : s \ s = ∅ := sdiff_self

lemma diff_diff_right_self (s t : set α)  : s \ (s \ t) = s ∩ t := sdiff_sdiff_right_self

lemma diff_diff_cancel_left {s t : set α} (h : s ⊆ t) : t \ (t \ s) = s :=
sdiff_sdiff_eq_self h

lemma mem_diff_singleton {x y : α} {s : set α} : x ∈ s \ {y} ↔ (x ∈ s ∧ x ≠ y) :=
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

theorem monotone_powerset : monotone (powerset : set α → set (set α)) :=
λ s t, powerset_mono.2

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

/-! ### Inverse image -/

section preimage
variables {f : α → β} {g : β → γ}

@[simp] theorem preimage_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t := rfl

@[simp] theorem preimage_ite (f : α → β) (s t₁ t₂ : set β) :
  f ⁻¹' (s.ite t₁ t₂) = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
rfl

end preimage

/-! ### Image of a set under a function -/

section image
variables {f : α → β}

lemma preimage_compl_eq_image_compl [boolean_algebra α] (S : set α) :
  compl ⁻¹' S = compl '' S :=
set.ext (λ x, ⟨λ h, ⟨xᶜ,h, compl_compl x⟩,
  λ h, exists.elim h (λ y hy, (compl_eq_comm.mp hy.2).symm.subst hy.1)⟩)

theorem mem_compl_image [boolean_algebra α] (t : α) (S : set α) :
  t ∈ compl '' S ↔ tᶜ ∈ S :=
by simp [←preimage_compl_eq_image_compl]

theorem compl_compl_image [boolean_algebra α] (S : set α) :
  compl '' (compl '' S) = S :=
by rw [←image_comp, compl_comp_compl, image_id]

theorem image_compl_subset {f : α → β} {s : set α} (H : injective f) : f '' sᶜ ⊆ (f '' s)ᶜ :=
disjoint.subset_compl_left $ by simp [disjoint_iff_inf_le, image_inter H]

theorem image_compl_eq {f : α → β} {s : set α} (H : bijective f) : f '' sᶜ = (f '' s)ᶜ :=
subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

theorem subset_image_diff (f : α → β) (s t : set α) :
  f '' s \ f '' t ⊆ f '' (s \ t) :=
begin
  rw [diff_subset_iff, ← image_union, union_diff_self],
  exact image_subset f (subset_union_right t s)
end

lemma subset_image_symm_diff : (f '' s) ∆ (f '' t) ⊆ f '' s ∆ t :=
(union_subset_union (subset_image_diff _ _ _) $ subset_image_diff _ _ _).trans
  (image_union _ _ _).superset

theorem image_diff {f : α → β} (hf : injective f) (s t : set α) :
  f '' (s \ t) = f '' s \ f '' t :=
subset.antisymm
  (subset.trans (image_inter_subset _ _ _) $ inter_subset_inter_right _ $ image_compl_subset hf)
  (subset_image_diff f s t)

lemma image_symm_diff (hf : injective f) (s t : set α) : f '' (s ∆ t) = (f '' s) ∆ (f '' t) :=
by simp_rw [set.symm_diff_def, image_union, image_diff hf]

lemma image_diff_preimage {f : α → β} {s : set α} {t : set β} : f '' (s \ f ⁻¹' t) = f '' s \ t :=
by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]

theorem compl_image : image (compl : set α → set α) = preimage compl :=
image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {p : set α → Prop} :
  compl '' {s | p s} = {s | p sᶜ} :=
congr_fun compl_image p

end image

/-! ### Subsingleton -/

/-- The image of a subsingleton is a subsingleton. -/
lemma subsingleton.image (hs : s.subsingleton) (f : α → β) : (f '' s).subsingleton :=
λ _ ⟨x, hx, Hx⟩ _ ⟨y, hy, Hy⟩, Hx ▸ Hy ▸ congr_arg f (hs hx hy)

/-- The preimage of a subsingleton under an injective map is a subsingleton. -/
theorem subsingleton.preimage {s : set β} (hs : s.subsingleton) {f : α → β}
  (hf : function.injective f) : (f ⁻¹' s).subsingleton := λ a ha b hb, hf $ hs ha hb

/-- If the image of a set under an injective map is a subsingleton, the set is a subsingleton. -/
theorem subsingleton_of_image {α β : Type*} {f : α → β} (hf : function.injective f)
  (s : set α) (hs : (f '' s).subsingleton) : s.subsingleton :=
(hs.preimage hf).anti $ subset_preimage_image _ _

/-- If the preimage of a set under an surjective map is a subsingleton,
the set is a subsingleton. -/
theorem subsingleton_of_preimage {α β : Type*} {f : α → β} (hf : function.surjective f)
  (s : set β) (hs : (f ⁻¹' s).subsingleton) : s.subsingleton :=
λ fx hx fy hy, by { rcases ⟨hf fx, hf fy⟩ with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩, exact congr_arg f (hs hx hy) }

/-! ### Nontrivial -/

/-- If the image of a set is nontrivial, the set is nontrivial. -/
lemma nontrivial_of_image (f : α → β) (s : set α) (hs : (f '' s).nontrivial) : s.nontrivial :=
let ⟨_, ⟨x, hx, rfl⟩, _, ⟨y, hy, rfl⟩, hxy⟩ := hs in ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩

/-- If the preimage of a set under an injective map is nontrivial, the set is nontrivial. -/
lemma nontrivial_of_preimage {f : α → β} (hf : function.injective f) (s : set β)
  (hs : (f ⁻¹' s).nontrivial) : s.nontrivial :=
(hs.image hf).mono $ image_preimage_subset _ _

/-! ### Lemmas about range of a function. -/
section range
variables {f : ι → α}
open function

lemma image_preimage_eq_of_subset {f : α → β} {s : set β} (hs : s ⊆ range f) :
  f '' (f ⁻¹' s) = s :=
by rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

lemma image_preimage_eq_iff {f : α → β} {s : set β} : f '' (f ⁻¹' s) = s ↔ s ⊆ range f :=
⟨by { intro h, rw [← h], apply image_subset_range }, image_preimage_eq_of_subset⟩

lemma subset_range_iff_exists_image_eq {f : α → β} {s : set β} :
  s ⊆ range f ↔ ∃ t, f '' t = s :=
⟨λ h, ⟨_, image_preimage_eq_iff.2 h⟩, λ ⟨t, ht⟩, ht ▸ image_subset_range _ _⟩

@[simp] lemma exists_subset_range_and_iff {f : α → β} {p : set β → Prop} :
  (∃ s, s ⊆ range f ∧ p s) ↔ ∃ s, p (f '' s) :=
⟨λ ⟨s, hsf, hps⟩, ⟨f ⁻¹' s, (image_preimage_eq_of_subset hsf).symm ▸ hps⟩,
  λ ⟨s, hs⟩, ⟨f '' s, image_subset_range _ _, hs⟩⟩

lemma exists_subset_range_iff {f : α → β} {p : set β → Prop} :
  (∃ s ⊆ range f, p s) ↔ ∃ s, p (f '' s) :=
by simp only [exists_prop, exists_subset_range_and_iff]

lemma range_image (f : α → β) : range (image f) = 𝒫 (range f) :=
ext $ λ s, subset_range_iff_exists_image_eq.symm

theorem is_compl_range_inl_range_inr : is_compl (range $ @sum.inl α β) (range sum.inr) :=
is_compl.of_le
  (by { rintro y ⟨⟨x₁, rfl⟩, ⟨x₂, _⟩⟩, cc })
  (by { rintro (x|y) -; [left, right]; exact mem_range_self _ })

@[simp] theorem range_inl_union_range_inr : range (sum.inl : α → α ⊕ β) ∪ range sum.inr = univ :=
is_compl.sup_eq_top $ by exact is_compl_range_inl_range_inr

@[simp] theorem range_inl_inter_range_inr : range (sum.inl : α → α ⊕ β) ∩ range sum.inr = ∅ :=
is_compl.inf_eq_bot $ by exact is_compl_range_inl_range_inr

@[simp] theorem range_inr_union_range_inl : range (sum.inr : β → α ⊕ β) ∪ range sum.inl = univ :=
is_compl.sup_eq_top $ by exact is_compl_range_inl_range_inr.symm

@[simp] theorem range_inr_inter_range_inl : range (sum.inr : β → α ⊕ β) ∩ range sum.inl = ∅ :=
is_compl.inf_eq_bot $ by exact is_compl_range_inl_range_inr.symm

@[simp] lemma compl_range_inl : (range (sum.inl : α → α ⊕ β))ᶜ = range (sum.inr : β → α ⊕ β) :=
is_compl.compl_eq is_compl_range_inl_range_inr

@[simp] lemma compl_range_inr : (range (sum.inr : β → α ⊕ β))ᶜ = range (sum.inl : α → α ⊕ β) :=
is_compl.compl_eq is_compl_range_inl_range_inr.symm

theorem image_preimage_inl_union_image_preimage_inr (s : set (α ⊕ β)) :
  sum.inl '' (sum.inl ⁻¹' s) ∪ sum.inr '' (sum.inr ⁻¹' s) = s :=
by rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, ← inter_distrib_left,
  range_inl_union_range_inr, inter_univ]

instance can_lift (c) (p) [can_lift α β c p] :
  can_lift (set α) (set β) (('') c) (λ s, ∀ x ∈ s, p x) :=
{ prf := λ s hs, subset_range_iff_exists_image_eq.mp (λ x hx, can_lift.prf _ (hs x hx)) }

lemma image_compl_preimage {f : α → β} {s : set β} : f '' ((f ⁻¹' s)ᶜ) = range f \ s :=
by rw [compl_eq_univ_diff, image_diff_preimage, image_univ]

lemma _root_.sum.range_eq (f : α ⊕ β → γ) : range f = range (f ∘ sum.inl) ∪ range (f ∘ sum.inr) :=
ext $ λ x, sum.exists

@[simp] lemma sum.elim_range (f : α → γ) (g : β → γ) : range (sum.elim f g) = range f ∪ range g :=
sum.range_eq _

lemma range_diff_image_subset (f : α → β) (s : set α) :
  range f \ f '' s ⊆ f '' sᶜ :=
λ y ⟨⟨x, h₁⟩, h₂⟩, ⟨x, λ h, h₂ ⟨x, h, h₁⟩, h₁⟩

lemma range_diff_image {f : α → β} (H : injective f) (s : set α) :
  range f \ f '' s = f '' sᶜ :=
subset.antisymm (range_diff_image_subset f s) $ λ y ⟨x, hx, hy⟩, hy ▸
  ⟨mem_range_self _, λ ⟨x', hx', eq⟩, hx $ H eq ▸ hx'⟩

lemma is_compl_range_some_none (α : Type*) :
  is_compl (range (some : α → option α)) {none} :=
is_compl.of_le
  (λ x ⟨⟨a, ha⟩, (hn : x = none)⟩, option.some_ne_none _ (ha.trans hn))
  (λ x hx, option.cases_on x (or.inr rfl) (λ x, or.inl $ mem_range_self _))

@[simp] lemma compl_range_some (α : Type*) :
  (range (some : α → option α))ᶜ = {none} :=
(is_compl_range_some_none α).compl_eq

@[simp] lemma range_some_inter_none (α : Type*) : range (some : α → option α) ∩ {none} = ∅ :=
(is_compl_range_some_none α).inf_eq_bot

@[simp] lemma range_some_union_none (α : Type*) : range (some : α → option α) ∪ {none} = univ :=
(is_compl_range_some_none α).sup_eq_top

@[simp] lemma insert_none_range_some (α : Type*) :
  insert none (range (some : α → option α)) = univ :=
(is_compl_range_some_none α).symm.sup_eq_top

end range
end set

open set

namespace function

variables {ι : Sort*} {α : Type*} {β : Type*} {f : α → β}

lemma injective.subsingleton_image_iff (hf : injective f) {s : set α} :
  (f '' s).subsingleton ↔ s.subsingleton :=
⟨subsingleton_of_image hf s, λ h, h.image f⟩

end function
open function

namespace option

lemma injective_iff {α β} {f : option α → β} :
  injective f ↔ injective (f ∘ some) ∧ f none ∉ range (f ∘ some) :=
begin
  simp only [mem_range, not_exists, (∘)],
  refine ⟨λ hf, ⟨hf.comp (option.some_injective _), λ x, hf.ne $ option.some_ne_none _⟩, _⟩,
  rintro ⟨h_some, h_none⟩ (_|a) (_|b) hab,
  exacts [rfl, (h_none _ hab.symm).elim, (h_none _ hab).elim, congr_arg some (h_some hab)]
end

lemma range_eq {α β} (f : option α → β) : range f = insert (f none) (range (f ∘ some)) :=
set.ext $ λ y, option.exists.trans $ eq_comm.or iff.rfl

end option

lemma with_bot.range_eq {α β} (f : with_bot α → β) :
  range f = insert (f ⊥) (range (f ∘ coe : α → β)) :=
option.range_eq f

lemma with_top.range_eq {α β} (f : with_top α → β) :
  range f = insert (f ⊤) (range (f ∘ coe : α → β)) :=
option.range_eq f

/-! ### Image and preimage on subtypes -/

namespace subtype

variable {α : Type*}


lemma exists_set_subtype {t : set α} (p : set α → Prop) :
  (∃(s : set t), p (coe '' s)) ↔ ∃(s : set α), s ⊆ t ∧ p s :=
begin
  split,
  { rintro ⟨s, hs⟩, refine ⟨coe '' s, _, hs⟩,
    convert image_subset_range _ _, rw [range_coe] },
  rintro ⟨s, hs₁, hs₂⟩, refine ⟨coe ⁻¹' s, _⟩,
  rw [image_preimage_eq_of_subset], exact hs₂, rw [range_coe], exact hs₁
end

@[simp] lemma preimage_coe_compl (s : set α) : (coe : s → α) ⁻¹' sᶜ = ∅ :=
preimage_coe_eq_empty.2 (inter_compl_self s)

@[simp] lemma preimage_coe_compl' (s : set α) : (coe : sᶜ → α) ⁻¹' s = ∅ :=
preimage_coe_eq_empty.2 (compl_inter_self s)

end subtype

namespace set

/-! ### Lemmas about `inclusion`, the injection of subtypes induced by `⊆` -/

section inclusion
variables {α : Type*} {s t u : set α}

/-- `inclusion` is the "identity" function between two subsets `s` and `t`, where `s ⊆ t` -/
def inclusion (h : s ⊆ t) : s → t :=
λ x : s, (⟨x, h x.2⟩ : t)

@[simp] lemma inclusion_self (x : s) : inclusion subset.rfl x = x := by { cases x, refl }

lemma inclusion_eq_id (h : s ⊆ s) : inclusion h = id := funext inclusion_self

@[simp] lemma inclusion_mk {h : s ⊆ t} (a : α) (ha : a ∈ s) : inclusion h ⟨a, ha⟩ = ⟨a, h ha⟩ := rfl

lemma inclusion_right (h : s ⊆ t) (x : t) (m : (x : α) ∈ s) : inclusion h ⟨x, m⟩ = x :=
by { cases x, refl }

@[simp] lemma inclusion_inclusion (hst : s ⊆ t) (htu : t ⊆ u) (x : s) :
  inclusion htu (inclusion hst x) = inclusion (hst.trans htu) x :=
by { cases x, refl }

@[simp] lemma inclusion_comp_inclusion {α} {s t u : set α} (hst : s ⊆ t) (htu : t ⊆ u) :
  inclusion htu ∘ inclusion hst = inclusion (hst.trans htu) :=
funext (inclusion_inclusion hst htu)

@[simp] lemma coe_inclusion (h : s ⊆ t) (x : s) : (inclusion h x : α) = (x : α) := rfl

lemma inclusion_injective (h : s ⊆ t) : injective (inclusion h)
| ⟨_, _⟩ ⟨_, _⟩ := subtype.ext_iff_val.2 ∘ subtype.ext_iff_val.1

@[simp] lemma range_inclusion (h : s ⊆ t) : range (inclusion h) = {x : t | (x:α) ∈ s} :=
by { ext ⟨x, hx⟩, simp [inclusion] }

lemma eq_of_inclusion_surjective {s t : set α} {h : s ⊆ t}
  (h_surj : function.surjective (inclusion h)) : s = t :=
begin
  rw [← range_iff_surjective, range_inclusion, eq_univ_iff_forall] at h_surj,
  exact set.subset.antisymm h (λ x hx, h_surj ⟨x, hx⟩)
end

end inclusion

/-!
### Images of binary and ternary functions

This section is very similar to `order.filter.n_ary`, `data.finset.n_ary`, `data.option.n_ary`.
Please keep them in sync.
-/

end set

/-! ### Decidability instances for sets -/

namespace set
variables {α : Type u} (s t : set α) (a : α)

instance decidable_sdiff [decidable (a ∈ s)] [decidable (a ∈ t)] : decidable (a ∈ s \ t) :=
(by apply_instance : decidable (a ∈ s ∧ a ∉ t))

end set

/-! ### Indicator function valued in bool -/

open bool

namespace set
variables {α : Type*} (s : set α)

/-- `bool_indicator` maps `x` to `tt` if `x ∈ s`, else to `ff` -/
noncomputable def bool_indicator (x : α) :=
@ite _ (x ∈ s) (classical.prop_decidable _) tt ff

lemma mem_iff_bool_indicator (x : α) : x ∈ s ↔ s.bool_indicator x = tt :=
by { unfold bool_indicator, split_ifs ; tauto }

lemma not_mem_iff_bool_indicator (x : α) : x ∉ s ↔ s.bool_indicator x = ff :=
by { unfold bool_indicator, split_ifs ; tauto }

lemma preimage_bool_indicator_tt : s.bool_indicator ⁻¹' {tt} = s :=
ext (λ x, (s.mem_iff_bool_indicator x).symm)

lemma preimage_bool_indicator_ff : s.bool_indicator ⁻¹' {ff} = sᶜ :=
ext (λ x, (s.not_mem_iff_bool_indicator x).symm)

open_locale classical

lemma preimage_bool_indicator_eq_union (t : set bool) :
  s.bool_indicator ⁻¹' t = (if tt ∈ t then s else ∅) ∪ (if ff ∈ t then sᶜ else ∅) :=
begin
  ext x,
  dsimp [bool_indicator],
  split_ifs ; tauto
end

lemma preimage_bool_indicator (t : set bool) :
  s.bool_indicator ⁻¹' t = univ ∨ s.bool_indicator ⁻¹' t = s ∨
  s.bool_indicator ⁻¹' t = sᶜ ∨ s.bool_indicator ⁻¹' t = ∅ :=
begin
  simp only [preimage_bool_indicator_eq_union],
  split_ifs ; simp [s.union_compl_self]
end

end set
