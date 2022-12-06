/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura
-/
import order.symm_diff
import logic.function.iterate

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

/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
def preimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}

infix ` ⁻¹' `:80 := preimage

section preimage
variables {f : α → β} {g : β → γ}

@[simp] theorem preimage_empty : f ⁻¹' ∅ = ∅ := rfl

@[simp] theorem mem_preimage {s : set β} {a : α} : (a ∈ f ⁻¹' s) ↔ (f a ∈ s) := iff.rfl

lemma preimage_congr {f g : α → β} {s : set β} (h : ∀ (x : α), f x = g x) : f ⁻¹' s = g ⁻¹' s :=
by { congr' with x, apply_assumption }

theorem preimage_mono {s t : set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t :=
assume x hx, h hx

@[simp] theorem preimage_univ : f ⁻¹' univ = univ := rfl

theorem subset_preimage_univ {s : set α} : s ⊆ f ⁻¹' univ := subset_univ _

@[simp] theorem preimage_inter {s t : set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := rfl

@[simp] theorem preimage_union {s t : set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := rfl

@[simp] theorem preimage_compl {s : set β} : f ⁻¹' sᶜ = (f ⁻¹' s)ᶜ := rfl

@[simp] theorem preimage_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t := rfl

@[simp] theorem preimage_ite (f : α → β) (s t₁ t₂ : set β) :
  f ⁻¹' (s.ite t₁ t₂) = (f ⁻¹' s).ite (f ⁻¹' t₁) (f ⁻¹' t₂) :=
rfl

@[simp] theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' {a | p a} = {a | p (f a)} :=
rfl

@[simp] lemma preimage_id_eq : preimage (id : α → α) = id := rfl

theorem preimage_id {s : set α} : id ⁻¹' s = s := rfl

@[simp] theorem preimage_id' {s : set α} : (λ x, x) ⁻¹' s = s := rfl

@[simp] theorem preimage_const_of_mem {b : β} {s : set β} (h : b ∈ s) :
  (λ (x : α), b) ⁻¹' s = univ :=
eq_univ_of_forall $ λ x, h

@[simp] theorem preimage_const_of_not_mem {b : β} {s : set β} (h : b ∉ s) :
  (λ (x : α), b) ⁻¹' s = ∅ :=
eq_empty_of_subset_empty $ λ x hx, h hx

theorem preimage_const (b : β) (s : set β) [decidable (b ∈ s)] :
  (λ (x : α), b) ⁻¹' s = if b ∈ s then univ else ∅ :=
by { split_ifs with hb hb, exacts [preimage_const_of_mem hb, preimage_const_of_not_mem hb] }

theorem preimage_comp {s : set γ} : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := rfl

lemma preimage_comp_eq : preimage (g ∘ f) = preimage f ∘ preimage g := rfl

@[simp] lemma preimage_iterate_eq {f : α → α} {n : ℕ} :
  set.preimage (f^[n]) = ((set.preimage f)^[n]) :=
begin
  induction n with n ih, { simp, },
  rw [iterate_succ, iterate_succ', set.preimage_comp_eq, ih],
end

lemma preimage_preimage {g : β → γ} {f : α → β} {s : set γ} :
  f ⁻¹' (g ⁻¹' s) = (λ x, g (f x)) ⁻¹' s :=
preimage_comp.symm

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : set (subtype p)} {t : set α} :
  s = subtype.val ⁻¹' t ↔ (∀x (h : p x), (⟨x, h⟩ : subtype p) ∈ s ↔ x ∈ t) :=
⟨assume s_eq x h, by { rw [s_eq], simp },
 assume h, ext $ λ ⟨x, hx⟩, by simp [h]⟩

lemma nonempty_of_nonempty_preimage {s : set β} {f : α → β} (hf : (f ⁻¹' s).nonempty) :
  s.nonempty :=
let ⟨x, hx⟩ := hf in ⟨f x, hx⟩

lemma preimage_subtype_coe_eq_compl {α : Type*} {s u v : set α} (hsuv : s ⊆ u ∪ v)
  (H : s ∩ (u ∩ v) = ∅) : (coe : s → α) ⁻¹' u = (coe ⁻¹' v)ᶜ :=
begin
  ext ⟨x, x_in_s⟩,
  split,
  { intros x_in_u x_in_v,
    exact eq_empty_iff_forall_not_mem.mp H x ⟨x_in_s, ⟨x_in_u, x_in_v⟩⟩ },
  { intro hx,
    exact or.elim (hsuv x_in_s) id (λ hx', hx.elim hx') }
end

end preimage

/-! ### Image of a set under a function -/

section image
variables {f : α → β}

/-- The image of `s : set α` by `f : α → β`, written `f '' s`,
  is the set of `y : β` such that `f x = y` for some `x ∈ s`. -/
def image (f : α → β) (s : set α) : set β := {y | ∃ x, x ∈ s ∧ f x = y}

infix ` '' `:80 := image

theorem mem_image_iff_bex {f : α → β} {s : set α} {y : β} :
  y ∈ f '' s ↔ ∃ x (_ : x ∈ s), f x = y := bex_def.symm

@[simp] theorem mem_image (f : α → β) (s : set α) (y : β) :
  y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y := iff.rfl

lemma image_eta (f : α → β) : f '' s = (λ x, f x) '' s := rfl

theorem mem_image_of_mem (f : α → β) {x : α} {a : set α} (h : x ∈ a) : f x ∈ f '' a :=
⟨_, h, rfl⟩

theorem _root_.function.injective.mem_set_image {f : α → β} (hf : injective f) {s : set α} {a : α} :
  f a ∈ f '' s ↔ a ∈ s :=
⟨λ ⟨b, hb, eq⟩, (hf eq) ▸ hb, mem_image_of_mem f⟩

theorem ball_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ f '' s, p y) ↔ (∀ x ∈ s, p (f x)) :=
by simp

theorem ball_image_of_ball {f : α → β} {s : set α} {p : β → Prop}
  (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ f '' s, p y :=
ball_image_iff.2 h

theorem bex_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∃ y ∈ f '' s, p y) ↔ (∃ x ∈ s, p (f x)) :=
by simp

theorem mem_image_elim {f : α → β} {s : set α} {C : β → Prop} (h : ∀ (x : α), x ∈ s → C (f x)) :
 ∀{y : β}, y ∈ f '' s → C y
| ._ ⟨a, a_in, rfl⟩ := h a a_in

theorem mem_image_elim_on {f : α → β} {s : set α} {C : β → Prop} {y : β} (h_y : y ∈ f '' s)
  (h : ∀ (x : α), x ∈ s → C (f x)) : C y :=
mem_image_elim h h_y

@[congr] lemma image_congr {f g : α → β} {s : set α}
  (h : ∀a∈s, f a = g a) : f '' s = g '' s :=
by safe [ext_iff, iff_def]

/-- A common special case of `image_congr` -/
lemma image_congr' {f g : α → β} {s : set α} (h : ∀ (x : α), f x = g x) : f '' s = g '' s :=
image_congr (λx _, h x)

theorem image_comp (f : β → γ) (g : α → β) (a : set α) : (f ∘ g) '' a = f '' (g '' a) :=
subset.antisymm
  (ball_image_of_ball $ assume a ha, mem_image_of_mem _ $ mem_image_of_mem _ ha)
  (ball_image_of_ball $ ball_image_of_ball $ assume a ha, mem_image_of_mem _ ha)

/-- A variant of `image_comp`, useful for rewriting -/
lemma image_image (g : β → γ) (f : α → β) (s : set α) : g '' (f '' s) = (λ x, g (f x)) '' s :=
(image_comp g f s).symm

lemma image_comm {β'} {f : β → γ} {g : α → β} {f' : α → β'} {g' : β' → γ}
  (h_comm : ∀ a, f (g a) = g' (f' a)) :
  (s.image g).image f = (s.image f').image g' :=
by simp_rw [image_image, h_comm]

lemma _root_.function.semiconj.set_image {f : α → β} {ga : α → α} {gb : β → β}
  (h : function.semiconj f ga gb) :
  function.semiconj (image f) (image ga) (image gb) :=
λ s, image_comm h

lemma _root_.function.commute.set_image {f g : α → α} (h : function.commute f g) :
  function.commute (image f) (image g) :=
h.set_image

/-- Image is monotone with respect to `⊆`. See `set.monotone_image` for the statement in
terms of `≤`. -/
theorem image_subset {a b : set α} (f : α → β) (h : a ⊆ b) : f '' a ⊆ f '' b :=
by { simp only [subset_def, mem_image], exact λ x, λ ⟨w, h1, h2⟩, ⟨w, h h1, h2⟩ }

theorem image_union (f : α → β) (s t : set α) :
  f '' (s ∪ t) = f '' s ∪ f '' t :=
ext $ λ x, ⟨by rintro ⟨a, h|h, rfl⟩; [left, right]; exact ⟨_, h, rfl⟩,
  by rintro (⟨a, h, rfl⟩ | ⟨a, h, rfl⟩); refine ⟨_, _, rfl⟩; [left, right]; exact h⟩

@[simp] theorem image_empty (f : α → β) : f '' ∅ = ∅ := by { ext, simp }

lemma image_inter_subset (f : α → β) (s t : set α) :
  f '' (s ∩ t) ⊆ f '' s ∩ f '' t :=
subset_inter (image_subset _ $ inter_subset_left _ _) (image_subset _ $ inter_subset_right _ _)

theorem image_inter_on {f : α → β} {s t : set α} (h : ∀x∈t, ∀y∈s, f x = f y → x = y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
subset.antisymm
  (assume b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩,
    have a₂ = a₁, from h _ ha₂ _ ha₁ (by simp *),
    ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
  (image_inter_subset _ _ _)

theorem image_inter {f : α → β} {s t : set α} (H : injective f) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
image_inter_on (assume x _ y _ h, H h)

theorem image_univ_of_surjective {ι : Type*} {f : ι → β} (H : surjective f) : f '' univ = univ :=
eq_univ_of_forall $ by { simpa [image] }

@[simp] theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
by { ext, simp [image, eq_comm] }

@[simp] theorem nonempty.image_const {s : set α} (hs : s.nonempty) (a : β) : (λ _, a) '' s = {a} :=
ext $ λ x, ⟨λ ⟨y, _, h⟩, h ▸ mem_singleton _,
  λ h, (eq_of_mem_singleton h).symm ▸ hs.imp (λ y hy, ⟨hy, rfl⟩)⟩

@[simp] lemma image_eq_empty {α β} {f : α → β} {s : set α} : f '' s = ∅ ↔ s = ∅ :=
by { simp only [eq_empty_iff_forall_not_mem],
     exact ⟨λ H a ha, H _ ⟨_, ha, rfl⟩, λ H b ⟨_, ha, _⟩, H _ ha⟩ }

lemma preimage_compl_eq_image_compl [boolean_algebra α] (S : set α) :
  compl ⁻¹' S = compl '' S :=
set.ext (λ x, ⟨λ h, ⟨xᶜ,h, compl_compl x⟩,
  λ h, exists.elim h (λ y hy, (compl_eq_comm.mp hy.2).symm.subst hy.1)⟩)

theorem mem_compl_image [boolean_algebra α] (t : α) (S : set α) :
  t ∈ compl '' S ↔ tᶜ ∈ S :=
by simp [←preimage_compl_eq_image_compl]

/-- A variant of `image_id` -/
@[simp] lemma image_id' (s : set α) : (λx, x) '' s = s := by { ext, simp }

theorem image_id (s : set α) : id '' s = s := by simp

theorem compl_compl_image [boolean_algebra α] (S : set α) :
  compl '' (compl '' S) = S :=
by rw [←image_comp, compl_comp_compl, image_id]

theorem image_insert_eq {f : α → β} {a : α} {s : set α} :
  f '' (insert a s) = insert (f a) (f '' s) :=
by { ext, simp [and_or_distrib_left, exists_or_distrib, eq_comm, or_comm, and_comm] }

theorem image_pair (f : α → β) (a b : α) : f '' {a, b} = {f a, f b} :=
by simp only [image_insert_eq, image_singleton]

theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α}
  (I : left_inverse g f) (s : set α) : f '' s ⊆ g ⁻¹' s :=
λ b ⟨a, h, e⟩, e ▸ ((I a).symm ▸ h : g (f a) ∈ s)

theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α}
  (I : left_inverse g f) (s : set β) : f ⁻¹' s ⊆ g '' s :=
λ b h, ⟨f b, h, I b⟩

theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α}
  (h₁ : left_inverse g f) (h₂ : right_inverse g f) :
  image f = preimage g :=
funext $ λ s, subset.antisymm
  (image_subset_preimage_of_inverse h₁ s)
  (preimage_subset_image_of_inverse h₂ s)

theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : set α}
  (h₁ : left_inverse g f) (h₂ : right_inverse g f) :
  b ∈ f '' s ↔ g b ∈ s :=
by rw image_eq_preimage_of_inverse h₁ h₂; refl

theorem image_compl_subset {f : α → β} {s : set α} (H : injective f) : f '' sᶜ ⊆ (f '' s)ᶜ :=
disjoint.subset_compl_left $ by simp [disjoint_iff_inf_le, image_inter H]

theorem subset_image_compl {f : α → β} {s : set α} (H : surjective f) : (f '' s)ᶜ ⊆ f '' sᶜ :=
compl_subset_iff_union.2 $
by { rw ← image_union, simp [image_univ_of_surjective H] }

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

lemma nonempty.image (f : α → β) {s : set α} : s.nonempty → (f '' s).nonempty
| ⟨x, hx⟩ := ⟨f x, mem_image_of_mem f hx⟩

lemma nonempty.of_image {f : α → β} {s : set α} : (f '' s).nonempty → s.nonempty
| ⟨y, x, hx, _⟩ := ⟨x, hx⟩

@[simp] lemma nonempty_image_iff {f : α → β} {s : set α} :
  (f '' s).nonempty ↔ s.nonempty :=
⟨nonempty.of_image, λ h, h.image f⟩

lemma nonempty.preimage {s : set β} (hs : s.nonempty) {f : α → β} (hf : surjective f) :
  (f ⁻¹' s).nonempty :=
let ⟨y, hy⟩ := hs, ⟨x, hx⟩ := hf y in ⟨x, mem_preimage.2 $ hx.symm ▸ hy⟩

instance (f : α → β) (s : set α) [nonempty s] : nonempty (f '' s) :=
(set.nonempty.image f nonempty_of_nonempty_subtype).to_subtype

/-- image and preimage are a Galois connection -/
@[simp] theorem image_subset_iff {s : set α} {t : set β} {f : α → β} :
  f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
ball_image_iff

theorem image_preimage_subset (f : α → β) (s : set β) : f '' (f ⁻¹' s) ⊆ s :=
image_subset_iff.2 subset.rfl

theorem subset_preimage_image (f : α → β) (s : set α) :
  s ⊆ f ⁻¹' (f '' s) :=
λ x, mem_image_of_mem f

theorem preimage_image_eq {f : α → β} (s : set α) (h : injective f) : f ⁻¹' (f '' s) = s :=
subset.antisymm
  (λ x ⟨y, hy, e⟩, h e ▸ hy)
  (subset_preimage_image f s)

theorem image_preimage_eq {f : α → β} (s : set β) (h : surjective f) : f '' (f ⁻¹' s) = s :=
subset.antisymm
  (image_preimage_subset f s)
  (λ x hx, let ⟨y, e⟩ := h x in ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩)

lemma preimage_eq_preimage {f : β → α} (hf : surjective f) : f ⁻¹' s = f ⁻¹' t ↔ s = t :=
iff.intro
  (assume eq, by rw [← image_preimage_eq s hf, ← image_preimage_eq t hf, eq])
  (assume eq, eq ▸ rfl)

lemma image_inter_preimage (f : α → β) (s : set α) (t : set β) :
  f '' (s ∩ f ⁻¹' t) = f '' s ∩ t :=
begin
  apply subset.antisymm,
  { calc f '' (s ∩ f ⁻¹' t) ⊆ f '' s ∩ (f '' (f⁻¹' t)) : image_inter_subset _ _ _
  ... ⊆ f '' s ∩ t : inter_subset_inter_right _ (image_preimage_subset f t) },
  { rintros _ ⟨⟨x, h', rfl⟩, h⟩,
    exact ⟨x, ⟨h', h⟩, rfl⟩ }
end

lemma image_preimage_inter (f : α → β) (s : set α) (t : set β) :
  f '' (f ⁻¹' t ∩ s) = t ∩ f '' s :=
by simp only [inter_comm, image_inter_preimage]

@[simp] lemma image_inter_nonempty_iff {f : α → β} {s : set α} {t : set β} :
  (f '' s ∩ t).nonempty ↔ (s ∩ f ⁻¹' t).nonempty :=
by rw [←image_inter_preimage, nonempty_image_iff]

lemma image_diff_preimage {f : α → β} {s : set α} {t : set β} : f '' (s \ f ⁻¹' t) = f '' s \ t :=
by simp_rw [diff_eq, ← preimage_compl, image_inter_preimage]

theorem compl_image : image (compl : set α → set α) = preimage compl :=
image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {p : set α → Prop} :
  compl '' {s | p s} = {s | p sᶜ} :=
congr_fun compl_image p

theorem inter_preimage_subset (s : set α) (t : set β) (f : α → β) :
  s ∩ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∩ t) :=
λ x h, ⟨mem_image_of_mem _ h.left, h.right⟩

theorem union_preimage_subset (s : set α) (t : set β) (f : α → β) :
  s ∪ f ⁻¹' t ⊆ f ⁻¹' (f '' s ∪ t) :=
λ x h, or.elim h (λ l, or.inl $ mem_image_of_mem _ l) (λ r, or.inr r)

theorem subset_image_union (f : α → β) (s : set α) (t : set β) :
  f '' (s ∪ f ⁻¹' t) ⊆ f '' s ∪ t :=
image_subset_iff.2 (union_preimage_subset _ _ _)

lemma preimage_subset_iff {A : set α} {B : set β} {f : α → β} :
  f⁻¹' B ⊆ A ↔ (∀ a : α, f a ∈ B → a ∈ A) := iff.rfl

lemma image_eq_image {f : α → β} (hf : injective f) : f '' s = f '' t ↔ s = t :=
iff.symm $ iff.intro (assume eq, eq ▸ rfl) $ assume eq,
  by rw [← preimage_image_eq s hf, ← preimage_image_eq t hf, eq]

lemma image_subset_image_iff {f : α → β} (hf : injective f) : f '' s ⊆ f '' t ↔ s ⊆ t :=
begin
  refine (iff.symm $ iff.intro (image_subset f) $ assume h, _),
  rw [← preimage_image_eq s hf, ← preimage_image_eq t hf],
  exact preimage_mono h
end

lemma prod_quotient_preimage_eq_image [s : setoid α] (g : quotient s → β) {h : α → β}
  (Hh : h = g ∘ quotient.mk) (r : set (β × β)) :
  {x : quotient s × quotient s | (g x.1, g x.2) ∈ r} =
  (λ a : α × α, (⟦a.1⟧, ⟦a.2⟧)) '' ((λ a : α × α, (h a.1, h a.2)) ⁻¹' r) :=
Hh.symm ▸ set.ext (λ ⟨a₁, a₂⟩, ⟨quotient.induction_on₂ a₁ a₂
  (λ a₁ a₂ h, ⟨(a₁, a₂), h, rfl⟩),
  λ ⟨⟨b₁, b₂⟩, h₁, h₂⟩, show (g a₁, g a₂) ∈ r, from
  have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := prod.ext_iff.1 h₂,
    h₃.1 ▸ h₃.2 ▸ h₁⟩)

lemma exists_image_iff (f : α → β) (x : set α) (P : β → Prop) :
  (∃ (a : f '' x), P a) ↔ ∃ (a : x), P (f a) :=
⟨λ ⟨a, h⟩, ⟨⟨_, a.prop.some_spec.1⟩, a.prop.some_spec.2.symm ▸ h⟩,
  λ ⟨a, h⟩, ⟨⟨_, _, a.prop, rfl⟩, h⟩⟩

/-- Restriction of `f` to `s` factors through `s.image_factorization f : s → f '' s`. -/
def image_factorization (f : α → β) (s : set α) : s → f '' s :=
λ p, ⟨f p.1, mem_image_of_mem f p.2⟩

lemma image_factorization_eq {f : α → β} {s : set α} :
  subtype.val ∘ image_factorization f s = f ∘ subtype.val :=
funext $ λ p, rfl

lemma surjective_onto_image {f : α → β} {s : set α} :
  surjective (image_factorization f s) :=
λ ⟨_, ⟨a, ha, rfl⟩⟩, ⟨⟨a, ha⟩, rfl⟩

/-- If the only elements outside `s` are those left fixed by `σ`, then mapping by `σ` has no effect.
-/
lemma image_perm {s : set α} {σ : equiv.perm α} (hs : {a : α | σ a ≠ a} ⊆ s) : σ '' s = s :=
begin
  ext i,
  obtain hi | hi := eq_or_ne (σ i) i,
  { refine ⟨_, λ h, ⟨i, h, hi⟩⟩,
    rintro ⟨j, hj, h⟩,
    rwa σ.injective (hi.trans h.symm) },
  { refine iff_of_true ⟨σ.symm i, hs $ λ h, hi _, σ.apply_symm_apply _⟩ (hs hi),
    convert congr_arg σ h; exact (σ.apply_symm_apply _).symm }
end

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

/-- The preimage of a nontrivial set under a surjective map is nontrivial. -/
theorem nontrivial.preimage {s : set β} (hs : s.nontrivial) {f : α → β}
  (hf : function.surjective f) : (f ⁻¹' s).nontrivial :=
begin
  rcases hs with ⟨fx, hx, fy, hy, hxy⟩,
  rcases ⟨hf fx, hf fy⟩ with ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩,
  exact ⟨x, hx, y, hy, mt (congr_arg f) hxy⟩
end

/-- The image of a nontrivial set under an injective map is nontrivial. -/
theorem nontrivial.image (hs : s.nontrivial)
  {f : α → β} (hf : function.injective f) : (f '' s).nontrivial :=
let ⟨x, hx, y, hy, hxy⟩ := hs in ⟨f x, mem_image_of_mem f hx, f y, mem_image_of_mem f hy, hf.ne hxy⟩

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

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : set α := {x | ∃y, f y = x}

@[simp] theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x := iff.rfl

@[simp] theorem mem_range_self (i : ι) : f i ∈ range f := ⟨i, rfl⟩

theorem forall_range_iff {p : α → Prop} : (∀ a ∈ range f, p a) ↔ (∀ i, p (f i)) :=
by simp

theorem forall_subtype_range_iff {p : range f → Prop} :
  (∀ a : range f, p a) ↔ ∀ i, p ⟨f i, mem_range_self _⟩ :=
⟨λ H i, H _, λ H ⟨y, i, hi⟩, by { subst hi, apply H }⟩

lemma subsingleton_range {α : Sort*} [subsingleton α] (f : α → β) : (range f).subsingleton :=
forall_range_iff.2 $ λ x, forall_range_iff.2 $ λ y, congr_arg f (subsingleton.elim x y)

theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ (∃ i, p (f i)) :=
by simp

lemma exists_range_iff' {p : α → Prop} :
  (∃ a, a ∈ range f ∧ p a) ↔ ∃ i, p (f i) :=
by simpa only [exists_prop] using exists_range_iff

lemma exists_subtype_range_iff {p : range f → Prop} :
  (∃ a : range f, p a) ↔ ∃ i, p ⟨f i, mem_range_self _⟩ :=
⟨λ ⟨⟨a, i, hi⟩, ha⟩, by { subst a, exact ⟨i, ha⟩}, λ ⟨i, hi⟩, ⟨_, hi⟩⟩

theorem range_iff_surjective : range f = univ ↔ surjective f :=
eq_univ_iff_forall

alias range_iff_surjective ↔ _ _root_.function.surjective.range_eq

@[simp] theorem image_univ {f : α → β} : f '' univ = range f :=
by { ext, simp [image, range] }

theorem image_subset_range (f : α → β) (s) : f '' s ⊆ range f :=
by rw ← image_univ; exact image_subset _ (subset_univ _)

theorem mem_range_of_mem_image (f : α → β) (s) {x : β} (h : x ∈ f '' s) : x ∈ range f :=
image_subset_range f s h

lemma _root_.nat.mem_range_succ (i : ℕ) : i ∈ range nat.succ ↔ 0 < i :=
⟨by { rintros ⟨n, rfl⟩, exact nat.succ_pos n, }, λ h, ⟨_, nat.succ_pred_eq_of_pos h⟩⟩

lemma nonempty.preimage' {s : set β} (hs : s.nonempty) {f : α → β} (hf : s ⊆ set.range f) :
  (f ⁻¹' s).nonempty :=
let ⟨y, hy⟩ := hs, ⟨x, hx⟩ := hf hy in ⟨x, set.mem_preimage.2 $ hx.symm ▸ hy⟩

theorem range_comp (g : α → β) (f : ι → α) : range (g ∘ f) = g '' range f :=
subset.antisymm
  (forall_range_iff.mpr $ assume i, mem_image_of_mem g (mem_range_self _))
  (ball_image_iff.mpr $ forall_range_iff.mpr mem_range_self)

theorem range_subset_iff : range f ⊆ s ↔ ∀ y, f y ∈ s :=
forall_range_iff

theorem range_eq_iff (f : α → β) (s : set β) :
  range f = s ↔ (∀ a, f a ∈ s) ∧ ∀ b ∈ s, ∃ a, f a = b :=
by { rw ←range_subset_iff, exact le_antisymm_iff }

lemma range_comp_subset_range (f : α → β) (g : β → γ) : range (g ∘ f) ⊆ range g :=
by rw range_comp; apply image_subset_range

lemma range_nonempty_iff_nonempty : (range f).nonempty ↔ nonempty ι :=
⟨λ ⟨y, x, hxy⟩, ⟨x⟩, λ ⟨x⟩, ⟨f x, mem_range_self x⟩⟩

lemma range_nonempty [h : nonempty ι] (f : ι → α) : (range f).nonempty :=
range_nonempty_iff_nonempty.2 h

@[simp] lemma range_eq_empty_iff {f : ι → α} : range f = ∅ ↔ is_empty ι :=
by rw [← not_nonempty_iff, ← range_nonempty_iff_nonempty, not_nonempty_iff_eq_empty]

lemma range_eq_empty [is_empty ι] (f : ι → α) : range f = ∅ := range_eq_empty_iff.2 ‹_›

instance [nonempty ι] (f : ι → α) : nonempty (range f) := (range_nonempty f).to_subtype

@[simp] lemma image_union_image_compl_eq_range (f : α → β) :
  (f '' s) ∪ (f '' sᶜ) = range f :=
by rw [← image_union, ← image_univ, ← union_compl_self]

lemma insert_image_compl_eq_range (f : α → β) (x : α) :
  insert (f x) (f '' {x}ᶜ) = range f :=
begin
  ext y, rw [mem_range, mem_insert_iff, mem_image],
  split,
  { rintro (h | ⟨x', hx', h⟩),
    { exact ⟨x, h.symm⟩ },
    { exact ⟨x', h⟩ } },
  { rintro ⟨x', h⟩,
    by_cases hx : x' = x,
    { left, rw [← h, hx] },
    { right, refine ⟨_, _, h⟩, rw mem_compl_singleton_iff, exact hx } }
end

theorem image_preimage_eq_inter_range {f : α → β} {t : set β} :
  f '' (f ⁻¹' t) = t ∩ range f :=
ext $ assume x, ⟨assume ⟨x, hx, heq⟩, heq ▸ ⟨hx, mem_range_self _⟩,
  assume ⟨hx, ⟨y, h_eq⟩⟩, h_eq ▸ mem_image_of_mem f $
    show y ∈ f ⁻¹' t, by simp [preimage, h_eq, hx]⟩

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

lemma preimage_subset_preimage_iff {s t : set α} {f : β → α} (hs : s ⊆ range f) :
  f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
begin
  split,
  { intros h x hx, rcases hs hx with ⟨y, rfl⟩, exact h hx },
  intros h x, apply h
end

lemma preimage_eq_preimage' {s t : set α} {f : β → α} (hs : s ⊆ range f) (ht : t ⊆ range f) :
  f ⁻¹' s = f ⁻¹' t ↔ s = t :=
begin
  split,
  { intro h, apply subset.antisymm, rw [←preimage_subset_preimage_iff hs, h],
    rw [←preimage_subset_preimage_iff ht, h] },
  rintro rfl, refl
end

@[simp] theorem preimage_inter_range {f : α → β} {s : set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
set.ext $ λ x, and_iff_left ⟨x, rfl⟩

@[simp] theorem preimage_range_inter {f : α → β} {s : set β} : f ⁻¹' (range f ∩ s) = f ⁻¹' s :=
by rw [inter_comm, preimage_inter_range]

theorem preimage_image_preimage {f : α → β} {s : set β} :
  f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s :=
by rw [image_preimage_eq_inter_range, preimage_inter_range]

@[simp] theorem range_id : range (@id α) = univ := range_iff_surjective.2 surjective_id

@[simp] theorem range_id' : range (λ (x : α), x) = univ := range_id

@[simp] theorem _root_.prod.range_fst [nonempty β] : range (prod.fst : α × β → α) = univ :=
prod.fst_surjective.range_eq

@[simp] theorem _root_.prod.range_snd [nonempty α] : range (prod.snd : α × β → β) = univ :=
prod.snd_surjective.range_eq

@[simp] theorem range_eval {ι : Type*} {α : ι → Sort*} [Π i, nonempty (α i)] (i : ι) :
  range (eval i : (Π i, α i) → α i) = univ :=
(surjective_eval i).range_eq

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

@[simp] theorem preimage_inl_image_inr (s : set β) : sum.inl ⁻¹' (@sum.inr α β '' s) = ∅ :=
by { ext, simp }

@[simp] theorem preimage_inr_image_inl (s : set α) : sum.inr ⁻¹' (@sum.inl α β '' s) = ∅ :=
by { ext, simp }

@[simp] theorem preimage_inl_range_inr : sum.inl ⁻¹' range (sum.inr : β → α ⊕ β) = ∅ :=
by rw [← image_univ, preimage_inl_image_inr]

@[simp] theorem preimage_inr_range_inl : sum.inr ⁻¹' range (sum.inl : α → α ⊕ β) = ∅ :=
by rw [← image_univ, preimage_inr_image_inl]

@[simp] lemma compl_range_inl : (range (sum.inl : α → α ⊕ β))ᶜ = range (sum.inr : β → α ⊕ β) :=
is_compl.compl_eq is_compl_range_inl_range_inr

@[simp] lemma compl_range_inr : (range (sum.inr : β → α ⊕ β))ᶜ = range (sum.inl : α → α ⊕ β) :=
is_compl.compl_eq is_compl_range_inl_range_inr.symm

theorem image_preimage_inl_union_image_preimage_inr (s : set (α ⊕ β)) :
  sum.inl '' (sum.inl ⁻¹' s) ∪ sum.inr '' (sum.inr ⁻¹' s) = s :=
by rw [image_preimage_eq_inter_range, image_preimage_eq_inter_range, ← inter_distrib_left,
  range_inl_union_range_inr, inter_univ]

@[simp] theorem range_quot_mk (r : α → α → Prop) : range (quot.mk r) = univ :=
(surjective_quot_mk r).range_eq

@[simp] theorem range_quot_lift {r : ι → ι → Prop} (hf : ∀ x y, r x y → f x = f y) :
  range (quot.lift f hf) = range f :=
ext $ λ y, (surjective_quot_mk _).exists

@[simp] theorem range_quotient_mk [setoid α] : range (λx : α, ⟦x⟧) = univ :=
range_quot_mk _

@[simp] theorem range_quotient_lift [s : setoid ι] (hf) :
  range (quotient.lift f hf : quotient s → α) = range f :=
range_quot_lift _

@[simp] theorem range_quotient_mk' {s : setoid α} : range (quotient.mk' : α → quotient s) = univ :=
range_quot_mk _

@[simp] theorem range_quotient_lift_on' {s : setoid ι} (hf) :
  range (λ x : quotient s, quotient.lift_on' x f hf) = range f :=
range_quot_lift _

instance can_lift (c) (p) [can_lift α β c p] :
  can_lift (set α) (set β) (('') c) (λ s, ∀ x ∈ s, p x) :=
{ prf := λ s hs, subset_range_iff_exists_image_eq.mp (λ x hx, can_lift.prf _ (hs x hx)) }

lemma range_const_subset {c : α} : range (λ x : ι, c) ⊆ {c} :=
range_subset_iff.2 $ λ x, rfl

@[simp] lemma range_const : ∀ [nonempty ι] {c : α}, range (λx:ι, c) = {c}
| ⟨x⟩ c := subset.antisymm range_const_subset $
  assume y hy, (mem_singleton_iff.1 hy).symm ▸ mem_range_self x

lemma range_subtype_map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀ x, p x → q (f x)) :
  range (subtype.map f h) = coe ⁻¹' (f '' {x | p x}) :=
begin
  ext ⟨x, hx⟩,
  simp_rw [mem_preimage, mem_range, mem_image, subtype.exists, subtype.map, subtype.coe_mk,
    mem_set_of, exists_prop]
end

lemma image_swap_eq_preimage_swap : image (@prod.swap α β) = preimage prod.swap :=
image_eq_preimage_of_inverse prod.swap_left_inverse prod.swap_right_inverse

theorem preimage_singleton_nonempty {f : α → β} {y : β} :
  (f ⁻¹' {y}).nonempty ↔ y ∈ range f :=
iff.rfl

theorem preimage_singleton_eq_empty {f : α → β} {y : β} :
  f ⁻¹' {y} = ∅ ↔ y ∉ range f :=
not_nonempty_iff_eq_empty.symm.trans preimage_singleton_nonempty.not

lemma range_subset_singleton {f : ι → α} {x : α} : range f ⊆ {x} ↔ f = const ι x :=
by simp [range_subset_iff, funext_iff, mem_singleton]

lemma image_compl_preimage {f : α → β} {s : set β} : f '' ((f ⁻¹' s)ᶜ) = range f \ s :=
by rw [compl_eq_univ_diff, image_diff_preimage, image_univ]

/-- Any map `f : ι → β` factors through a map `range_factorization f : ι → range f`. -/
def range_factorization (f : ι → β) : ι → range f :=
λ i, ⟨f i, mem_range_self i⟩

lemma range_factorization_eq {f : ι → β} :
  subtype.val ∘ range_factorization f = f :=
funext $ λ i, rfl

@[simp] lemma range_factorization_coe (f : ι → β) (a : ι) :
  (range_factorization f a : β) = f a := rfl

@[simp] lemma coe_comp_range_factorization (f : ι → β) : coe ∘ range_factorization f = f := rfl

lemma surjective_onto_range : surjective (range_factorization f) :=
λ ⟨_, ⟨i, rfl⟩⟩, ⟨i, rfl⟩

lemma image_eq_range (f : α → β) (s : set α) : f '' s = range (λ(x : s), f x) :=
by { ext, split, rintro ⟨x, h1, h2⟩, exact ⟨⟨x, h1⟩, h2⟩, rintro ⟨⟨x, h1⟩, h2⟩, exact ⟨x, h1, h2⟩ }

lemma _root_.sum.range_eq (f : α ⊕ β → γ) : range f = range (f ∘ sum.inl) ∪ range (f ∘ sum.inr) :=
ext $ λ x, sum.exists

@[simp] lemma sum.elim_range (f : α → γ) (g : β → γ) : range (sum.elim f g) = range f ∪ range g :=
sum.range_eq _

lemma range_ite_subset' {p : Prop} [decidable p] {f g : α → β} :
  range (if p then f else g) ⊆ range f ∪ range g :=
begin
  by_cases h : p, {rw if_pos h, exact subset_union_left _ _},
  {rw if_neg h, exact subset_union_right _ _}
end

lemma range_ite_subset {p : α → Prop} [decidable_pred p] {f g : α → β} :
  range (λ x, if p x then f x else g x) ⊆ range f ∪ range g :=
begin
  rw range_subset_iff, intro x, by_cases h : p x,
  simp [if_pos h, mem_union, mem_range_self],
  simp [if_neg h, mem_union, mem_range_self]
end

@[simp] lemma preimage_range (f : α → β) : f ⁻¹' (range f) = univ :=
eq_univ_of_forall mem_range_self

/-- The range of a function from a `unique` type contains just the
function applied to its single value. -/
lemma range_unique [h : unique ι] : range f = {f default} :=
begin
  ext x,
  rw mem_range,
  split,
  { rintros ⟨i, hi⟩,
    rw h.uniq i at hi,
    exact hi ▸ mem_singleton _ },
  { exact λ h, ⟨default, h.symm⟩ }
end

lemma range_diff_image_subset (f : α → β) (s : set α) :
  range f \ f '' s ⊆ f '' sᶜ :=
λ y ⟨⟨x, h₁⟩, h₂⟩, ⟨x, λ h, h₂ ⟨x, h, h₁⟩, h₁⟩

lemma range_diff_image {f : α → β} (H : injective f) (s : set α) :
  range f \ f '' s = f '' sᶜ :=
subset.antisymm (range_diff_image_subset f s) $ λ y ⟨x, hx, hy⟩, hy ▸
  ⟨mem_range_self _, λ ⟨x', hx', eq⟩, hx $ H eq ▸ hx'⟩

/-- We can use the axiom of choice to pick a preimage for every element of `range f`. -/
noncomputable def range_splitting (f : α → β) : range f → α := λ x, x.2.some

-- This can not be a `@[simp]` lemma because the head of the left hand side is a variable.
lemma apply_range_splitting (f : α → β) (x : range f) : f (range_splitting f x) = x :=
x.2.some_spec

attribute [irreducible] range_splitting

@[simp] lemma comp_range_splitting (f : α → β) : f ∘ range_splitting f = coe :=
by { ext, simp only [function.comp_app], apply apply_range_splitting, }

-- When `f` is injective, see also `equiv.of_injective`.
lemma left_inverse_range_splitting (f : α → β) :
  left_inverse (range_factorization f) (range_splitting f) :=
λ x, by { ext, simp only [range_factorization_coe], apply apply_range_splitting, }

lemma range_splitting_injective (f : α → β) : injective (range_splitting f) :=
(left_inverse_range_splitting f).injective

lemma right_inverse_range_splitting {f : α → β} (h : injective f) :
  right_inverse (range_factorization f) (range_splitting f) :=
(left_inverse_range_splitting f).right_inverse_of_injective $
  λ x y hxy, h $ subtype.ext_iff.1 hxy

lemma preimage_range_splitting {f : α → β} (hf : injective f) :
  preimage (range_splitting f) = image (range_factorization f) :=
(image_eq_preimage_of_inverse (right_inverse_range_splitting hf)
  (left_inverse_range_splitting f)).symm

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

lemma surjective.preimage_injective (hf : surjective f) : injective (preimage f) :=
assume s t, (preimage_eq_preimage hf).1

lemma injective.preimage_image (hf : injective f) (s : set α) : f ⁻¹' (f '' s) = s :=
preimage_image_eq s hf

lemma injective.preimage_surjective (hf : injective f) : surjective (preimage f) :=
by { intro s, use f '' s, rw hf.preimage_image }

lemma injective.subsingleton_image_iff (hf : injective f) {s : set α} :
  (f '' s).subsingleton ↔ s.subsingleton :=
⟨subsingleton_of_image hf s, λ h, h.image f⟩

lemma surjective.image_preimage (hf : surjective f) (s : set β) : f '' (f ⁻¹' s) = s :=
image_preimage_eq s hf

lemma surjective.image_surjective (hf : surjective f) : surjective (image f) :=
by { intro s, use f ⁻¹' s, rw hf.image_preimage }

lemma surjective.nonempty_preimage (hf : surjective f) {s : set β} :
  (f ⁻¹' s).nonempty ↔ s.nonempty :=
by rw [← nonempty_image_iff, hf.image_preimage]

lemma injective.image_injective (hf : injective f) : injective (image f) :=
by { intros s t h, rw [←preimage_image_eq s hf, ←preimage_image_eq t hf, h] }

lemma surjective.preimage_subset_preimage_iff {s t : set β} (hf : surjective f) :
  f ⁻¹' s ⊆ f ⁻¹' t ↔ s ⊆ t :=
by { apply preimage_subset_preimage_iff, rw [hf.range_eq], apply subset_univ }

lemma surjective.range_comp {ι' : Sort*} {f : ι → ι'} (hf : surjective f) (g : ι' → α) :
  range (g ∘ f) = range g :=
ext $ λ y, (@surjective.exists _ _ _ hf (λ x, g x = y)).symm

lemma injective.nonempty_apply_iff {f : set α → set β} (hf : injective f)
  (h2 : f ∅ = ∅) {s : set α} : (f s).nonempty ↔ s.nonempty :=
by rw [nonempty_iff_ne_empty, ← h2, nonempty_iff_ne_empty, hf.ne_iff]

lemma injective.mem_range_iff_exists_unique (hf : injective f) {b : β} :
  b ∈ range f ↔ ∃! a, f a = b :=
⟨λ ⟨a, h⟩, ⟨a, h, λ a' ha, hf (ha.trans h.symm)⟩, exists_unique.exists⟩

lemma injective.exists_unique_of_mem_range (hf : injective f) {b : β} (hb : b ∈ range f) :
  ∃! a, f a = b :=
hf.mem_range_iff_exists_unique.mp hb

theorem injective.compl_image_eq (hf : injective f) (s : set α) :
  (f '' s)ᶜ = f '' sᶜ ∪ (range f)ᶜ :=
begin
  ext y,
  rcases em (y ∈ range f) with ⟨x, rfl⟩|hx,
  { simp [hf.eq_iff] },
  { rw [mem_range, not_exists] at hx,
    simp [hx] }
end

lemma left_inverse.image_image {g : β → α} (h : left_inverse g f) (s : set α) :
  g '' (f '' s) = s :=
by rw [← image_comp, h.comp_eq_id, image_id]

lemma left_inverse.preimage_preimage {g : β → α} (h : left_inverse g f) (s : set α) :
  f ⁻¹' (g ⁻¹' s) = s :=
by rw [← preimage_comp, h.comp_eq_id, preimage_id]

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

lemma coe_image {p : α → Prop} {s : set (subtype p)} :
  coe '' s = {x | ∃h : p x, (⟨x, h⟩ : subtype p) ∈ s} :=
set.ext $ assume a,
⟨assume ⟨⟨a', ha'⟩, in_s, h_eq⟩, h_eq ▸ ⟨ha', in_s⟩,
  assume ⟨ha, in_s⟩, ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp] lemma coe_image_of_subset {s t : set α} (h : t ⊆ s) : coe '' {x : ↥s | ↑x ∈ t} = t :=
begin
  ext x,
  rw set.mem_image,
  exact ⟨λ ⟨x', hx', hx⟩, hx ▸ hx', λ hx, ⟨⟨x, h hx⟩, hx, rfl⟩⟩,
end

lemma range_coe {s : set α} :
  range (coe : s → α) = s :=
by { rw ← set.image_univ, simp [-set.image_univ, coe_image] }

/-- A variant of `range_coe`. Try to use `range_coe` if possible.
  This version is useful when defining a new type that is defined as the subtype of something.
  In that case, the coercion doesn't fire anymore. -/
lemma range_val {s : set α} :
  range (subtype.val : s → α) = s :=
range_coe

/-- We make this the simp lemma instead of `range_coe`. The reason is that if we write
  for `s : set α` the function `coe : s → α`, then the inferred implicit arguments of `coe` are
  `coe α (λ x, x ∈ s)`. -/
@[simp] lemma range_coe_subtype {p : α → Prop} :
  range (coe : subtype p → α) = {x | p x} :=
range_coe

@[simp] lemma coe_preimage_self (s : set α) : (coe : s → α) ⁻¹' s = univ :=
by rw [← preimage_range (coe : s → α), range_coe]

lemma range_val_subtype {p : α → Prop} :
  range (subtype.val : subtype p → α) = {x | p x} :=
range_coe

theorem coe_image_subset (s : set α) (t : set s) : coe '' t ⊆ s :=
λ x ⟨y, yt, yvaleq⟩, by rw ←yvaleq; exact y.property

theorem coe_image_univ (s : set α) : (coe : s → α) '' set.univ = s :=
image_univ.trans range_coe

@[simp] theorem image_preimage_coe (s t : set α) :
  (coe : s → α) '' (coe ⁻¹' t) = t ∩ s :=
image_preimage_eq_inter_range.trans $ congr_arg _ range_coe

theorem image_preimage_val (s t : set α) :
  (subtype.val : s → α) '' (subtype.val ⁻¹' t) = t ∩ s :=
image_preimage_coe s t

theorem preimage_coe_eq_preimage_coe_iff {s t u : set α} :
  ((coe : s → α) ⁻¹' t = coe ⁻¹' u) ↔ t ∩ s = u ∩ s :=
by rw [← image_preimage_coe, ← image_preimage_coe, coe_injective.image_injective.eq_iff]

@[simp] theorem preimage_coe_inter_self (s t : set α) :
  (coe : s → α) ⁻¹' (t ∩ s) = coe ⁻¹' t :=
by rw [preimage_coe_eq_preimage_coe_iff, inter_assoc, inter_self]

theorem preimage_val_eq_preimage_val_iff (s t u : set α) :
  ((subtype.val : s → α) ⁻¹' t = subtype.val ⁻¹' u) ↔ (t ∩ s = u ∩ s) :=
preimage_coe_eq_preimage_coe_iff

lemma exists_set_subtype {t : set α} (p : set α → Prop) :
  (∃(s : set t), p (coe '' s)) ↔ ∃(s : set α), s ⊆ t ∧ p s :=
begin
  split,
  { rintro ⟨s, hs⟩, refine ⟨coe '' s, _, hs⟩,
    convert image_subset_range _ _, rw [range_coe] },
  rintro ⟨s, hs₁, hs₂⟩, refine ⟨coe ⁻¹' s, _⟩,
  rw [image_preimage_eq_of_subset], exact hs₂, rw [range_coe], exact hs₁
end

lemma preimage_coe_nonempty {s t : set α} : ((coe : s → α) ⁻¹' t).nonempty ↔ (s ∩ t).nonempty :=
by rw [inter_comm, ← image_preimage_coe, nonempty_image_iff]

lemma preimage_coe_eq_empty {s t : set α} : (coe : s → α) ⁻¹' t = ∅ ↔ s ∩ t = ∅ :=
by simp only [← not_nonempty_iff_eq_empty, preimage_coe_nonempty]

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

/-! ### Injectivity and surjectivity lemmas for image and preimage -/
section image_preimage
variables {α : Type u} {β : Type v} {f : α → β}
@[simp]
lemma preimage_injective : injective (preimage f) ↔ surjective f :=
begin
  refine ⟨λ h y, _, surjective.preimage_injective⟩,
  obtain ⟨x, hx⟩ : (f ⁻¹' {y}).nonempty,
  { rw [h.nonempty_apply_iff preimage_empty], apply singleton_nonempty },
  exact ⟨x, hx⟩
end

@[simp]
lemma preimage_surjective : surjective (preimage f) ↔ injective f :=
begin
  refine ⟨λ h x x' hx, _, injective.preimage_surjective⟩,
  cases h {x} with s hs, have := mem_singleton x,
  rwa [← hs, mem_preimage, hx, ← mem_preimage, hs, mem_singleton_iff, eq_comm] at this
end

@[simp] lemma image_surjective : surjective (image f) ↔ surjective f :=
begin
  refine ⟨λ h y, _, surjective.image_surjective⟩,
  cases h {y} with s hs,
  have := mem_singleton y, rw [← hs] at this, rcases this with ⟨x, h1x, h2x⟩,
  exact ⟨x, h2x⟩
end

@[simp] lemma image_injective : injective (image f) ↔ injective f :=
begin
  refine ⟨λ h x x' hx, _, injective.image_injective⟩,
  rw [← singleton_eq_singleton_iff], apply h,
  rw [image_singleton, image_singleton, hx]
end

lemma preimage_eq_iff_eq_image {f : α → β} (hf : bijective f) {s t} :
  f ⁻¹' s = t ↔ s = f '' t :=
by rw [← image_eq_image hf.1, hf.2.image_preimage]

lemma eq_preimage_iff_image_eq {f : α → β} (hf : bijective f) {s t} :
  s = f ⁻¹' t ↔ f '' s = t :=
by rw [← image_eq_image hf.1, hf.2.image_preimage]

end image_preimage

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
