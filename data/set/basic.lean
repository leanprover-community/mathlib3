/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Leonardo de Moura
-/
import tactic.finish

namespace set
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

instance : inhabited (set α) := ⟨∅⟩

theorem ext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
funext (assume x, propext (h x))

theorem set_eq_def (s t : set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
⟨begin intros h x, rw h end, set.ext⟩

/- mem and set_of -/

-- TODO(Jeremy): I had to add ematch here
@[simp, ematch] theorem mem_set_of_eq {a : α} {p : α → Prop} : a ∈ {a | p a} = p a := rfl

@[simp] theorem nmem_set_of_eq {a : α} {P : α → Prop} : a ∉ {a : α | P a} = ¬ P a := rfl

/- subset -/

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl

theorem subset.refl (a : set α) : a ⊆ a := assume x, id

theorem subset.trans {a b c : set α} (subab : a ⊆ b) (subbc : b ⊆ c) : a ⊆ c :=
assume x, assume ax, subbc (subab ax)

theorem subset.antisymm {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))

-- an alterantive name
theorem eq_of_subset_of_subset {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subset.antisymm h₁ h₂

theorem mem_of_subset_of_mem {s₁ s₂ : set α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ h₂

/- strict subset -/

def strict_subset (s t : set α) := s ⊆ t ∧ s ≠ t

instance : has_ssubset (set α) := ⟨strict_subset⟩

theorem ssubset_def {s t : set α} : (s ⊂ t) = (s ⊆ t ∧ s ≠ t) := rfl

theorem not_mem_empty (x : α) : ¬ (x ∈ (∅ : set α)) :=
assume h : x ∈ ∅, h

/- empty set -/

theorem empty_def : (∅ : set α) = {x | false} := rfl

@[simp] theorem mem_empty_eq (x : α) : x ∈ (∅ : set α) = false :=
rfl

@[simp] lemma set_of_false : {a : α | false} = ∅ := rfl

theorem eq_empty_of_forall_not_mem {s : set α} (h : ∀ x, x ∉ s) : s = ∅ :=
ext (assume x, iff.intro
  (assume xs, absurd xs (h x))
  (assume xe, absurd xe (not_mem_empty _)))

theorem ne_empty_of_mem {s : set α} {x : α} (h : x ∈ s) : s ≠ ∅ :=
  begin intro hs, rewrite hs at h, apply not_mem_empty _ h end

@[simp] theorem empty_subset (s : set α) : ∅ ⊆ s :=
assume x, assume h, false.elim h

theorem eq_empty_of_subset_empty {s : set α} (h : s ⊆ ∅) : s = ∅ :=
subset.antisymm h (empty_subset s)

theorem exists_mem_of_ne_empty {s : set α} (h : s ≠ ∅) : ∃ x, x ∈ s :=
by finish [set_eq_def]

theorem subset_empty_iff (s : set α) : s ⊆ ∅ ↔ s = ∅ :=
by finish [set_eq_def]

theorem bounded_forall_empty_iff {p : α → Prop} :
  (∀ x ∈ (∅ : set α), p x) ↔ true :=
by finish [iff_def]

/- universal set -/

theorem univ_def : @univ α = {x | true} := rfl

theorem mem_univ (x : α) : x ∈ @univ α := trivial

theorem mem_univ_iff (x : α) : x ∈ @univ α ↔ true := iff.rfl

@[simp] theorem mem_univ_eq (x : α) : x ∈ @univ α = true := rfl

theorem empty_ne_univ [h : inhabited α] : (∅ : set α) ≠ univ :=
by finish [set_eq_def]

@[simp] theorem subset_univ (s : set α) : s ⊆ univ := λ x H, trivial

theorem eq_univ_of_univ_subset {s : set α} (h : univ ⊆ s) : s = univ :=
by finish [subset_def, set_eq_def]

theorem eq_univ_of_forall {s : set α} (H : ∀ x, x ∈ s) : s = univ :=
by finish [set_eq_def]

/- union -/

theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl

theorem mem_union_left {x : α} {a : set α} (b : set α) : x ∈ a → x ∈ a ∪ b := or.inl

theorem mem_union_right {x : α} {b : set α} (a : set α) : x ∈ b → x ∈ a ∪ b := or.inr

theorem mem_or_mem_of_mem_union {x : α} {a b : set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b := H

theorem mem_union.elim {x : α} {a b : set α} {P : Prop}
    (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
or.elim H₁ H₂ H₃

theorem mem_union_iff (x : α) (a b : set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := iff.rfl

@[simp] theorem mem_union_eq (x : α) (a b : set α) : x ∈ a ∪ b = (x ∈ a ∨ x ∈ b) := rfl

@[simp] theorem union_self (a : set α) : a ∪ a = a :=
ext (assume x, or_self _)

@[simp] theorem union_empty (a : set α) : a ∪ ∅ = a :=
ext (assume x, or_false _)

@[simp] theorem empty_union (a : set α) : ∅ ∪ a = a :=
ext (assume x, false_or _)

@[simp] theorem union_comm (a b : set α) : a ∪ b = b ∪ a :=
ext (assume x, or.comm)

@[simp] theorem union_assoc (a b c : set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
ext (assume x, or.assoc)

instance union_is_assoc : is_associative (set α) (∪) :=
⟨union_assoc⟩

instance union_is_comm : is_commutative (set α) (∪) :=
⟨union_comm⟩

@[simp] theorem union_left_comm (s₁ s₂ s₃ : set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
by finish

theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
by finish

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
by finish [subset_def, set_eq_def, iff_def]

theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by finish [subset_def, set_eq_def, iff_def]

theorem subset_union_left (s t : set α) : s ⊆ s ∪ t := λ x, or.inl

theorem subset_union_right (s t : set α) : t ⊆ s ∪ t := λ x, or.inr

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
by finish [subset_def, union_def]

theorem union_subset_iff {s t u : set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
by finish [iff_def, subset_def]

theorem union_subset_union {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∪ s₂ ⊆ t₁ ∪ t₂ :=
by finish [subset_def]

/- intersection -/

theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := rfl

theorem mem_inter_iff (x : α) (a b : set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := iff.rfl

@[simp] theorem mem_inter_eq (x : α) (a b : set α) : x ∈ a ∩ b = (x ∈ a ∧ x ∈ b) := rfl

theorem mem_inter {x : α} {a b : set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
⟨ha, hb⟩

theorem mem_of_mem_inter_left {x : α} {a b : set α} (h : x ∈ a ∩ b) : x ∈ a :=
h.left

theorem mem_of_mem_inter_right {x : α} {a b : set α} (h : x ∈ a ∩ b) : x ∈ b :=
h.right

@[simp] theorem inter_self (a : set α) : a ∩ a = a :=
ext (assume x, and_self _)

@[simp] theorem inter_empty (a : set α) : a ∩ ∅ = ∅ :=
ext (assume x, and_false _)

@[simp] theorem empty_inter (a : set α) : ∅ ∩ a = ∅ :=
ext (assume x, false_and _)

@[simp] theorem inter_comm (a b : set α) : a ∩ b = b ∩ a :=
ext (assume x, and.comm)

@[simp] theorem inter_assoc (a b c : set α) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
ext (assume x, and.assoc)

instance inter_is_assoc : is_associative (set α) (∩) :=
⟨inter_assoc⟩

instance inter_is_comm : is_commutative (set α) (∩) :=
⟨inter_comm⟩

@[simp] theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
by finish

theorem inter_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
by finish

theorem inter_subset_left (s t : set α) : s ∩ t ⊆ s := λ x H, and.left H

theorem inter_subset_right (s t : set α) : s ∩ t ⊆ t := λ x H, and.right H

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
by finish [subset_def, inter_def]

theorem inter_univ (a : set α) : a ∩ univ = a :=
ext (assume x, and_true _)

theorem univ_inter (a : set α) : univ ∩ a = a :=
ext (assume x, true_and _)

theorem inter_subset_inter_right {s t : set α} (u : set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by finish [subset_def]

theorem inter_subset_inter_left {s t : set α} (u : set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
by finish [subset_def]

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∩ s₂ ⊆ t₁ ∩ t₂ :=
by finish [subset_def]

theorem inter_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∩ t = s :=
by finish [subset_def, set_eq_def, iff_def]

theorem inter_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∩ t = t :=
by finish [subset_def, set_eq_def, iff_def]

-- TODO(Mario): remove?
theorem nonempty_of_inter_nonempty_right {T : Type} {s t : set T} (h : s ∩ t ≠ ∅) : t ≠ ∅ :=
by finish [set_eq_def, iff_def]

theorem nonempty_of_inter_nonempty_left {T : Type} {s t : set T} (h : s ∩ t ≠ ∅) : s ≠ ∅ :=
by finish [set_eq_def, iff_def]

/- distributivity laws -/

theorem inter_distrib_left (s t u : set α) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
ext (assume x, and_distrib _ _ _)

theorem inter_distrib_right (s t u : set α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext (assume x, and_distrib_right _ _ _)

theorem union_distrib_left (s t u : set α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext (assume x, or_distrib _ _ _)

theorem union_distrib_right (s t u : set α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext (assume x, or_distrib_right _ _ _)

/- insert -/

theorem insert_def (x : α) (s : set α) : insert x s = { y | y = x ∨ y ∈ s } := rfl

@[simp] theorem insert_of_has_insert (x : α) (s : set α) : has_insert.insert x s = insert x s := rfl

@[simp] theorem subset_insert (x : α) (s : set α) : s ⊆ insert x s :=
assume y ys, or.inr ys

theorem mem_insert (x : α) (s : set α) : x ∈ insert x s :=
or.inl rfl

theorem mem_insert_of_mem {x : α} {s : set α} (y : α) : x ∈ s → x ∈ insert y s := or.inr

theorem eq_or_mem_of_mem_insert {x a : α} {s : set α} : x ∈ insert a s → x = a ∨ x ∈ s := id

theorem mem_of_mem_insert_of_ne {x a : α} {s : set α} (xin : x ∈ insert a s) : x ≠ a → x ∈ s :=
by finish [insert_def]

@[simp]
theorem mem_insert_iff (x a : α) (s : set α) : x ∈ insert a s ↔ (x = a ∨ x ∈ s) := iff.rfl

@[simp]
theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by finish [set_eq_def, iff_def]

theorem ssubset_insert {s : set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
by finish [ssubset_def, set_eq_def]

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
ext (assume c, by simp)

-- TODO(Jeremy): make this automatic
theorem insert_ne_empty (a : α) (s : set α) : insert a s ≠ ∅ :=
by safe [set_eq_def, iff_def]; have h' := a_1 a; finish

-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ insert a s → P x) :
  ∀ x, x ∈ s → P x :=
by finish

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ s → P x) (ha : P a) :
  ∀ x, x ∈ insert a s → P x :=
by finish

theorem bounded_forall_insert_iff {P : α → Prop} {a : α} {s : set α} :
  (∀ x ∈ insert a s, P x) ↔ P a ∧ (∀x ∈ s, P x) :=
by finish [iff_def]

/- singletons -/

theorem singleton_def (a : α) : ({a} : set α) = insert a ∅ := rfl

@[simp] theorem mem_singleton_iff (a b : α) : a ∈ ({b} : set α) ↔ a = b :=
by finish [singleton_def]

-- TODO: again, annotation needed
@[simp] theorem mem_singleton (a : α) : a ∈ ({a} : set α) := by finish

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : set α)) : x = y :=
by finish

@[simp] theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : set α) ↔ x = y :=
by finish [set_eq_def, iff_def]

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : set α) :=
by finish

theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s :=
by finish [set_eq_def]

@[simp] theorem union_insert_eq {a : α} {s t : set α} :
  s ∪ (insert a t) = insert a (s ∪ t) :=
by simp [insert_eq]

@[simp] theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
by finish

theorem singleton_ne_empty (a : α) : ({a} : set α) ≠ ∅ := insert_ne_empty _ _

@[simp] theorem singleton_subset_iff {a : α} {s : set α} : {a} ⊆ s ↔ a ∈ s :=
⟨λh, h (by simp), λh b e, by simp at e; simp [*]⟩

/- separation -/

theorem mem_sep {s : set α} {p : α → Prop} {x : α} (xs : x ∈ s) (px : p x) : x ∈ {x ∈ s | p x} :=
⟨xs, px⟩

@[simp]
theorem mem_sep_eq {s : set α} {p : α → Prop} {x : α} : x ∈ {x ∈ s | p x} = (x ∈ s ∧ p x) :=
rfl

theorem mem_sep_iff {s : set α} {p : α → Prop} {x : α} : x ∈ {x ∈ s | p x} ↔ x ∈ s ∧ p x :=
iff.rfl

theorem eq_sep_of_subset {s t : set α} (ssubt : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
by finish [set_eq_def, iff_def, subset_def]

theorem sep_subset (s : set α) (p : α → Prop) : {x ∈ s | p x} ⊆ s :=
assume x, and.left

theorem forall_not_of_sep_empty {s : set α} {p : α → Prop} (h : {x ∈ s | p x} = ∅) :
  ∀ x ∈ s, ¬ p x :=
by finish [set_eq_def]

/- complement -/

theorem mem_compl {s : set α} {x : α} (h : x ∉ s) : x ∈ -s := h

theorem not_mem_of_mem_compl {s : set α} {x : α} (h : x ∈ -s) : x ∉ s := h

@[simp] theorem mem_compl_eq (s : set α) (x : α) : x ∈ -s = (x ∉ s) := rfl

theorem mem_compl_iff (s : set α) (x : α) : x ∈ -s ↔ x ∉ s := iff.rfl

@[simp] theorem inter_compl_self (s : set α) : s ∩ -s = ∅ :=
by finish [set_eq_def]

@[simp] theorem compl_inter_self (s : set α) : -s ∩ s = ∅ :=
by finish [set_eq_def]

@[simp] theorem compl_empty : -(∅ : set α) = univ :=
by finish [set_eq_def]

@[simp] theorem compl_union (s t : set α) : -(s ∪ t) = -s ∩ -t :=
by finish [set_eq_def]

@[simp] theorem compl_compl (s : set α) : -(-s) = s :=
by finish [set_eq_def]

-- ditto
theorem compl_inter (s t : set α) : -(s ∩ t) = -s ∪ -t :=
by finish [set_eq_def]

@[simp] theorem compl_univ : -(univ : set α) = ∅ :=
by finish [set_eq_def]

theorem union_eq_compl_compl_inter_compl (s t : set α) : s ∪ t = -(-s ∩ -t) :=
by simp [compl_inter, compl_compl]

theorem inter_eq_compl_compl_union_compl (s t : set α) : s ∩ t = -(-s ∪ -t) :=
by simp [compl_compl]

theorem union_compl_self (s : set α) : s ∪ -s = univ :=
by finish [set_eq_def]

theorem compl_union_self (s : set α) : -s ∪ s = univ :=
by finish [set_eq_def]

theorem compl_comp_compl : compl ∘ compl = @id (set α) :=
funext compl_compl

/- set difference -/

theorem diff_eq (s t : set α) : s \ t = s ∩ -t := rfl

theorem mem_diff {s t : set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
⟨h1, h2⟩

theorem mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
h.left

theorem not_mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
h.right

theorem mem_diff_iff (s t : set α) (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := iff.rfl

@[simp] theorem mem_diff_eq (s t : set α) (x : α) : x ∈ s \ t = (x ∈ s ∧ x ∉ t) := rfl

theorem union_diff_cancel {s t : set α} (h : s ⊆ t) : s ∪ (t \ s) = t :=
by finish [set_eq_def, iff_def, subset_def]

theorem diff_subset (s t : set α) : s \ t ⊆ s :=
by finish [subset_def]

theorem compl_eq_univ_diff (s : set α) : -s = univ \ s :=
by finish [set_eq_def]

/- powerset -/

theorem mem_powerset {x s : set α} (h : x ⊆ s) : x ∈ powerset s := h

theorem subset_of_mem_powerset {x s : set α} (h : x ∈ powerset s) : x ⊆ s := h

theorem mem_powerset_iff (x s : set α) : x ∈ powerset s ↔ x ⊆ s := iff.rfl

/- function image -/

section image

infix ` '' `:80 := image

@[reducible] def eq_on (f1 f2 : α → β) (a : set α) : Prop :=
∀ x ∈ a, f1 x = f2 x

-- TODO(Jeremy): use bounded exists in image

theorem mem_image_eq (f : α → β) (s : set α) (y: β) : y ∈ image f s = ∃ x, x ∈ s ∧ f x = y :=
rfl

-- the introduction rule
theorem mem_image {f : α → β} {s : set α} {x : α} {y : β} (h₁ : x ∈ s) (h₂ : f x = y) :
  y ∈ image f s :=
⟨x, h₁, h₂⟩

theorem mem_image_of_mem (f : α → β) {x : α} {a : set α} (h : x ∈ a) : f x ∈ image f a :=
mem_image h rfl

theorem mono_image {f : α → β} {s t : set α} (h : s ⊆ t) : image f s ⊆ image f t :=
assume x ⟨y, hy, y_eq⟩, y_eq ▸ mem_image_of_mem _ $ h hy

/- image and vimage are a Galois connection -/
theorem image_subset_iff_subset_vimage {s : set α} {t : set β} {f : α → β} :
  set.image f s ⊆ t ↔ s ⊆ {x | f x ∈ t} :=
⟨assume h x hx, h (mem_image_of_mem f hx),
  assume h x hx, match x, hx with ._, ⟨y, hy, rfl⟩ := h hy end⟩

def mem_image_elim {f : α → β} {s : set α} {C : β → Prop} (h : ∀ (x : α), x ∈ s → C (f x)) :
 ∀{y : β}, y ∈ image f s → C y
| ._ ⟨a, a_in, rfl⟩ := h a a_in

def mem_image_elim_on {f : α → β} {s : set α} {C : β → Prop} {y : β} (h_y : y ∈ image f s)
  (h : ∀ (x : α), x ∈ s → C (f x)) : C y :=
mem_image_elim h h_y

theorem image_eq_image_of_eq_on {f₁ f₂ : α → β} {s : set α} (heq : eq_on f₁ f₂ s) :
  image f₁ s = image f₂ s :=
by safe [set_eq_def, iff_def, mem_image_eq, eq_on]

-- TODO(Jeremy): make automatic
theorem image_comp (f : β → γ) (g : α → β) (a : set α) : image (f ∘ g) a = image f (image g a) :=
begin
  safe [set_eq_def, iff_def, mem_image_eq, (∘)],
  have h' :=  h_1 (g a_1),
  finish
end

theorem image_subset {a b : set α} (f : α → β) (h : a ⊆ b) : image f a ⊆ image f b :=
by finish [subset_def, mem_image_eq]

theorem image_union (f : α → β) (s t : set α) :
  image f (s ∪ t) = image f s ∪ image f t :=
by finish [set_eq_def, iff_def, mem_image_eq]

theorem image_empty (f : α → β) : image f ∅ = ∅ :=
by finish [set_eq_def, mem_image_eq]

theorem fix_set_compl (t : set α) : compl t = - t := rfl

-- TODO(Jeremy): there is an issue with - t unfolding to compl t
theorem mem_image_compl (t : set α) (S : set (set α)) :
  t ∈ image compl S ↔ -t ∈ S :=
begin
  safe [mem_image_eq, iff_def, fix_set_compl],
  have h' := h_1 (- t), clear h_1,
  all_goals { simp [compl_compl] at *; contradiction }
end

theorem image_id (s : set α) : image id s = s :=
by finish [set_eq_def, iff_def, mem_image_eq]

theorem compl_compl_image (S : set (set α)) :
  image compl (image compl S) = S :=
by rw [←image_comp, compl_comp_compl, image_id]

theorem bounded_forall_image_of_bounded_forall {f : α → β} {s : set α} {p : β → Prop}
  (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ image f s, p y :=
by finish [mem_image_eq]

theorem bounded_forall_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ image f s, p y) ↔ (∀ x ∈ s, p (f x)) :=
begin
  safe [mem_image_eq, iff_def],
  have h' := h_1 (f a),
  finish
end

theorem image_insert_eq {f : α → β} {a : α} {s : set α} :
  image f (insert a s) = insert (f a) (image f s) :=
begin
  safe [set_eq_def, iff_def, mem_image_eq],
  have h' := h_1 a,
  finish
end

end image

/- inverse image -/

def vimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}

section vimage
variables {f : α → β} {g : β → γ}

@[simp] theorem vimage_empty : vimage f ∅ = ∅ := rfl

@[simp] theorem mem_vimage_eq {s : set β} {a : α} : (a ∈ vimage f s) = (f a ∈ s) := rfl

theorem vimage_mono {s t : set β} (h : s ⊆ t) : vimage f s ⊆ vimage f t :=
assume x hx, h hx

theorem vimage_image_eq {s : set α} (h : ∀{x y}, f x = f y → x = y) : vimage f (image f s) = s :=
set.ext $ assume x, ⟨assume ⟨y, hy, y_eq⟩, h y_eq ▸ hy, assume hx, mem_image_of_mem _ hx⟩

@[simp] theorem vimage_univ : vimage f univ = univ := rfl

@[simp] theorem vimage_inter {s t : set β} : vimage f (s ∩ t) = vimage f s ∩ vimage f t := rfl

@[simp] theorem vimage_union {s t : set β} : vimage f (s ∪ t) = vimage f s ∪ vimage f t := rfl

@[simp] theorem vimage_compl {s : set β} : vimage f (- s) = - vimage f s := rfl

theorem vimage_id {s : set α} : vimage id s = s := rfl

theorem vimage_comp {s : set γ} : vimage (g ∘ f) s = vimage f (vimage g s) := rfl

theorem eq_vimage_subtype_val_iff {p : α → Prop} {s : set (subtype p)} {t : set α} :
  s = vimage subtype.val t ↔ (∀x (h : p x), (⟨x, h⟩ : subtype p) ∈ s ↔ x ∈ t) :=
⟨ assume s_eq x h, by rw [s_eq]; simp
, assume h, set.ext $ assume ⟨x, hx⟩, by simp [h]⟩

end vimage

def pairwise_on (s : set α) (r : α → α → Prop) := ∀x ∈ s, ∀y ∈ s, x ≠ y → r x y

end set
