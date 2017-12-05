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

@[trans] lemma mem_of_mem_of_subset {α : Type u} {x : α} {s t : set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
h hx

/- mem and set_of -/

@[simp] theorem mem_set_of_eq {a : α} {p : α → Prop} : a ∈ {a | p a} = p a := rfl

@[simp] theorem nmem_set_of_eq {a : α} {P : α → Prop} : a ∉ {a : α | P a} = ¬ P a := rfl

@[simp] lemma set_of_mem_eq {s : set α} : {x | x ∈ s} = s := rfl

theorem mem_def {a : α} {s : set α} : a ∈ s ↔ s a := iff.rfl

instance decidable_mem (s : set α) [H : decidable_pred s] : ∀ a, decidable (a ∈ s) := H

instance decidable_set_of (p : α → Prop) [H : decidable_pred p] : decidable_pred {a | p a} := H

/- set coercion to a type -/

instance : has_coe_to_sort (set α) := ⟨_, λ s, {x // x ∈ s}⟩

@[simp] theorem set_coe_eq_subtype (s : set α) : coe_sort.{(u+1) (u+2)} s = {x // x ∈ s} := rfl

@[simp] theorem set_coe.forall {s : set α} {p : s → Prop} :
  (∀ x : s, p x) ↔ (∀ x (h : x ∈ s), p ⟨x, h⟩) :=
subtype.forall

@[simp] theorem set_coe.exists {s : set α} {p : s → Prop} :
  (∃ x : s, p x) ↔ (∃ x (h : x ∈ s), p ⟨x, h⟩) :=
subtype.exists

/- subset -/

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl

theorem subset.refl (a : set α) : a ⊆ a := assume x, id

@[trans] theorem subset.trans {a b c : set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c :=
assume x h, bc (ab h)

@[trans] theorem mem_of_eq_of_mem {α : Type u} {x y : α} {s : set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
hx.symm ▸ h

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

@[simp] lemma not_not_mem {α : Type u} {a : α} {s : set α} [decidable (a ∈ s)] :
  ¬ (a ∉ s) ↔ a ∈ s :=
not_not


/- empty set -/

theorem empty_def : (∅ : set α) = {x | false} := rfl

@[simp] theorem mem_empty_eq (x : α) : x ∈ (∅ : set α) = false := rfl

@[simp] theorem set_of_false : {a : α | false} = ∅ := rfl

theorem eq_empty_of_forall_not_mem {s : set α} (h : ∀ x, x ∉ s) : s = ∅ :=
ext $ by simp [h]

theorem ne_empty_of_mem {s : set α} {x : α} (h : x ∈ s) : s ≠ ∅ :=
by { intro hs, rewrite hs at h, apply not_mem_empty _ h }

@[simp] theorem empty_subset (s : set α) : ∅ ⊆ s :=
assume x, assume h, false.elim h

theorem eq_empty_of_subset_empty {s : set α} (h : s ⊆ ∅) : s = ∅ :=
subset.antisymm h (empty_subset s)

theorem exists_mem_of_ne_empty {s : set α} (h : s ≠ ∅) : ∃ x, x ∈ s :=
by finish [set_eq_def]

lemma ne_empty_iff_exists_mem {s : set α} : s ≠ ∅ ↔ ∃ x, x ∈ s :=
⟨exists_mem_of_ne_empty, assume ⟨x, hx⟩, ne_empty_of_mem hx⟩

-- TODO: remove when simplifier stops rewriting `a ≠ b` to `¬ a = b`
lemma not_eq_empty_iff_exists {s : set α} : ¬ (s = ∅) ↔ ∃ x, x ∈ s :=
ne_empty_iff_exists_mem

theorem subset_empty_iff {s : set α} : s ⊆ ∅ ↔ s = ∅ :=
by finish [set_eq_def]

theorem subset_eq_empty {s t : set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
subset_empty_iff.1 $ e ▸ h

theorem subset_ne_empty {s t : set α} (h : t ⊆ s) : t ≠ ∅ → s ≠ ∅ :=
mt (subset_eq_empty h)

theorem ball_empty_iff {p : α → Prop} :
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

theorem eq_univ_iff_forall {s : set α} : s = univ ↔ ∀ x, x ∈ s :=
by finish [set_eq_def]

theorem eq_univ_of_forall {s : set α} : (∀ x, x ∈ s) → s = univ := eq_univ_iff_forall.2

/- union -/

theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl

theorem mem_union_left {x : α} {a : set α} (b : set α) : x ∈ a → x ∈ a ∪ b := or.inl

theorem mem_union_right {x : α} {b : set α} (a : set α) : x ∈ b → x ∈ a ∪ b := or.inr

theorem mem_or_mem_of_mem_union {x : α} {a b : set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b := H

theorem mem_union.elim {x : α} {a b : set α} {P : Prop}
    (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
or.elim H₁ H₂ H₃

theorem mem_union (x : α) (a b : set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := iff.rfl

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

@[simp] theorem inter_subset_left (s t : set α) : s ∩ t ⊆ s := λ x H, and.left H

@[simp] theorem inter_subset_right (s t : set α) : s ∩ t ⊆ t := λ x H, and.right H

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
by finish [subset_def, inter_def]

@[simp] theorem subset_inter_iff {s t r : set α} : r ⊆ s ∩ t ↔ r ⊆ s ∧ r ⊆ t :=
⟨λ h, ⟨subset.trans h (inter_subset_left _ _), subset.trans h (inter_subset_right _ _)⟩,
 λ ⟨h₁, h₂⟩, subset_inter h₁ h₂⟩

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
ext (assume x, and_or_distrib_left)

theorem inter_distrib_right (s t u : set α) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
ext (assume x, or_and_distrib_right)

theorem union_distrib_left (s t u : set α) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
ext (assume x, or_and_distrib_left)

theorem union_distrib_right (s t u : set α) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
ext (assume x, and_or_distrib_right)

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

@[simp] theorem mem_insert_iff (x a : α) (s : set α) : x ∈ insert a s ↔ (x = a ∨ x ∈ s) := iff.rfl

@[simp] theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by finish [set_eq_def, iff_def]

theorem ssubset_insert {s : set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
by finish [ssubset_def, set_eq_def]

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
ext $ by simp [or.left_comm]

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

theorem ball_insert_iff {P : α → Prop} {a : α} {s : set α} :
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
by finish [set_eq_def, or_comm]

@[simp] theorem union_insert_eq {a : α} {s t : set α} :
  s ∪ (insert a t) = insert a (s ∪ t) :=
by simp [insert_eq]

@[simp] theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
by finish

@[simp] theorem singleton_ne_empty (a : α) : ({a} : set α) ≠ ∅ := insert_ne_empty _ _

@[simp] theorem singleton_subset_iff {a : α} {s : set α} : {a} ⊆ s ↔ a ∈ s :=
⟨λh, h (by simp), λh b e, by simp at e; simp [*]⟩

lemma set_compr_eq_eq_singleton {a : α} : {b | b = a} = {a} :=
set.ext $ by simp

/- separation -/

theorem mem_sep {s : set α} {p : α → Prop} {x : α} (xs : x ∈ s) (px : p x) : x ∈ {x ∈ s | p x} :=
⟨xs, px⟩

@[simp] theorem mem_sep_eq {s : set α} {p : α → Prop} {x : α} : x ∈ {x ∈ s | p x} = (x ∈ s ∧ p x) := rfl

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

lemma compl_subset_of_compl_subset {α : Type u} {s t : set α} (h : -s ⊆ t) : -t ⊆ s :=
assume x hx, classical.by_contradiction $ assume : x ∉ s, hx $ h $ this

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

lemma diff_subset_diff {s₁ s₂ t₁ t₂ : set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
by finish [subset_def]

lemma diff_right_antimono {s t u : set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
diff_subset_diff (subset.refl s) h

theorem compl_eq_univ_diff (s : set α) : -s = univ \ s :=
by finish [set_eq_def]

lemma diff_neq_empty {s t : set α} : s \ t = ∅ ↔ s ⊆ t :=
⟨assume h x hx, classical.by_contradiction $ assume : x ∉ t, show x ∈ (∅ : set α), from h ▸ ⟨hx, this⟩,
  assume h, eq_empty_of_subset_empty $ assume x ⟨hx, hnx⟩, hnx $ h hx⟩

@[simp] lemma diff_empty {s : set α} : s \ ∅ = s :=
set.ext $ assume x, ⟨assume ⟨hx, _⟩, hx, assume h, ⟨h, not_false⟩⟩

/- powerset -/

theorem mem_powerset {x s : set α} (h : x ⊆ s) : x ∈ powerset s := h

theorem subset_of_mem_powerset {x s : set α} (h : x ∈ powerset s) : x ⊆ s := h

theorem mem_powerset_iff (x s : set α) : x ∈ powerset s ↔ x ⊆ s := iff.rfl

/- inverse image -/

def preimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}

infix ` ⁻¹' `:80 := preimage

section preimage
variables {f : α → β} {g : β → γ}

@[simp] theorem preimage_empty : f ⁻¹' ∅ = ∅ := rfl

@[simp] theorem mem_preimage_eq {s : set β} {a : α} : (a ∈ f ⁻¹' s) = (f a ∈ s) := rfl

theorem preimage_mono {s t : set β} (h : s ⊆ t) : f ⁻¹' s ⊆ f ⁻¹' t :=
assume x hx, h hx

@[simp] theorem preimage_univ : f ⁻¹' univ = univ := rfl

@[simp] theorem preimage_inter {s t : set β} : f ⁻¹' (s ∩ t) = f ⁻¹' s ∩ f ⁻¹' t := rfl

@[simp] theorem preimage_union {s t : set β} : f ⁻¹' (s ∪ t) = f ⁻¹' s ∪ f ⁻¹' t := rfl

@[simp] theorem preimage_compl {s : set β} : f ⁻¹' (- s) = - (f ⁻¹' s) := rfl

@[simp] theorem preimage_diff (f : α → β) (s t : set β) :
  f ⁻¹' (s \ t) = f ⁻¹' s \ f ⁻¹' t := rfl

@[simp] theorem preimage_set_of_eq {p : α → Prop} {f : β → α} : f ⁻¹' {a | p a} = {a | p (f a)} :=
rfl

theorem preimage_id {s : set α} : id ⁻¹' s = s := rfl

theorem preimage_comp {s : set γ} : (g ∘ f) ⁻¹' s = f ⁻¹' (g ⁻¹' s) := rfl

theorem eq_preimage_subtype_val_iff {p : α → Prop} {s : set (subtype p)} {t : set α} :
  s = subtype.val ⁻¹' t ↔ (∀x (h : p x), (⟨x, h⟩ : subtype p) ∈ s ↔ x ∈ t) :=
⟨assume s_eq x h, by rw [s_eq]; simp,
 assume h, set.ext $ assume ⟨x, hx⟩, by simp [h]⟩

end preimage

/- function image -/

section image

infix ` '' `:80 := image

@[reducible] def eq_on (f1 f2 : α → β) (a : set α) : Prop :=
∀ x ∈ a, f1 x = f2 x

-- TODO(Jeremy): use bounded exists in image

theorem mem_image_iff_bex {f : α → β} {s : set α} {y : β} :
  y ∈ f '' s ↔ ∃ x (_ : x ∈ s), f x = y := bex_def.symm

theorem mem_image_eq (f : α → β) (s : set α) (y: β) : y ∈ f '' s = ∃ x, x ∈ s ∧ f x = y := rfl

@[simp] theorem mem_image (f : α → β) (s : set α) (y : β) : y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y := iff.rfl

theorem mem_image_of_mem (f : α → β) {x : α} {a : set α} (h : x ∈ a) : f x ∈ f '' a :=
⟨_, h, rfl⟩

theorem ball_image_of_ball {f : α → β} {s : set α} {p : β → Prop}
  (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ f '' s, p y :=
by finish [mem_image_eq]

@[simp] theorem ball_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ f '' s, p y) ↔ (∀ x ∈ s, p (f x)) :=
iff.intro
  (assume h a ha, h _ $ mem_image_of_mem _ ha)
  (assume h b ⟨a, ha, eq⟩, eq ▸ h a ha)

theorem mono_image {f : α → β} {s t : set α} (h : s ⊆ t) : f '' s ⊆ f '' t :=
assume x ⟨y, hy, y_eq⟩, y_eq ▸ mem_image_of_mem _ $ h hy

def mem_image_elim {f : α → β} {s : set α} {C : β → Prop} (h : ∀ (x : α), x ∈ s → C (f x)) :
 ∀{y : β}, y ∈ f '' s → C y
| ._ ⟨a, a_in, rfl⟩ := h a a_in

def mem_image_elim_on {f : α → β} {s : set α} {C : β → Prop} {y : β} (h_y : y ∈ f '' s)
  (h : ∀ (x : α), x ∈ s → C (f x)) : C y :=
mem_image_elim h h_y

theorem image_eq_image_of_eq_on {f₁ f₂ : α → β} {s : set α} (heq : eq_on f₁ f₂ s) :
  f₁ '' s = f₂ '' s :=
by safe [set_eq_def, iff_def, mem_image, eq_on]

theorem image_comp (f : β → γ) (g : α → β) (a : set α) : (f ∘ g) '' a = f '' (g '' a) :=
subset.antisymm
  (ball_image_of_ball $ assume a ha, mem_image_of_mem _ $ mem_image_of_mem _ ha)
  (ball_image_of_ball $ ball_image_of_ball $ assume a ha, mem_image_of_mem _ ha)
/- Proof is removed as it uses generated names
TODO(Jeremy): make automatic,
begin
  safe [set_eq_def, iff_def, mem_image, (∘)],
  have h' := h_2 (g a_2),
  finish
end -/

theorem image_subset {a b : set α} (f : α → β) (h : a ⊆ b) : f '' a ⊆ f '' b :=
by finish [subset_def, mem_image_eq]

theorem image_union (f : α → β) (s t : set α) :
  f '' (s ∪ t) = f '' s ∪ f '' t :=
by finish [set_eq_def, iff_def, mem_image_eq]

theorem image_empty (f : α → β) : f '' ∅ = ∅ :=
by finish [set_eq_def, mem_image_eq]

lemma image_inter_on {f : α → β} {s t : set α} (h : ∀x∈t, ∀y∈s, f x = f y → x = y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
subset.antisymm
  (assume b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩,
    have a₂ = a₁, from h _ ha₂ _ ha₁ (by simp *),
    ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
  (subset_inter (mono_image $ inter_subset_left _ _) (mono_image $ inter_subset_right _ _))

lemma image_inter {f : α → β} {s t : set α} (h : ∀ x y, f x = f y → x = y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
image_inter_on (assume x _ y _, h x y)

@[simp] lemma image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
set.ext $ λ x, by simp [image]; rw eq_comm

theorem fix_set_compl (t : set α) : compl t = - t := rfl

-- TODO(Jeremy): there is an issue with - t unfolding to compl t
theorem mem_image_compl (t : set α) (S : set (set α)) :
  t ∈ compl '' S ↔ -t ∈ S :=
begin
  suffices : ∀ x, -x = t ↔ -t = x, {simp [fix_set_compl, this]},
  intro x, split; { intro e, subst e, simp }
end

theorem image_id (s : set α) : id '' s = s :=
by finish [set_eq_def, iff_def, mem_image_eq]

theorem compl_compl_image (S : set (set α)) :
  compl '' (compl '' S) = S :=
by rw [← image_comp, compl_comp_compl, image_id]

theorem image_insert_eq {f : α → β} {a : α} {s : set α} :
  f '' (insert a s) = insert (f a) (f '' s) :=
ext $ by simp [and_or_distrib_left, exists_or_distrib, eq_comm, or_comm, and_comm]

theorem image_subset_preimage_of_inverse {f : α → β} {g : β → α}
  (I : function.left_inverse g f) (s : set α) :
  f '' s ⊆ g ⁻¹' s :=
λ b ⟨a, h, e⟩, e ▸ ((I a).symm ▸ h : g (f a) ∈ s)

theorem preimage_subset_image_of_inverse {f : α → β} {g : β → α}
  (I : function.left_inverse g f) (s : set β) :
  f ⁻¹' s ⊆ g '' s :=
λ b h, ⟨f b, h, I b⟩

theorem image_eq_preimage_of_inverse {f : α → β} {g : β → α}
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  image f = preimage g :=
funext $ λ s, subset.antisymm
  (image_subset_preimage_of_inverse h₁ s)
  (preimage_subset_image_of_inverse h₂ s)

theorem mem_image_iff_of_inverse {f : α → β} {g : β → α} {b : β} {s : set α}
  (h₁ : function.left_inverse g f) (h₂ : function.right_inverse g f) :
  b ∈ f '' s ↔ g b ∈ s :=
by rw image_eq_preimage_of_inverse h₁ h₂; refl

/- image and preimage are a Galois connection -/
theorem image_subset_iff {s : set α} {t : set β} {f : α → β} :
  f '' s ⊆ t ↔ s ⊆ f ⁻¹' t :=
ball_image_iff

theorem image_preimage_subset (f : α → β) (s : set β) :
  f '' (f ⁻¹' s) ⊆ s :=
image_subset_iff.2 (subset.refl _)

theorem subset_preimage_image (f : α → β) (s : set α) :
  s ⊆ f ⁻¹' (f '' s) :=
λ x, mem_image_of_mem f

theorem preimage_image_eq {f : α → β} {s : set α}
  (h : function.injective f) : f ⁻¹' (f '' s) = s :=
subset.antisymm
  (λ x ⟨y, hy, e⟩, h e ▸ hy)
  (subset_preimage_image f s)

theorem image_preimage_eq {f : α → β} {s : set β}
  (h : function.surjective f) : f '' (f ⁻¹' s) = s :=
subset.antisymm
  (image_preimage_subset f s)
  (λ x hx, let ⟨y, e⟩ := h x in ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩)

lemma image_preimage_eq_inter_rng {f : α → β} {t : set β} :
  f '' preimage f t = t ∩ f '' univ :=
set.ext $ assume x, ⟨assume ⟨x, hx, heq⟩, heq ▸ ⟨hx, mem_image_of_mem f trivial⟩,
  assume ⟨hx, ⟨y, hy, h_eq⟩⟩, h_eq ▸ mem_image_of_mem f $
    show y ∈ preimage f t, by simp [preimage, h_eq, hx]⟩

theorem compl_image : image (@compl α) = preimage compl :=
image_eq_preimage_of_inverse compl_compl compl_compl

lemma compl_image_set_of {α : Type u} {p : set α → Prop} :
  compl '' {x | p x} = {x | p (- x)} :=
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

@[simp] lemma quot_mk_image_univ_eq [setoid α] : (λx : α, ⟦x⟧) '' univ = univ :=
set.ext $ assume x, quotient.induction_on x $ assume a, ⟨by simp, assume _, ⟨a, trivial, rfl⟩⟩

end image

lemma univ_eq_true_false : univ = ({true, false} : set Prop) :=
eq.symm $ eq_univ_of_forall $ classical.cases (by simp) (by simp)

section range
variables {f : ι → α}
open function

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : set α := {x | ∃y, f y = x}

lemma mem_range {i : ι} : f i ∈ range f := ⟨i, rfl⟩

lemma forall_range_iff {p : α → Prop} : (∀ a ∈ range f, p a) ↔ (∀ i, p (f i)) :=
⟨assume h i, h (f i) mem_range, assume h a ⟨i, (hi : f i = a)⟩, hi ▸ h i⟩

lemma range_iff_surjective : range f = univ ↔ surjective f :=
eq_univ_iff_forall

@[simp] lemma range_id : range (@id α) = univ := range_iff_surjective.2 surjective_id

lemma range_eq_image {ι : Type*} {f : ι → β} : range f = f '' univ :=
set.ext $ by simp [image, range]

lemma range_compose {g : α → β} : range (g ∘ f) = g '' range f :=
subset.antisymm
  (forall_range_iff.mpr $ assume i, mem_image_of_mem g mem_range)
  (ball_image_iff.mpr $ forall_range_iff.mpr $ assume i, mem_range)
end range

def pairwise_on (s : set α) (r : α → α → Prop) := ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y

end set
