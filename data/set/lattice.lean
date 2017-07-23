/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors Jeremy Avigad, Leonardo de Moura, Johannes Hölzl

-- QUESTION: can make the first argument in ∀ x ∈ a, ... implicit?
-/
import logic.basic data.set.basic
import algebra.lattice algebra.lattice.complete_boolean_algebra
import tools.auto.finish

open function tactic set lattice auto

universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x}

namespace set

instance : inhabited (set α) :=
⟨∅⟩

@[simp]
lemma mem_set_of {a : α} {p : α → Prop} : a ∈ {a | p a} = p a :=
rfl

theorem set_eq_def (s t : set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
⟨begin intros h x, rw h end, set.ext⟩

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl
theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl
theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := rfl

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
by finish [subset_def, union_def]

theorem inter_subset_left (s t : set α) : s ∩ t ⊆ s := λ x H, and.left H

theorem inter_subset_right (s t : set α) : s ∩ t ⊆ t := λ x H, and.right H

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
by finish [subset_def, inter_def]

instance lattice_set : complete_lattice (set α) :=
{ lattice.complete_lattice .
  le           := (⊆),
  le_refl      := subset.refl,
  le_trans     := assume a b c, subset.trans,
  le_antisymm  := assume a b, subset.antisymm,

  sup          := (∪),
  le_sup_left  := subset_union_left,
  le_sup_right := subset_union_right,
  sup_le       := assume a b c, union_subset,

  inf          := (∩),
  inf_le_left  := inter_subset_left,
  inf_le_right := inter_subset_right,
  le_inf       := assume a b c, subset_inter,

  top          := {a | true },
  le_top       := assume s a h, trivial,

  bot          := ∅,
  bot_le       := assume s a, false.elim,

  Sup          := λs, {a | ∃ t ∈ s, a ∈ t },
  le_Sup       := assume s t t_in a a_in, ⟨t, ⟨t_in, a_in⟩⟩,
  Sup_le       := assume s t h a ⟨t', ⟨t'_in, a_in⟩⟩, h t' t'_in a_in,

  Inf          := λs, {a | ∀ t ∈ s, a ∈ t },
  le_Inf       := assume s t h a a_in t' t'_in, h t' t'_in a_in,
  Inf_le       := assume s t t_in a h, h _ t_in }

instance : distrib_lattice (set α) :=
{ set.lattice_set with
  le_sup_inf     := assume s t u x ⟨h₁, h₂⟩,
    match h₁ with
    | or.inl h₁ := or.inl h₁
    | or.inr h₁ :=
      match h₂ with
      | or.inl h₂ := or.inl h₂
      | or.inr h₂ := or.inr ⟨h₁, h₂⟩
      end
    end }

/- mem and set_of -/

@[simp] lemma mem_set_of_eq (a : α) (P : α → Prop) : a ∈ {a : α | P a} = P a :=
rfl

@[simp] lemma nmem_set_of_eq (a : α) (P : α → Prop) : a ∉ {a : α | P a} = ¬ P a :=
rfl

@[simp] lemma set_of_false : {a : α | false} = ∅ :=
set.ext $ assume a, by simp [mem_empty_eq]

/- strict subset -/

def strict_subset (s t : set α) := s ⊆ t ∧ s ≠ t

instance : has_ssubset (set α) := ⟨strict_subset⟩

theorem ssubset_def {s t : set α} : (s ⊂ t) = (s ⊆ t ∧ s ≠ t) := rfl

/- empty set -/

attribute [simp] mem_empty_eq empty_subset

theorem exists_mem_of_ne_empty {s : set α} (h : s ≠ ∅) : ∃ x, x ∈ s :=
by finish [set_eq_def]

theorem subset_empty_iff (s : set α) : s ⊆ ∅ ↔ s = ∅ :=
by finish [set_eq_def]

lemma bounded_forall_empty_iff {p : α → Prop} :
  (∀ x ∈ (∅ : set α), p x) ↔ true :=
by finish [iff_def]

/- universal set -/

theorem mem_univ (x : α) : x ∈ @univ α :=
by trivial

theorem mem_univ_iff (x : α) : x ∈ @univ α ↔ true := iff.rfl

@[simp]
theorem mem_univ_eq (x : α) : x ∈ @univ α = true := rfl

theorem empty_ne_univ [h : inhabited α] : (∅ : set α) ≠ univ :=
by clarify [set_eq_def]

theorem univ_def : @univ α = { x | true } := rfl

@[simp]
theorem subset_univ (s : set α) : s ⊆ univ := λ x H, trivial

theorem eq_univ_of_univ_subset {s : set α} (h : univ ⊆ s) : s = univ :=
by finish [subset_def, set_eq_def]

theorem eq_univ_of_forall {s : set α} (H : ∀ x, x ∈ s) : s = univ :=
by finish [set_eq_def]

/- union -/

theorem mem_union_left {x : α} {a : set α} (b : set α) : x ∈ a → x ∈ a ∪ b :=
assume h, or.inl h

theorem mem_union_right {x : α} {b : set α} (a : set α) : x ∈ b → x ∈ a ∪ b :=
assume h, or.inr h

theorem mem_unionl {x : α} {a b : set α} : x ∈ a → x ∈ a ∪ b :=
assume h, or.inl h

theorem mem_unionr {x : α} {a b : set α} : x ∈ b → x ∈ a ∪ b :=
assume h, or.inr h

theorem mem_or_mem_of_mem_union {x : α} {a b : set α} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b := H

theorem mem_union.elim {x : α} {a b : set α} {P : Prop}
    (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
or.elim H₁ H₂ H₃

theorem mem_union_iff (x : α) (a b : set α) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := iff.rfl

@[simp]
theorem mem_union_eq (x : α) (a b : set α) : x ∈ a ∪ b = (x ∈ a ∨ x ∈ b) := rfl

attribute [simp] union_self union_empty empty_union -- union_comm union_assoc

theorem union_left_comm (s₁ s₂ s₃ : set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
by finish [set_eq_def]

theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
by finish [set_eq_def]

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
by finish [subset_def, set_eq_def, iff_def]

theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by finish [subset_def, set_eq_def, iff_def]

lemma union_subset_iff {s t u : set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
@sup_le_iff (set α) _ s t u

theorem union_subset_union {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∪ s₂ ⊆ t₁ ∪ t₂ :=
@sup_le_sup (set α) _ _ _ _ _ h₁ h₂

attribute [simp] union_comm union_assoc union_left_comm

/- intersection -/
theorem mem_inter_iff (x : α) (a b : set α) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := iff.rfl

@[simp]
theorem mem_inter_eq (x : α) (a b : set α) : x ∈ a ∩ b = (x ∈ a ∧ x ∈ b) := rfl

theorem mem_inter {x : α} {a b : set α} (ha : x ∈ a) (hb : x ∈ b) : x ∈ a ∩ b :=
⟨ha, hb⟩

theorem mem_of_mem_inter_left {x : α} {a b : set α} (h : x ∈ a ∩ b) : x ∈ a :=
h^.left

theorem mem_of_mem_inter_right {x : α} {a b : set α} (h : x ∈ a ∩ b) : x ∈ b :=
h^.right

attribute [simp] inter_self inter_empty empty_inter -- inter_comm inter_assoc

theorem nonempty_of_inter_nonempty_right {T : Type} {s t : set T} (h : s ∩ t ≠ ∅) : t ≠ ∅ :=
by finish [set_eq_def, iff_def]

theorem nonempty_of_inter_nonempty_left {T : Type} {s t : set T} (h : s ∩ t ≠ ∅) : s ≠ ∅ :=
by finish [set_eq_def, iff_def]

theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
by finish [set_eq_def, iff_def]

theorem inter_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
by finish [set_eq_def, iff_def]

theorem inter_univ (a : set α) : a ∩ univ = a :=
ext (assume x, and_true _)

theorem univ_inter (a : set α) : univ ∩ a = a :=
ext (assume x, true_and _)

theorem inter_subset_inter_right {s t : set α} (u : set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by finish [subset_def]

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∩ s₂ ⊆ t₁ ∩ t₂ :=
@inf_le_inf (set α) _ _ _ _ _ h₁ h₂

theorem inter_subset_inter_left {s t : set α} (u : set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
assume x, assume xus, and.intro (and.left xus) (H (and.right xus))

theorem inter_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∩ t = s :=
by finish [subset_def, set_eq_def, iff_def]

theorem inter_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∩ t = t :=
by finish [subset_def, set_eq_def, iff_def]

attribute [simp] inter_comm inter_assoc inter_left_comm

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
assume y, assume ys, or.inr ys

theorem mem_insert (x : α) (s : set α) : x ∈ insert x s :=
or.inl rfl

theorem mem_insert_of_mem {x : α} {s : set α} (y : α) : x ∈ s → x ∈ insert y s :=
assume h, or.inr h

theorem eq_or_mem_of_mem_insert {x a : α} {s : set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
assume h, h

theorem mem_of_mem_insert_of_ne {x a : α} {s : set α} (xin : x ∈ insert a s) : x ≠ a → x ∈ s :=
by finish [insert_def]

@[simp]
theorem mem_insert_iff (x a : α) (s : set α) : x ∈ insert a s ↔ (x = a ∨ x ∈ s) :=
iff.refl _

@[simp]
theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by finish [set_eq_def, iff_def]

lemma ssubset_insert {s : set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
by finish [ssubset_def, set_eq_def]

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
ext (assume c, by simp)

-- TODO(Jeremy): make this automatic
theorem insert_ne_empty (a : α) (s : set α) : insert a s ≠ ∅ :=
begin safe [set_eq_def, iff_def]; have h' := a_1 a; finish end

-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ insert a s → P x) :
  ∀ x, x ∈ s → P x :=
by finish

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ s → P x) (ha : P a) :
  ∀ x, x ∈ insert a s → P x :=
by finish

lemma bounded_forall_insert_iff {P : α → Prop} {a : α} {s : set α} :
  (∀ x ∈ insert a s, P x) ↔ P a ∧ (∀x ∈ s, P x) :=
by finish [iff_def]

/- properties of singletons -/

theorem singleton_def (a : α) : ({a} : set α) = insert a ∅ := rfl

@[simp]
theorem mem_singleton_iff (a b : α) : a ∈ ({b} : set α) ↔ a = b :=
by finish [singleton_def]

-- TODO: again, annotation needed
@[simp]
theorem mem_singleton (a : α) : a ∈ ({a} : set α) := mem_insert a _

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : set α)) : x = y :=
by finish

@[simp]
theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : set α) ↔ x = y :=
⟨assume eq, eq_of_mem_singleton $ eq ▸ mem_singleton x, by intro; simp [*]⟩

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : set α) :=
by finish

theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s :=
by finish [set_eq_def]

@[simp] lemma union_insert_eq {a : α} {s t : set α} :
  s ∪ (insert a t) = insert a (s ∪ t) :=
by simp [insert_eq]

@[simp]
theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
by finish

theorem singleton_ne_empty (a : α) : ({a} : set α) ≠ ∅ := insert_ne_empty _ _

@[simp]
lemma singleton_subset_iff {a : α} {s : set α} : {a} ⊆ s ↔ a ∈ s :=
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
assume x, assume H, and.left H

theorem forall_not_of_sep_empty {s : set α} {p : α → Prop} (h : {x ∈ s | p x} = ∅) :
  ∀ x ∈ s, ¬ p x :=
by finish [set_eq_def]

/- complement -/

theorem mem_compl {s : set α} {x : α} (h : x ∉ s) : x ∈ -s := h

theorem not_mem_of_mem_compl {s : set α} {x : α} (h : x ∈ -s) : x ∉ s := h

@[simp]
theorem mem_compl_eq (s : set α) (x : α) : x ∈ -s = (x ∉ s) := rfl

theorem mem_compl_iff (s : set α) (x : α) : x ∈ -s ↔ x ∉ s := iff.rfl

@[simp]
theorem inter_compl_self (s : set α) : s ∩ -s = ∅ :=
by finish [set_eq_def]

@[simp]
theorem compl_inter_self (s : set α) : -s ∩ s = ∅ :=
by finish [set_eq_def]

@[simp]
theorem compl_empty : -(∅ : set α) = univ :=
by finish [set_eq_def]

@[simp]
theorem compl_union (s t : set α) : -(s ∪ t) = -s ∩ -t :=
by finish [set_eq_def]

@[simp]
theorem compl_compl (s : set α) : -(-s) = s :=
by finish [set_eq_def]

-- ditto
theorem compl_inter (s t : set α) : -(s ∩ t) = -s ∪ -t :=
by finish [set_eq_def]

@[simp]
theorem compl_univ : -(univ : set α) = ∅ :=
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
funext (λ s, compl_compl s)

/- set difference -/

theorem diff_eq (s t : set α) : s \ t = s ∩ -t := rfl

theorem mem_diff {s t : set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
⟨h1, h2⟩

theorem mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
h^.left

theorem not_mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
h^.right

theorem mem_diff_iff (s t : set α) (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := iff.rfl

@[simp]
theorem mem_diff_eq (s t : set α) (x : α) : x ∈ s \ t = (x ∈ s ∧ x ∉ t) := rfl

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
lemma image_comp (f : β → γ) (g : α → β) (a : set α) : image (f ∘ g) a = image f (image g a) :=
begin
  safe [set_eq_def, iff_def, mem_image_eq, comp],
  have h' :=  h_1 (g a_1),
  finish
end

lemma image_subset {a b : set α} (f : α → β) (h : a ⊆ b) : image f a ⊆ image f b :=
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

lemma bounded_forall_image_of_bounded_forall {f : α → β} {s : set α} {p : β → Prop}
  (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ image f s, p y :=
by finish [mem_image_eq]

lemma bounded_forall_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ image f s, p y) ↔ (∀ x ∈ s, p (f x)) :=
begin
  safe [mem_image_eq, iff_def],
  have h' := h_1 (f a),
  finish
end

lemma image_insert_eq {f : α → β} {a : α} {s : set α} :
  image f (insert a s) = insert (f a) (image f s) :=
begin
  safe [set_eq_def, iff_def, mem_image_eq],
  have h' := h_1 a,
  finish
end

end image

/- union and intersection over a family of sets indexed by a type -/

@[reducible]
def Union (s : ι → set β) : set β := supr s

@[reducible]
def Inter (s : ι → set β) : set β := infi s

notation `⋃` binders `, ` r:(scoped f, Union f) := r
notation `⋂` binders `, ` r:(scoped f, Inter f) := r

@[simp]
theorem mem_Union_eq (x : β) (s : ι → set β) : (x ∈ ⋃ i, s i) = (∃ i, x ∈ s i) :=
propext
  ⟨assume ⟨t, ⟨⟨a, (t_eq : t = s a)⟩, (h : x ∈ t)⟩⟩, ⟨a, t_eq ▸ h⟩,
  assume ⟨a, h⟩, ⟨s a, ⟨⟨a, rfl⟩, h⟩⟩⟩
/- alternative proof: dsimp [Union, supr, Sup]; simp -/
  -- TODO: more rewrite rules wrt forall / existentials and logical connectives
  -- TODO: also eliminate ∃i, ... ∧ i = t ∧ ...

@[simp]
theorem mem_Inter_eq (x : β) (s : ι → set β) : (x ∈ ⋂ i, s i) = (∀ i, x ∈ s i) :=
propext
  ⟨assume (h : ∀a ∈ {a : set β | ∃i, a = s i}, x ∈ a) a, h (s a) ⟨a, rfl⟩,
  assume h t ⟨a, (eq : t = s a)⟩, eq^.symm ▸ h a⟩


theorem Union_subset {s : ι → set β} {t : set β} (h : ∀ i, s i ⊆ t) : (⋃ i, s i) ⊆ t :=
-- TODO: should be simpler when sets' order is based on lattices
@supr_le (set β) _ set.lattice_set _ _ h

theorem Union_subset_iff {α : Sort u} {s : α → set β} {t : set β} : (⋃ i, s i) ⊆ t ↔ (∀ i, s i ⊆ t):=
⟨assume h i, subset.trans (le_supr s _) h, Union_subset⟩

theorem mem_Inter {α : Sort u} {x : β} {s : α → set β} : (∀ i, x ∈ s i) → (x ∈ ⋂ i, s i) :=
assume h t ⟨a, (eq : t = s a)⟩, eq^.symm ▸ h a

theorem subset_Inter {t : set β} {s : α → set β} (h : ∀ i, t ⊆ s i) : t ⊆ ⋂ i, s i :=
-- TODO: should be simpler when sets' order is based on lattices
@le_infi (set β) _ set.lattice_set _ _ h

@[simp] -- complete_boolean_algebra
theorem compl_Union (s : α → set β) : - (⋃ i, s i) = (⋂ i, - s i) :=
ext (λ x, begin simp, apply not_exists_iff end)

-- classical -- complete_boolean_algebra
theorem compl_Inter (s : α → set β) : -(⋂ i, s i) = (⋃ i, - s i) :=
ext (λ x, begin simp, apply classical.not_forall_iff end)

-- classical -- complete_boolean_algebra
theorem Union_eq_comp_Inter_comp (s : α → set β) : (⋃ i, s i) = - (⋂ i, - s i) :=
by simp [compl_Inter, compl_compl]

-- classical -- complete_boolean_algebra
theorem Inter_eq_comp_Union_comp (s : α → set β) : (⋂ i, s i) = - (⋃ i, -s i) :=
by simp [compl_compl]

theorem inter_distrib_Union_left (s : set β) (t : α → set β) :
  s ∩ (⋃ i, t i) = ⋃ i, s ∩ t i :=
set.ext (by simp)

-- classical
theorem union_distrib_Inter_left (s : set β) (t : α → set β) :
  s ∪ (⋂ i, t i) = ⋂ i, s ∪ t i :=
set.ext $ assume x, by simp [classical.forall_or_distrib_left]

/- bounded unions and intersections -/

theorem mem_bUnion {s : set α} {t : α → set β} {x : α} {y : β} (xs : x ∈ s) (ytx : y ∈ t x) :
  y ∈ ⋃ x ∈ s, t x :=
by simp; exact ⟨x, ⟨xs, ytx⟩⟩

theorem mem_bInter {s : set α} {t : α → set β} {y : β} (h : ∀ x ∈ s, y ∈ t x) :
  y ∈ ⋂ x ∈ s, t x :=
by simp; assumption

theorem bUnion_subset {s : set α} {t : set β} {u : α → set β} (h : ∀ x ∈ s, u x ⊆ t) :
  (⋃ x ∈ s, u x) ⊆ t :=
show (⨆ x ∈ s, u x) ≤ t, -- TODO: should not be necessary when sets' order is based on lattices
  from supr_le $ assume x, supr_le (h x)

theorem subset_bInter {s : set α} {t : set β} {u : α → set β} (h : ∀ x ∈ s, t ⊆ u x) :
  t ⊆ (⋂ x ∈ s, u x) :=
show t ≤ (⨅ x ∈ s, u x), -- TODO: should not be necessary when sets' order is based on lattices
  from le_infi $ assume x, le_infi (h x)

theorem subset_bUnion_of_mem {s : set α} {u : α → set β} {x : α} (xs : x ∈ s) :
  u x ⊆ (⋃ x ∈ s, u x) :=
show u x ≤ (⨆ x ∈ s, u x),
  from le_supr_of_le x $ le_supr _ xs

theorem bInter_subset_of_mem {s : set α} {t : α → set β} {x : α} (xs : x ∈ s) :
  (⋂ x ∈ s, t x) ⊆ t x :=
show (⨅x ∈ s, t x) ≤ t x,
  from infi_le_of_le x $ infi_le _ xs

@[simp]
theorem bInter_empty (u : α → set β) : (⋂ x ∈ (∅ : set α), u x) = univ :=
show (⨅x ∈ (∅ : set α), u x) = ⊤, -- simplifier should be able to rewrite x ∈ ∅ to false.
  from infi_emptyset

@[simp]
theorem bInter_univ (u : α → set β) : (⋂ x ∈ @univ α, u x) = ⋂ x, u x :=
infi_univ

-- TODO(Jeremy): here is an artifact of the the encoding of bounded intersection:
-- without dsimp, the next theorem fails to type check, because there is a lambda
-- in a type that needs to be contracted. Using simp [eq_of_mem_singleton xa] also works.

@[simp]
theorem bInter_singleton (a : α) (s : α → set β) : (⋂ x ∈ ({a} : set α), s x) = s a :=
show (⨅ x ∈ ({a} : set α), s x) = s a, by simp

theorem bInter_union (s t : set α) (u : α → set β) :
  (⋂ x ∈ s ∪ t, u x) = (⋂ x ∈ s, u x) ∩ (⋂ x ∈ t, u x) :=
show (⨅ x ∈ s ∪ t, u x) = (⨅ x ∈ s, u x) ⊓ (⨅ x ∈ t, u x),
  from infi_union

-- TODO(Jeremy): simp [insert_eq, bInter_union] doesn't work
@[simp]
theorem bInter_insert (a : α) (s : set α) (t : α → set β) :
  (⋂ x ∈ insert a s, t x) = t a ∩ (⋂ x ∈ s, t x) :=
begin rw insert_eq, simp [bInter_union] end

-- TODO(Jeremy): another example of where an annotation is needed

theorem bInter_pair (a b : α) (s : α → set β) :
  (⋂ x ∈ ({a, b} : set α), s x) = s a ∩ s b :=
by rw insert_of_has_insert; simp

@[simp]
theorem bUnion_empty (s : α → set β) : (⋃ x ∈ (∅ : set α), s x) = ∅ :=
supr_emptyset

@[simp]
theorem bUnion_univ (s : α → set β) : (⋃ x ∈ @univ α, s x) = ⋃ x, s x :=
supr_univ

@[simp]
theorem bUnion_singleton (a : α) (s : α → set β) : (⋃ x ∈ ({a} : set α), s x) = s a :=
supr_singleton

theorem bUnion_union (s t : set α) (u : α → set β) :
  (⋃ x ∈ s ∪ t, u x) = (⋃ x ∈ s, u x) ∪ (⋃ x ∈ t, u x) :=
supr_union

-- TODO(Jeremy): once again, simp doesn't do it alone.

@[simp]
theorem bUnion_insert (a : α) (s : set α) (t : α → set β) :
  (⋃ x ∈ insert a s, t x) = t a ∪ (⋃ x ∈ s, t x) :=
begin rw [insert_eq], simp [bUnion_union] end

theorem bUnion_pair (a b : α) (s : α → set β) :
  (⋃ x ∈ ({a, b} : set α), s x) = s a ∪ s b :=
by rw insert_of_has_insert; simp

@[reducible]
def sInter (S : set (set α)) : set α := Inf S

prefix `⋂₀`:110 := sInter

theorem mem_sUnion {x : α} {t : set α} {S : set (set α)} (hx : x ∈ t) (ht : t ∈ S) :
  x ∈ ⋃₀ S :=
⟨t, ⟨ht, hx⟩⟩

@[simp]
theorem mem_sUnion_eq {x : α} {S : set (set α)} : x ∈ ⋃₀ S = (∃t ∈ S, x ∈ t) := rfl

-- is this lemma really necessary?
theorem not_mem_of_not_mem_sUnion {x : α} {t : set α} {S : set (set α)}
    (hx : x ∉ ⋃₀ S) (ht : t ∈ S) :
  x ∉ t :=
assume : x ∈ t,
have x ∈ ⋃₀ S, from mem_sUnion this ht,
show false, from hx this

theorem mem_sInter {x : α} {t : set α} {S : set (set α)} (h : ∀ t ∈ S, x ∈ t) : x ∈ ⋂₀ S := h

@[simp]
theorem mem_sInter_eq {x : α} {S : set (set α)} : x ∈ ⋂₀ S = (∀ t ∈ S, x ∈ t) := rfl

theorem sInter_subset_of_mem {S : set (set α)} {t : set α} (tS : t ∈ S) : (⋂₀ S) ⊆ t :=
Inf_le tS

theorem subset_sUnion_of_mem {S : set (set α)} {t : set α} (tS : t ∈ S) : t ⊆ (⋃₀ S) :=
le_Sup tS

theorem sUnion_subset {S : set (set α)} {t : set α} (h : ∀t' ∈ S, t' ⊆ t) : (⋃₀ S) ⊆ t :=
Sup_le h

theorem sUnion_subset_iff {s : set (set α)} {t : set α} : (⋃₀ s) ⊆ t ↔ ∀t' ∈ s, t' ⊆ t :=
⟨assume h t' ht', subset.trans (subset_sUnion_of_mem ht') h, sUnion_subset⟩

theorem subset_sInter {S : set (set α)} {t : set α} (h : ∀t' ∈ S, t ⊆ t') : t ⊆ (⋂₀ S) :=
le_Inf h

@[simp]
theorem sUnion_empty : ⋃₀ ∅ = (∅ : set α) := Sup_empty

@[simp]
theorem sInter_empty : ⋂₀ ∅ = (univ : set α) := Inf_empty

@[simp]
theorem sUnion_singleton (s : set α) : ⋃₀ {s} = s := Sup_singleton

@[simp]
theorem sInter_singleton (s : set α) : ⋂₀ {s} = s := Inf_singleton

theorem sUnion_union (S T : set (set α)) : ⋃₀ (S ∪ T) = ⋃₀ S ∪ ⋃₀ T := Sup_union

theorem sInter_union (S T : set (set α)) : ⋂₀ (S ∪ T) = ⋂₀ S ∩ ⋂₀ T := Inf_union

@[simp]
theorem sUnion_insert (s : set α) (T : set (set α)) : ⋃₀ (insert s T) = s ∪ ⋃₀ T := Sup_insert

@[simp]
theorem sInter_insert (s : set α) (T : set (set α)) : ⋂₀ (insert s T) = s ∩ ⋂₀ T := Inf_insert

@[simp]
theorem sUnion_image (f : α → set β) (s : set α) : ⋃₀ (f '' s) = ⋃ x ∈ s, f x := Sup_image

@[simp]
theorem sInter_image (f : α → set β) (s : set α) : ⋂₀ (f '' s) = ⋂ x ∈ s, f x := Inf_image

theorem compl_sUnion (S : set (set α)) :
  - ⋃₀ S = ⋂₀ (compl '' S) :=
set.ext $ assume x,
  ⟨assume : ¬ (∃s∈S, x ∈ s), assume s h,
    match s, h with
    ._, ⟨t, hs, rfl⟩ := assume h, this ⟨t, hs, h⟩
    end,
    assume : ∀s, s ∈ compl '' S → x ∈ s,
    assume ⟨t, tS, xt⟩, this (compl t) (mem_image_of_mem _ tS) xt⟩

-- classical
theorem sUnion_eq_compl_sInter_compl (S : set (set α)) :
  ⋃₀ S = - ⋂₀ (compl '' S) :=
by rw [←compl_compl (⋃₀ S), compl_sUnion]

-- classical
theorem compl_sInter (S : set (set α)) :
  - ⋂₀ S = ⋃₀ (compl '' S) :=
by rw [sUnion_eq_compl_sInter_compl, compl_compl_image]

-- classical
theorem sInter_eq_comp_sUnion_compl (S : set (set α)) :
   ⋂₀ S = -(⋃₀ (compl '' S)) :=
by rw [←compl_compl (⋂₀ S), compl_sInter]

theorem inter_empty_of_inter_sUnion_empty {s t : set α} {S : set (set α)} (hs : t ∈ S)
    (h : s ∩ ⋃₀ S = ∅) :
  s ∩ t = ∅ :=
eq_empty_of_subset_empty
  begin rw ←h, apply inter_subset_inter_left, apply subset_sUnion_of_mem hs end

theorem Union_eq_sUnion_image (s : α → set β) : (⋃ i, s i) = ⋃₀ (s '' univ) :=
by simp

theorem Inter_eq_sInter_image {α I : Type} (s : I → set α) : (⋂ i, s i) = ⋂₀ (s '' univ) :=
by simp

instance : complete_boolean_algebra (set α) :=
{ set.lattice_set with
  neg                 := compl,
  sub                 := (\),
  inf_neg_eq_bot      := assume s, ext $ assume x, ⟨assume ⟨h, nh⟩, nh h, false.elim⟩,
  sup_neg_eq_top      := assume s, ext $ assume x, ⟨assume h, trivial, assume _, classical.em $ x ∈ s⟩,
  le_sup_inf          := distrib_lattice.le_sup_inf,
  sub_eq              := assume x y, rfl,
  infi_sup_le_sup_Inf := assume s t x, show x ∈ (⋂ b ∈ t, s ∪ b) → x ∈ s ∪ (⋂₀ t),
    by simp; exact assume h,
      or.imp_right
        (assume hn : x ∉ s, assume i hi, or.resolve_left (h i hi) hn)
        (classical.em $ x ∈ s),
  inf_Sup_le_supr_inf := assume s t x, show x ∈ s ∩ (⋃₀ t) → x ∈ (⋃ b ∈ t, s ∩ b), by simp; exact id }

lemma union_sdiff_same {a b : set α} : a ∪ (b \ a) = a ∪ b :=
lattice.sup_sub_same

@[simp]
lemma union_same_compl {a : set α} : a ∪ (-a) = univ :=
sup_neg_eq_top

@[simp]
lemma sdiff_singleton_eq_same {a : α} {s : set α} (h : a ∉ s) : s \ {a} = s :=
sub_eq_left $ eq_empty_of_forall_not_mem $ assume x ⟨ht, ha⟩,
  begin simp at ha, simp [ha] at ht, exact h ht end

@[simp]
lemma insert_sdiff_singleton {a : α} {s : set α} :
  insert a (s \ {a}) = insert a s :=
by simp [insert_eq, union_sdiff_same]

/- inverse image -/

def vimage {α : Type u} {β : Type v} (f : α → β) (s : set β) : set α := {x | f x ∈ s}

section vimage
variables {f : α → β} {g : β → γ}

@[simp] lemma vimage_empty : vimage f ∅ = ∅ := rfl

@[simp] lemma mem_vimage_eq {s : set β} {a : α} : (a ∈ vimage f s) = (f a ∈ s) := rfl

lemma vimage_mono {s t : set β} (h : s ⊆ t) : vimage f s ⊆ vimage f t :=
assume x hx, h hx

lemma monotone_vimage : monotone (vimage f) := assume a b h, vimage_mono h

lemma vimage_image_eq {s : set α} (h : ∀{x y}, f x = f y → x = y) : vimage f (image f s) = s :=
set.ext $ assume x, ⟨assume ⟨y, hy, y_eq⟩, h y_eq ▸ hy, assume hx, mem_image_of_mem _ hx⟩

@[simp] lemma vimage_univ : vimage f univ = univ := rfl

@[simp] lemma vimage_inter {s t : set β} : vimage f (s ∩ t) = vimage f s ∩ vimage f t := rfl

@[simp] lemma vimage_union {s t : set β} : vimage f (s ∪ t) = vimage f s ∪ vimage f t := rfl

@[simp] lemma vimage_compl {s : set β} : vimage f (- s) = - vimage f s := rfl

@[simp] lemma vimage_Union {ι : Sort w} {f : α → β} {s : ι → set β} :
  vimage f (⋃i, s i) = (⋃i, vimage f (s i)) :=
set.ext $ by simp [vimage]

@[simp] lemma vimage_sUnion {f : α → β} {s : set (set β)} :
  vimage f (⋃₀ s) = (⋃t ∈ s, vimage f t) :=
set.ext $ by simp [vimage]

lemma vimage_id {s : set α} : vimage id s = s := rfl

lemma vimage_comp {s : set γ} : vimage (g ∘ f) s = vimage f (vimage g s) := rfl

lemma eq_vimage_subtype_val_iff {p : α → Prop} {s : set (subtype p)} {t : set α} :
  s = vimage subtype.val t ↔ (∀x (h : p x), (⟨x, h⟩ : subtype p) ∈ s ↔ x ∈ t) :=
⟨ assume s_eq x h, by rw [s_eq]; simp
, assume h, set.ext $ assume ⟨x, hx⟩, by simp [h]⟩

end vimage

/- disjoint sets -/

section pairwise
def pairwise_on (s : set α) (r : α → α → Prop) := ∀x∈s, ∀y∈s, x ≠ y → r x y
end pairwise

section disjoint
variable [semilattice_inf_bot α]
def disjoint (a b : α) : Prop := a ⊓ b = ⊥

lemma disjoint_symm {a b : α} : disjoint a b → disjoint b a :=
assume : a ⊓ b = ⊥, show b ⊓ a = ⊥, from this ▸ inf_comm

lemma disjoint_bot_left {a : α} : disjoint ⊥ a := bot_inf_eq
lemma disjoint_bot_right {a : α} : disjoint a ⊥ := inf_bot_eq

end disjoint

end set
