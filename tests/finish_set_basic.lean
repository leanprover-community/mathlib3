/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad

Test examples for "finish".
-/
import data.set.basic logic.basic algebra.lattice tools.auto.finish

open function lattice auto

universes u v w
variables {α : Type u} {β : Type v} {γ : Type w}

namespace set

@[simp]
lemma mem_set_of {a : α} {p : α → Prop} : a ∈ {a | p a} = p a :=
rfl

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl
theorem union_def {s₁ s₂ : set α} : s₁ ∪ s₂ = {a | a ∈ s₁ ∨ a ∈ s₂} := rfl
theorem inter_def {s₁ s₂ : set α} : s₁ ∩ s₂ = {a | a ∈ s₁ ∧ a ∈ s₂} := rfl

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
by finish [subset_def, union_def]

/- old proof
theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
λ x xst, or.elim xst (λ xs, sr xs) (λ xt, tr xt)
-/

theorem inter_subset_left (s t : set α) : s ∩ t ⊆ s := λ x H, and.left H

theorem inter_subset_right (s t : set α) : s ∩ t ⊆ t := λ x H, and.right H

theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
by finish [subset_def, inter_def]

/- old proof
theorem subset_inter {s t r : set α} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
λ x xr, and.intro (rs xr) (rt xr)
-/

instance lattice_set : complete_lattice (set α) :=
{ lattice.complete_lattice .
  le           := has_subset.subset,
  le_refl      := subset.refl,
  le_trans     := assume a b c, subset.trans,
  le_antisymm  := assume a b, subset.antisymm,

  sup          := has_union.union,
  le_sup_left  := subset_union_left,
  le_sup_right := subset_union_right,
  sup_le       := assume a b c, union_subset,

  inf          := set.inter,
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

/- strict subset -/

def strict_subset (a b : set α) := a ⊆ b ∧ a ≠ b

instance : has_ssubset (set α) := ⟨strict_subset⟩

/- empty set -/

attribute [simp] mem_empty_eq empty_subset

theorem set_eq_def (s t : set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
⟨begin intros h x, rw h end, set.ext⟩

theorem empty_def : (∅ : set α) = { x | false } := rfl

theorem exists_mem_of_ne_empty {s : set α} (h : s ≠ ∅) : ∃ x, x ∈ s :=
by finish [set_eq_def]

/- old proof
theorem exists_mem_of_ne_empty {s : set α} (h : s ≠ ∅) : ∃ x, x ∈ s :=
classical.by_contradiction
  (assume : ¬ ∃ x, x ∈ s,
    have ∀ x, x ∉ s, from forall_not_of_not_exists this,
    show false, from h (eq_empty_of_forall_not_mem this))
-/

theorem subset_empty_iff (s : set α) : s ⊆ ∅ ↔ s = ∅ :=
by finish [set_eq_def]

/- old proof
theorem subset_empty_iff (s : set α) : s ⊆ ∅ ↔ s = ∅ :=
iff.intro eq_empty_of_subset_empty (assume xeq, begin rw xeq, apply subset.refl end)
-/

lemma bounded_forall_empty_iff {p : α → Prop} :
  (∀ x ∈ (∅ : set α), p x) ↔ true :=
by finish [iff_def]

/- old proof
lemma bounded_forall_empty_iff {p : α → Prop} :
  (∀ x ∈ (∅ : set α), p x) ↔ true :=
iff.intro (assume H, true.intro) (assume H x H1, absurd H1 (not_mem_empty _))
-/

/- universal set -/

theorem mem_univ (x : α) : x ∈ @univ α :=
by trivial

theorem mem_univ_iff (x : α) : x ∈ @univ α ↔ true := iff.rfl

@[simp]
theorem mem_univ_eq (x : α) : x ∈ @univ α = true := rfl

theorem empty_ne_univ [h : inhabited α] : (∅ : set α) ≠ univ :=
by clarify [set_eq_def]

/- old proof
theorem empty_ne_univ [h : inhabited α] : (∅ : set α) ≠ univ :=
assume H : ∅ = univ,
absurd (mem_univ (inhabited.default α)) (eq.rec_on H (not_mem_empty _))
-/

theorem univ_def : @univ α = { x | true } := rfl

@[simp]
theorem subset_univ (s : set α) : s ⊆ univ := λ x H, trivial

theorem eq_univ_of_univ_subset {s : set α} (h : univ ⊆ s) : s = univ :=
by finish [subset_def, set_eq_def]

/- old proof
theorem eq_univ_of_univ_subset {s : set α} (h : univ ⊆ s) : s = univ :=
eq_of_subset_of_subset (subset_univ s) h
-/

theorem eq_univ_of_forall {s : set α} (H : ∀ x, x ∈ s) : s = univ :=
by finish [set_eq_def]

/-
theorem eq_univ_of_forall {s : set α} (H : ∀ x, x ∈ s) : s = univ :=
ext (assume x, iff.intro (assume H', trivial) (assume H', H x))
-/

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

/- old proof
theorem union_left_comm (s₁ s₂ s₃ : set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
by rw [←union_assoc, union_comm s₁, union_assoc]
-/

theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
by finish [set_eq_def]

/- old proof
theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
by rw [union_assoc, union_comm s₂, union_assoc]
-/

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
by finish [subset_def, set_eq_def, iff_def]

/- old proof
theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
eq_of_subset_of_subset (union_subset h (subset.refl _)) (subset_union_right _ _)
-/

theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by finish [subset_def, set_eq_def, iff_def]

/- old proof
theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by rw [union_comm, union_eq_self_of_subset_left h]
-/

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

/- old proof
theorem nonempty_of_inter_nonempty_right {T : Type} {s t : set T} (h : s ∩ t ≠ ∅) : t ≠ ∅ :=
assume : t = ∅,
have s ∩ t = ∅, from eq.subst (eq.symm this) (inter_empty s),
h this
-/

theorem nonempty_of_inter_nonempty_left {T : Type} {s t : set T} (h : s ∩ t ≠ ∅) : s ≠ ∅ :=
by finish [set_eq_def, iff_def]

/- old proof
theorem nonempty_of_inter_nonempty_left {T : Type} {s t : set T} (h : s ∩ t ≠ ∅) : s ≠ ∅ :=
assume : s = ∅,
have s ∩ t = ∅,
  begin rw this, apply empty_inter end,
h this
-/

theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
by finish [set_eq_def, iff_def]

/- currently this does not work
theorem inter_left_comm' (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
begin simp [inter_assoc, inter_comm] end
-/

/- old proof
theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
by rw [←inter_assoc, inter_comm s₁, inter_assoc]
-/

theorem inter_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
by finish [set_eq_def, iff_def]

/- old proof
theorem inter_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
by rw [inter_assoc, inter_comm s₂, inter_assoc]
-/

theorem inter_univ (a : set α) : a ∩ univ = a :=
ext (assume x, and_true _)

theorem univ_inter (a : set α) : univ ∩ a = a :=
ext (assume x, true_and _)

theorem inter_subset_inter_right {s t : set α} (u : set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by finish [subset_def]

/- old proof
theorem inter_subset_inter_right {s t : set α} (u : set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
assume x, assume xsu, and.intro (H (and.left xsu)) (and.right xsu)
-/

theorem inter_subset_inter_left {s t : set α} (u : set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
assume x, assume xus, and.intro (and.left xus) (H (and.right xus))

/- old proof
theorem inter_subset_inter_left {s t : set α} (u : set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
assume x, assume xus, and.intro (and.left xus) (H (and.right xus))
-/

theorem inter_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∩ t = s :=
by finish [subset_def, set_eq_def, iff_def]

theorem inter_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∩ t = t :=
by finish [subset_def, set_eq_def, iff_def]

/- old proofs
theorem inter_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∩ t = s :=
eq_of_subset_of_subset (inter_subset_left _ _) (subset_inter (subset.refl _) h)

theorem inter_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∩ t = t :=
by rw [inter_comm, inter_eq_self_of_subset_left h]
-/

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

theorem insert_def (x : α) (a : set α) : insert x a = { y | y = x ∨ y ∈ a } := rfl

theorem subset_insert (x : α) (a : set α) : a ⊆ insert x a :=
assume y, assume ys, or.inr ys

theorem mem_insert (x : α) (s : set α) : x ∈ insert x s :=
or.inl rfl

theorem mem_insert_of_mem {x : α} {s : set α} (y : α) : x ∈ s → x ∈ insert y s :=
assume h, or.inr h

theorem eq_or_mem_of_mem_insert {x a : α} {s : set α} : x ∈ insert a s → x = a ∨ x ∈ s :=
assume h, h

theorem mem_of_mem_insert_of_ne {x a : α} {s : set α} (xin : x ∈ insert a s) : x ≠ a → x ∈ s :=
by finish [insert_def]

/- old proof
theorem mem_of_mem_insert_of_ne {x a : α} {s : set α} (xin : x ∈ insert a s) : x ≠ a → x ∈ s :=
or_resolve_right (eq_or_mem_of_mem_insert xin)
-/

@[simp]
theorem mem_insert_iff (x a : α) (s : set α) : x ∈ insert a s ↔ (x = a ∨ x ∈ s) :=
iff.refl _

@[simp]
theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by finish [set_eq_def, iff_def]

/- old proof
@[simp]
theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
ext (assume x, iff.intro
  (begin intro h, cases h with h' h', rw h', exact h, exact h' end)
  (mem_insert_of_mem _))
-/

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
ext (assume c, by simp)

-- TODO(Jeremy): make this automatic
theorem insert_ne_empty (a : α) (s : set α) : insert a s ≠ ∅ :=
begin
  safe [set_eq_def, iff_def],
  have a_1' := a_1 a, finish
end
--begin safe [set_eq_def, iff_def]; have h' := h a; finish end

/- old proof
theorem insert_ne_empty (a : α) (s : set α) : insert a s ≠ ∅ :=
λ h, absurd (mem_insert a s) begin rw h, apply not_mem_empty end
-/

-- useful in proofs by induction
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ insert a s → P x) :
  ∀ x, x ∈ s → P x :=
by finish

/- old proof
theorem forall_of_forall_insert {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ insert a s → P x) :
  ∀ x, x ∈ s → P x :=
λ x xs, h x (mem_insert_of_mem _ xs)
-/

theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ s → P x) (ha : P a) :
  ∀ x, x ∈ insert a s → P x :=
by finish

/- old proof
theorem forall_insert_of_forall {P : α → Prop} {a : α} {s : set α} (h : ∀ x, x ∈ s → P x) (ha : P a) :
  ∀ x, x ∈ insert a s → P x
| ._ (or.inl rfl) := ha
| x  (or.inr p)   := h x p
-/

lemma bounded_forall_insert_iff {P : α → Prop} {a : α} {s : set α} :
  (∀ x ∈ insert a s, P x) ↔ P a ∧ (∀x ∈ s, P x) :=
by finish [iff_def]

/- old proof
lemma bounded_forall_insert_iff {P : α → Prop} {a : α} {s : set α} :
  (∀ x ∈ insert a s, P x) ↔ P a ∧ (∀x ∈ s, P x) :=
⟨assume h, ⟨h a $ mem_insert a s, forall_of_forall_insert h⟩,
  assume ⟨P_a, h⟩, forall_insert_of_forall h P_a⟩
-/

/- properties of singletons -/

theorem singleton_def (a : α) : ({a} : set α) = insert a ∅ := rfl

@[simp]
theorem mem_singleton_iff (a b : α) : a ∈ ({b} : set α) ↔ a = b :=
by finish [singleton_def]

/- old proof
@[simp]
theorem mem_singleton_iff (a b : α) : a ∈ ({b} : set α) ↔ a = b :=
iff.intro
  (assume ainb,
    or.elim (ainb : a = b ∨ false) (λ aeqb, aeqb) (λ f, false.elim f))
  (assume aeqb, or.inl aeqb)
-/

-- TODO: again, annotation needed
@[simp]
theorem mem_singleton (a : α) : a ∈ ({a} : set α) := mem_insert a _

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : set α)) : x = y :=
by finish

/- old proof
theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : set α)) : x = y :=
or.elim (eq_or_mem_of_mem_insert h)
  (assume : x = y, this)
  (assume : x ∈ (∅ : set α), absurd this (not_mem_empty _))
-/

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : set α) :=
by finish

/- old proof
theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : set α) :=
eq.subst (eq.symm H) (mem_singleton y)
-/

theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s :=
by finish [set_eq_def]

/- old proof
theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s :=
ext (assume y, iff.intro
  (assume : y ∈ insert x s,
    or.elim this (assume : y = x, or.inl (or.inl this)) (assume : y ∈ s, or.inr this))
  (assume : y ∈ ({x} : set α) ∪ s,
    or.elim this
      (assume : y ∈ ({x} : set α), or.inl (eq_of_mem_singleton this))
      (assume : y ∈ s, or.inr this)))
-/

@[simp] theorem insert_of_has_insert (x : α) (a : set α) : has_insert.insert x a = insert x a := rfl

@[simp]
theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
by finish

/- old proof
theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
begin rw insert_eq_of_mem, apply mem_singleton end
-/

theorem singleton_ne_empty (a : α) : ({a} : set α) ≠ ∅ := insert_ne_empty _ _

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

/- old proof
theorem eq_sep_of_subset {s t : set α} (ssubt : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
ext (assume x, iff.intro
  (assume : x ∈ s, ⟨ssubt this, this⟩)
  (assume : x ∈ {x ∈ t | x ∈ s}, this^.right))
-/

theorem sep_subset (s : set α) (p : α → Prop) : {x ∈ s | p x} ⊆ s :=
assume x, assume H, and.left H

theorem forall_not_of_sep_empty {s : set α} {p : α → Prop} (h : {x ∈ s | p x} = ∅) :
  ∀ x ∈ s, ¬ p x :=
by finish [set_eq_def]

/- old proof
theorem forall_not_of_sep_empty {s : set α} {p : α → Prop} (h : {x ∈ s | p x} = ∅) :
  ∀ x ∈ s, ¬ p x :=
assume x, assume : x ∈ s, assume : p x,
have x ∈ {x ∈ s | p x}, from ⟨by assumption, this⟩,
show false, from ne_empty_of_mem this h
-/

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

/- old proofs
@[simp]
theorem inter_compl_self (s : set α) : s ∩ -s = ∅ :=
ext (assume x, and_not_self_iff _)

@[simp]
theorem compl_inter_self (s : set α) : -s ∩ s = ∅ :=
ext (assume x, not_and_self_iff _)

@[simp]
theorem compl_empty : -(∅ : set α) = univ :=
ext (assume x, not_false_iff)

@[simp]
theorem compl_union (s t : set α) : -(s ∪ t) = -s ∩ -t :=
ext (assume x, not_or_iff _ _)

theorem compl_compl (s : set α) : -(-s) = s :=
ext (assume x, classical.not_not_iff _)

-- ditto
theorem compl_inter (s t : set α) : -(s ∩ t) = -s ∪ -t :=
ext (assume x, classical.not_and_iff _ _)

@[simp]
theorem compl_univ : -(univ : set α) = ∅ :=
ext (assume x, not_true_iff)

theorem union_eq_compl_compl_inter_compl (s t : set α) : s ∪ t = -(-s ∩ -t) :=
by simp [compl_inter, compl_compl]

theorem inter_eq_compl_compl_union_compl (s t : set α) : s ∩ t = -(-s ∪ -t) :=
by simp [compl_compl]

theorem union_compl_self (s : set α) : s ∪ -s = univ :=
ext (assume x, classical.or_not_self_iff _)

theorem compl_union_self (s : set α) : -s ∪ s = univ :=
ext (assume x, classical.not_or_self_iff _)

theorem compl_comp_compl : compl ∘ compl = @id (set α) :=
funext (λ s, compl_compl s)
-/

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

/- old proofs
theorem union_diff_cancel {s t : set α} (h : s ⊆ t) : s ∪ (t \ s) = t :=
begin rw [diff_eq, union_distrib_left, union_compl_self, inter_univ,
          union_eq_self_of_subset_left h] end

theorem diff_subset (s t : set α) : s \ t ⊆ s := @inter_subset_left _ s _

theorem compl_eq_univ_diff (s : set α) : -s = univ \ s :=
ext (assume x, iff.intro (assume H, and.intro trivial H) (assume H, and.right H))
-/

/- powerset -/

theorem mem_powerset {x s : set α} (h : x ⊆ s) : x ∈ powerset s := h

theorem subset_of_mem_powerset {x s : set α} (h : x ∈ powerset s) : x ⊆ s := h

theorem mem_powerset_iff (x s : set α) : x ∈ powerset s ↔ x ⊆ s := iff.rfl

/- function image -/

section image

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

def mem_image_elim {f : α → β} {s : set α} {C : β → Prop} (h : ∀ (x : α), x ∈ s → C (f x)) :
 ∀{y : β}, y ∈ image f s → C y
| ._ ⟨a, a_in, rfl⟩ := h a a_in

def mem_image_elim_on {f : α → β} {s : set α} {C : β → Prop} {y : β} (h_y : y ∈ image f s)
  (h : ∀ (x : α), x ∈ s → C (f x)) : C y :=
mem_image_elim h h_y

theorem image_eq_image_of_eq_on {f₁ f₂ : α → β} {s : set α} (heq : eq_on f₁ f₂ s) :
  image f₁ s = image f₂ s :=
by finish [set_eq_def, iff_def, mem_image_eq, eq_on]

/- old proof
theorem image_eq_image_of_eq_on {f₁ f₂ : α → β} {s : set α} (heq : eq_on f₁ f₂ s) :
  f₁ ' s = f₂ ' s :=
ext (assume y, iff.intro
  (assume ⟨x, xs, f₁xeq⟩, mem_image xs ((heq x xs)^.symm^.trans f₁xeq))
  (assume ⟨x, xs, f₂xeq⟩, mem_image xs ((heq x xs)^.trans f₂xeq)))
-/

-- TODO(Jeremy): make automatic
lemma image_comp (f : β → γ) (g : α → β) (a : set α) : image (f ∘ g) a = image f (image g a) :=
begin
  safe [set_eq_def, iff_def, mem_image_eq, comp],
  have h' :=  h_1 (g a_1),
  finish
end

/- old proof
lemma image_comp (f : β → γ) (g : α → β) (a : set α) : (f ∘ g) ' a = f ' (g ' a) :=
ext (assume z,
  iff.intro
    (assume ⟨x, (hx₁ : x ∈ a), (hx₂ : f (g x) = z)⟩,
      have g x ∈ g ' a,
        from mem_image hx₁ rfl,
      show z ∈ f ' (g ' a),
        from mem_image this hx₂)
    (assume ⟨y, ⟨x, (hz₁ : x ∈ a), (hz₂ : g x = y)⟩, (hy₂ : f y = z)⟩,
      have f (g x) = z,
        from eq.subst (eq.symm hz₂) hy₂,
      show z ∈ (f ∘ g) ' a,
        from mem_image hz₁ this))
-/

lemma image_subset {a b : set α} (f : α → β) (h : a ⊆ b) : image f a ⊆ image f b :=
by finish [subset_def, mem_image_eq]

/- old_proof
lemma image_subset {a b : set α} (f : α → β) (h : a ⊆ b) : f ' a ⊆ f ' b :=
assume y,
assume ⟨x, hx₁, hx₂⟩,
mem_image (h hx₁) hx₂
-/

theorem image_union (f : α → β) (s t : set α) :
  image f (s ∪ t) = image f s ∪ image f t :=
by finish [set_eq_def, iff_def, mem_image_eq]

/- old proof
theorem image_union (f : α → β) (s t : set α) :
  image f (s ∪ t) = image f s ∪ image f t :=
ext (assume y, iff.intro
  (assume ⟨x, (xst : x ∈ s ∪ t), (fxy : f x = y)⟩,
    or.elim xst
      (assume xs, or.inl (mem_image xs fxy))
      (assume xt, or.inr (mem_image xt fxy)))
  (assume H : y ∈ image f s ∪ image f t,
    or.elim H
      (assume ⟨x, (xs : x ∈ s), (fxy : f x = y)⟩,
        mem_image (or.inl xs) fxy)
      (assume ⟨x, (xt : x ∈ t), (fxy : f x = y)⟩,
        mem_image (or.inr xt) fxy)))
-/

theorem image_empty (f : α → β) : image f ∅ = ∅ :=
by finish [set_eq_def, mem_image_eq]

/- old proof
theorem image_empty (f : α → β) : image f ∅ = ∅ :=
eq_empty_of_forall_not_mem (assume y, assume ⟨x, (h : x ∈ ∅), h'⟩, h)
-/

theorem fix_set_compl (t : set α) : compl t = - t := rfl

-- TODO(Jeremy): there is an issue with - t unfolding to compl t
theorem mem_image_compl (t : set α) (S : set (set α)) :
  t ∈ image compl S ↔ -t ∈ S :=
begin
  safe [mem_image_eq, iff_def, fix_set_compl],
  have h' := h_1 (- t),
  safe [compl_compl],
  rw compl_compl at h, contradiction
  -- TODO(Jeremy): figure out why safe [compl_compl] doesn't solve it.
end

/- old proof
theorem mem_image_compl (t : set α) (S : set (set α)) :
  t ∈ compl ' S ↔ -t ∈ S :=
iff.intro
  (assume ⟨t', (Ht' : t' ∈ S), (Ht : -t' = t)⟩,
    show -t ∈ S, begin rw [←Ht, compl_compl], exact Ht' end)
  (assume : -t ∈ S,
    have -(-t) ∈ compl ' S, from mem_image_of_mem compl this,
    show t ∈ compl ' S, from compl_compl t ▸ this)
-/

theorem image_id (s : set α) : image id s = s :=
by finish [set_eq_def, iff_def, mem_image_eq]

/- old proof
theorem image_id (s : set α) : id ' s = s :=
ext (assume x, iff.intro
  (assume ⟨x', (hx' : x' ∈ s), (x'eq : x' = x)⟩,
    show x ∈ s, begin rw [←x'eq], apply hx' end)
  (assume : x ∈ s, mem_image_of_mem id this))
-/

theorem compl_compl_image (S : set (set α)) :
  image compl (image compl S) = S :=
by rw [←image_comp, compl_comp_compl, image_id]

lemma bounded_forall_image_of_bounded_forall {f : α → β} {s : set α} {p : β → Prop}
  (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ image f s, p y :=
by finish [mem_image_eq]

/- old proof
lemma bounded_forall_image_of_bounded_forall {f : α → β} {s : set α} {p : β → Prop}
  (h : ∀ x ∈ s, p (f x)) : ∀ y ∈ f ' s, p y
| ._ ⟨x, s_in, rfl⟩ := h x s_in
-/

lemma bounded_forall_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ image f s, p y) ↔ (∀ x ∈ s, p (f x)) :=
begin
  safe [mem_image_eq, iff_def],
  have h' := h_1 (f a),
  finish
end

/- old proof
lemma bounded_forall_image_iff {f : α → β} {s : set α} {p : β → Prop} :
  (∀ y ∈ f ' s, p y) ↔ (∀ x ∈ s, p (f x)) :=
iff.intro (assume h x xs, h _ (mem_image_of_mem _ xs)) bounded_forall_image_of_bounded_forall
-/

lemma image_insert_eq {f : α → β} {a : α} {s : set α} :
  image f (insert a s) = insert (f a) (image f s) :=
begin
  safe [set_eq_def, iff_def, mem_image_eq],
  have h' := h_1 a,
  finish
end

/- old proof
lemma image_insert_eq {f : α → β} {a : α} {s : set α} :
  f ' insert a s = insert (f a) (f ' s) :=
set.ext $ assume x, ⟨
  assume h, match x, h with
  | ._, ⟨._, ⟨or.inl rfl, rfl⟩⟩ := mem_insert _ _
  | ._, ⟨b,  ⟨or.inr h,   rfl⟩⟩ := mem_insert_of_mem _ $ mem_image h rfl
  end,
  assume h, match x, h with
  | ._, or.inl rfl          := mem_image (mem_insert _ _) rfl
  | ._, or.inr ⟨x, ⟨_, rfl⟩⟩ := mem_image (mem_insert_of_mem _ ‹x ∈ s›) rfl
  end⟩
-/

end image

-- TODO(Jeremy): stopped here.

end set
