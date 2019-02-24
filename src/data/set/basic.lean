/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Jeremy Avigad, Leonardo de Moura
-/
import tactic.ext tactic.finish data.subtype tactic.interactive
open function


/- set coercion to a type -/
namespace set
instance {α : Type*} : has_coe_to_sort (set α) := ⟨_, λ s, {x // x ∈ s}⟩
end set

section set_coe
universe u
variables {α : Type u}
theorem set.set_coe_eq_subtype (s : set α) :
  coe_sort.{(u+1) (u+2)} s = {x // x ∈ s} := rfl

@[simp] theorem set_coe.forall {s : set α} {p : s → Prop} :
  (∀ x : s, p x) ↔ (∀ x (h : x ∈ s), p ⟨x, h⟩) :=
subtype.forall

@[simp] theorem set_coe.exists {s : set α} {p : s → Prop} :
  (∃ x : s, p x) ↔ (∃ x (h : x ∈ s), p ⟨x, h⟩) :=
subtype.exists

@[simp] theorem set_coe_cast : ∀ {s t : set α} (H' : s = t) (H : @eq (Type u) s t) (x : s),
  cast H x = ⟨x.1, H' ▸ x.2⟩
| s _ rfl _ ⟨x, h⟩ := rfl

theorem set_coe.ext {s : set α} {a b : s} : (↑a : α) = ↑b → a = b :=
subtype.eq

theorem set_coe.ext_iff {s : set α} {a b : s} : (↑a : α) = ↑b ↔ a = b :=
iff.intro set_coe.ext (assume h, h ▸ rfl)

end set_coe

lemma subtype.mem {α : Type*} {s : set α} (p : s) : (p : α) ∈ s := p.property

namespace set
universes u v w x
variables {α : Type u} {β : Type v} {γ : Type w} {ι : Sort x} {a : α} {s t : set α}

instance : inhabited (set α) := ⟨∅⟩

@[extensionality]
theorem ext {a b : set α} (h : ∀ x, x ∈ a ↔ x ∈ b) : a = b :=
funext (assume x, propext (h x))

theorem ext_iff (s t : set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t :=
⟨λ h x, by rw h, ext⟩

@[trans] theorem mem_of_mem_of_subset {α : Type u} {x : α} {s t : set α} (hx : x ∈ s) (h : s ⊆ t) : x ∈ t :=
h hx

/- mem and set_of -/

@[simp] theorem mem_set_of_eq {a : α} {p : α → Prop} : a ∈ {a | p a} = p a := rfl

@[simp] theorem nmem_set_of_eq {a : α} {P : α → Prop} : a ∉ {a : α | P a} = ¬ P a := rfl

@[simp] theorem set_of_mem_eq {s : set α} : {x | x ∈ s} = s := rfl

theorem mem_def {a : α} {s : set α} : a ∈ s ↔ s a := iff.rfl

instance decidable_mem (s : set α) [H : decidable_pred s] : ∀ a, decidable (a ∈ s) := H

instance decidable_set_of (p : α → Prop) [H : decidable_pred p] : decidable_pred {a | p a} := H

@[simp] theorem set_of_subset_set_of {p q : α → Prop} : {a | p a} ⊆ {a | q a} ↔ (∀a, p a → q a) := iff.rfl

@[simp] lemma sep_set_of {α} {p q : α → Prop} : {a ∈ {a | p a } | q a} = {a | p a ∧ q a} :=
rfl

@[simp] lemma set_of_mem {α} {s : set α} : {a | a ∈ s} = s := rfl

/- subset -/

-- TODO(Jeremy): write a tactic to unfold specific instances of generic notation?
theorem subset_def {s t : set α} : (s ⊆ t) = ∀ x, x ∈ s → x ∈ t := rfl

@[refl] theorem subset.refl (a : set α) : a ⊆ a := assume x, id

@[trans] theorem subset.trans {a b c : set α} (ab : a ⊆ b) (bc : b ⊆ c) : a ⊆ c :=
assume x h, bc (ab h)

@[trans] theorem mem_of_eq_of_mem {α : Type u} {x y : α} {s : set α} (hx : x = y) (h : y ∈ s) : x ∈ s :=
hx.symm ▸ h

theorem subset.antisymm {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))

theorem subset.antisymm_iff {a b : set α} : a = b ↔ a ⊆ b ∧ b ⊆ a :=
⟨λ e, e ▸ ⟨subset.refl _, subset.refl _⟩,
 λ ⟨h₁, h₂⟩, subset.antisymm h₁ h₂⟩

-- an alterantive name
theorem eq_of_subset_of_subset {a b : set α} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subset.antisymm h₁ h₂

theorem mem_of_subset_of_mem {s₁ s₂ : set α} {a : α} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ h₂

theorem not_subset : (¬ s ⊆ t) ↔ ∃a, a ∈ s ∧ a ∉ t :=
by simp [subset_def, classical.not_forall]

/- strict subset -/

/-- `s ⊂ t` means that `s` is a strict subset of `t`, that is, `s ⊆ t` but `s ≠ t`. -/
def strict_subset (s t : set α) := s ⊆ t ∧ s ≠ t

instance : has_ssubset (set α) := ⟨strict_subset⟩

theorem ssubset_def : (s ⊂ t) = (s ⊆ t ∧ s ≠ t) := rfl

lemma exists_of_ssubset {α : Type u} {s t : set α} (h : s ⊂ t) : (∃x∈t, x ∉ s) :=
classical.by_contradiction $ assume hn,
  have t ⊆ s, from assume a hat, classical.by_contradiction $ assume has, hn ⟨a, hat, has⟩,
  h.2 $ subset.antisymm h.1 this

lemma ssubset_iff_subset_not_subset {s t : set α} : s ⊂ t ↔ s ⊆ t ∧ ¬ t ⊆ s :=
by split; simp [set.ssubset_def, ne.def, set.subset.antisymm_iff] {contextual := tt}

theorem not_mem_empty (x : α) : ¬ (x ∈ (∅ : set α)) :=
assume h : x ∈ ∅, h

@[simp] theorem not_not_mem [decidable (a ∈ s)] : ¬ (a ∉ s) ↔ a ∈ s :=
not_not

/- empty set -/

theorem empty_def : (∅ : set α) = {x | false} := rfl

@[simp] theorem mem_empty_eq (x : α) : x ∈ (∅ : set α) = false := rfl

@[simp] theorem set_of_false : {a : α | false} = ∅ := rfl

theorem eq_empty_iff_forall_not_mem {s : set α} : s = ∅ ↔ ∀ x, x ∉ s :=
by simp [ext_iff]

theorem ne_empty_of_mem {s : set α} {x : α} (h : x ∈ s) : s ≠ ∅ :=
by { intro hs, rw hs at h, apply not_mem_empty _ h }

@[simp] theorem empty_subset (s : set α) : ∅ ⊆ s :=
assume x, assume h, false.elim h

theorem subset_empty_iff {s : set α} : s ⊆ ∅ ↔ s = ∅ :=
by simp [subset.antisymm_iff]

theorem eq_empty_of_subset_empty {s : set α} : s ⊆ ∅ → s = ∅ :=
subset_empty_iff.1

theorem ne_empty_iff_exists_mem {s : set α} : s ≠ ∅ ↔ ∃ x, x ∈ s :=
by haveI := classical.prop_decidable;
   simp [eq_empty_iff_forall_not_mem]

theorem exists_mem_of_ne_empty {s : set α} : s ≠ ∅ → ∃ x, x ∈ s :=
ne_empty_iff_exists_mem.1

theorem coe_nonempty_iff_ne_empty {s : set α} : nonempty s ↔ s ≠ ∅ :=
nonempty_subtype.trans ne_empty_iff_exists_mem.symm

-- TODO: remove when simplifier stops rewriting `a ≠ b` to `¬ a = b`
theorem not_eq_empty_iff_exists {s : set α} : ¬ (s = ∅) ↔ ∃ x, x ∈ s :=
ne_empty_iff_exists_mem

theorem subset_eq_empty {s t : set α} (h : t ⊆ s) (e : s = ∅) : t = ∅ :=
subset_empty_iff.1 $ e ▸ h

theorem subset_ne_empty {s t : set α} (h : t ⊆ s) : t ≠ ∅ → s ≠ ∅ :=
mt (subset_eq_empty h)

theorem ball_empty_iff {p : α → Prop} :
  (∀ x ∈ (∅ : set α), p x) ↔ true :=
by simp [iff_def]

/- universal set -/

theorem univ_def : @univ α = {x | true} := rfl

@[simp] theorem mem_univ (x : α) : x ∈ @univ α := trivial

theorem empty_ne_univ [h : inhabited α] : (∅ : set α) ≠ univ :=
by simp [ext_iff]

@[simp] theorem subset_univ (s : set α) : s ⊆ univ := λ x H, trivial

theorem univ_subset_iff {s : set α} : univ ⊆ s ↔ s = univ :=
by simp [subset.antisymm_iff]

theorem eq_univ_of_univ_subset {s : set α} : univ ⊆ s → s = univ :=
univ_subset_iff.1

theorem eq_univ_iff_forall {s : set α} : s = univ ↔ ∀ x, x ∈ s :=
by simp [ext_iff]

theorem eq_univ_of_forall {s : set α} : (∀ x, x ∈ s) → s = univ := eq_univ_iff_forall.2

@[simp] lemma univ_eq_empty_iff {α : Type*} : (univ : set α) = ∅ ↔ ¬ nonempty α :=
eq_empty_iff_forall_not_mem.trans ⟨λ H ⟨x⟩, H x trivial, λ H x _, H ⟨x⟩⟩

lemma nonempty_iff_univ_ne_empty {α : Type*} : nonempty α ↔ (univ : set α) ≠ ∅ :=
by classical; exact iff_not_comm.1 univ_eq_empty_iff

lemma exists_mem_of_nonempty (α) : ∀ [nonempty α], ∃x:α, x ∈ (univ : set α)
| ⟨x⟩ := ⟨x, trivial⟩

@[simp] lemma univ_ne_empty {α} [h : nonempty α] : (univ : set α) ≠ ∅ :=
λ e, univ_eq_empty_iff.1 e h

instance univ_decidable : decidable_pred (@set.univ α) :=
λ x, is_true trivial

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

theorem union_comm (a b : set α) : a ∪ b = b ∪ a :=
ext (assume x, or.comm)

theorem union_assoc (a b c : set α) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
ext (assume x, or.assoc)

instance union_is_assoc : is_associative (set α) (∪) :=
⟨union_assoc⟩

instance union_is_comm : is_commutative (set α) (∪) :=
⟨union_comm⟩

theorem union_left_comm (s₁ s₂ s₃ : set α) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
by finish

theorem union_right_comm (s₁ s₂ s₃ : set α) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
by finish

theorem union_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∪ t = t :=
by finish [subset_def, ext_iff, iff_def]

theorem union_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∪ t = s :=
by finish [subset_def, ext_iff, iff_def]

@[simp] theorem subset_union_left (s t : set α) : s ⊆ s ∪ t := λ x, or.inl

@[simp] theorem subset_union_right (s t : set α) : t ⊆ s ∪ t := λ x, or.inr

theorem union_subset {s t r : set α} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
by finish [subset_def, union_def]

@[simp] theorem union_subset_iff {s t u : set α} : s ∪ t ⊆ u ↔ s ⊆ u ∧ t ⊆ u :=
by finish [iff_def, subset_def]

theorem union_subset_union {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ s₂) (h₂ : t₁ ⊆ t₂) : s₁ ∪ t₁ ⊆ s₂ ∪ t₂ :=
by finish [subset_def]

theorem union_subset_union_left {s₁ s₂ : set α} (t) (h : s₁ ⊆ s₂) : s₁ ∪ t ⊆ s₂ ∪ t :=
union_subset_union h (by refl)

theorem union_subset_union_right (s) {t₁ t₂ : set α} (h : t₁ ⊆ t₂) : s ∪ t₁ ⊆ s ∪ t₂ :=
union_subset_union (by refl) h

@[simp] theorem union_empty_iff {s t : set α} : s ∪ t = ∅ ↔ s = ∅ ∧ t = ∅ :=
⟨by finish [ext_iff], by finish [ext_iff]⟩

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

theorem inter_comm (a b : set α) : a ∩ b = b ∩ a :=
ext (assume x, and.comm)

theorem inter_assoc (a b c : set α) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
ext (assume x, and.assoc)

instance inter_is_assoc : is_associative (set α) (∩) :=
⟨inter_assoc⟩

instance inter_is_comm : is_commutative (set α) (∩) :=
⟨inter_comm⟩

theorem inter_left_comm (s₁ s₂ s₃ : set α) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
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

@[simp] theorem inter_univ (a : set α) : a ∩ univ = a :=
ext (assume x, and_true _)

@[simp] theorem univ_inter (a : set α) : univ ∩ a = a :=
ext (assume x, true_and _)

theorem inter_subset_inter_left {s t : set α} (u : set α) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
by finish [subset_def]

theorem inter_subset_inter_right {s t : set α} (u : set α) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
by finish [subset_def]

theorem inter_subset_inter {s₁ s₂ t₁ t₂ : set α} (h₁ : s₁ ⊆ t₁) (h₂ : s₂ ⊆ t₂) : s₁ ∩ s₂ ⊆ t₁ ∩ t₂ :=
by finish [subset_def]

theorem inter_eq_self_of_subset_left {s t : set α} (h : s ⊆ t) : s ∩ t = s :=
by finish [subset_def, ext_iff, iff_def]

theorem inter_eq_self_of_subset_right {s t : set α} (h : t ⊆ s) : s ∩ t = t :=
by finish [subset_def, ext_iff, iff_def]

theorem union_inter_cancel_left {s t : set α} : (s ∪ t) ∩ s = s :=
by finish [ext_iff, iff_def]

theorem union_inter_cancel_right {s t : set α} : (s ∪ t) ∩ t = t :=
by finish [ext_iff, iff_def]

-- TODO(Mario): remove?
theorem nonempty_of_inter_nonempty_right {s t : set α} (h : s ∩ t ≠ ∅) : t ≠ ∅ :=
by finish [ext_iff, iff_def]

theorem nonempty_of_inter_nonempty_left {s t : set α} (h : s ∩ t ≠ ∅) : s ≠ ∅ :=
by finish [ext_iff, iff_def]

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

@[simp] theorem mem_insert_iff {x a : α} {s : set α} : x ∈ insert a s ↔ (x = a ∨ x ∈ s) := iff.rfl

@[simp] theorem insert_eq_of_mem {a : α} {s : set α} (h : a ∈ s) : insert a s = s :=
by finish [ext_iff, iff_def]

theorem insert_subset : insert a s ⊆ t ↔ (a ∈ t ∧ s ⊆ t) :=
by simp [subset_def, or_imp_distrib, forall_and_distrib]

theorem insert_subset_insert (h : s ⊆ t) : insert a s ⊆ insert a t :=
assume a', or.imp_right (@h a')

theorem ssubset_insert {s : set α} {a : α} (h : a ∉ s) : s ⊂ insert a s :=
by finish [ssubset_def, ext_iff]

theorem insert_comm (a b : α) (s : set α) : insert a (insert b s) = insert b (insert a s) :=
ext $ by simp [or.left_comm]

theorem insert_union : insert a s ∪ t = insert a (s ∪ t) :=
ext $ assume a, by simp [or.comm, or.left_comm]

@[simp] theorem union_insert : s ∪ insert a t = insert a (s ∪ t) :=
ext $ assume a, by simp [or.comm, or.left_comm]

-- TODO(Jeremy): make this automatic
theorem insert_ne_empty (a : α) (s : set α) : insert a s ≠ ∅ :=
by safe [ext_iff, iff_def]; have h' := a_1 a; finish

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

@[simp] theorem mem_singleton_iff {a b : α} : a ∈ ({b} : set α) ↔ a = b :=
by finish [singleton_def]

-- TODO: again, annotation needed
@[simp] theorem mem_singleton (a : α) : a ∈ ({a} : set α) := by finish

theorem eq_of_mem_singleton {x y : α} (h : x ∈ ({y} : set α)) : x = y :=
by finish

@[simp] theorem singleton_eq_singleton_iff {x y : α} : {x} = ({y} : set α) ↔ x = y :=
by finish [ext_iff, iff_def]

theorem mem_singleton_of_eq {x y : α} (H : x = y) : x ∈ ({y} : set α) :=
by finish

theorem insert_eq (x : α) (s : set α) : insert x s = ({x} : set α) ∪ s :=
by finish [ext_iff, or_comm]

@[simp] theorem pair_eq_singleton (a : α) : ({a, a} : set α) = {a} :=
by finish

@[simp] theorem singleton_ne_empty (a : α) : ({a} : set α) ≠ ∅ := insert_ne_empty _ _

@[simp] theorem singleton_subset_iff {a : α} {s : set α} : {a} ⊆ s ↔ a ∈ s :=
⟨λh, h (by simp), λh b e, by simp at e; simp [*]⟩

theorem set_compr_eq_eq_singleton {a : α} : {b | b = a} = {a} :=
ext $ by simp

@[simp] theorem union_singleton : s ∪ {a} = insert a s :=
by simp [singleton_def]

@[simp] theorem singleton_union : {a} ∪ s = insert a s :=
by rw [union_comm, union_singleton]

theorem singleton_inter_eq_empty : {a} ∩ s = ∅ ↔ a ∉ s :=
by simp [eq_empty_iff_forall_not_mem]

theorem inter_singleton_eq_empty : s ∩ {a} = ∅ ↔ a ∉ s :=
by rw [inter_comm, singleton_inter_eq_empty]

/- separation -/

theorem mem_sep {s : set α} {p : α → Prop} {x : α} (xs : x ∈ s) (px : p x) : x ∈ {x ∈ s | p x} :=
⟨xs, px⟩

@[simp] theorem mem_sep_eq {s : set α} {p : α → Prop} {x : α} : x ∈ {x ∈ s | p x} = (x ∈ s ∧ p x) := rfl

theorem mem_sep_iff {s : set α} {p : α → Prop} {x : α} : x ∈ {x ∈ s | p x} ↔ x ∈ s ∧ p x :=
iff.rfl

theorem eq_sep_of_subset {s t : set α} (ssubt : s ⊆ t) : s = {x ∈ t | x ∈ s} :=
by finish [ext_iff, iff_def, subset_def]

theorem sep_subset (s : set α) (p : α → Prop) : {x ∈ s | p x} ⊆ s :=
assume x, and.left

theorem forall_not_of_sep_empty {s : set α} {p : α → Prop} (h : {x ∈ s | p x} = ∅) :
  ∀ x ∈ s, ¬ p x :=
by finish [ext_iff]

@[simp] lemma sep_univ {α} {p : α → Prop} : {a ∈ (univ : set α) | p a} = {a | p a} :=
set.ext $ by simp

/- complement -/

theorem mem_compl {s : set α} {x : α} (h : x ∉ s) : x ∈ -s := h

lemma compl_set_of {α} (p : α → Prop) : - {a | p a} = { a | ¬ p a } := rfl

theorem not_mem_of_mem_compl {s : set α} {x : α} (h : x ∈ -s) : x ∉ s := h

@[simp] theorem mem_compl_eq (s : set α) (x : α) : x ∈ -s = (x ∉ s) := rfl

theorem mem_compl_iff (s : set α) (x : α) : x ∈ -s ↔ x ∉ s := iff.rfl

@[simp] theorem inter_compl_self (s : set α) : s ∩ -s = ∅ :=
by finish [ext_iff]

@[simp] theorem compl_inter_self (s : set α) : -s ∩ s = ∅ :=
by finish [ext_iff]

@[simp] theorem compl_empty : -(∅ : set α) = univ :=
by finish [ext_iff]

@[simp] theorem compl_union (s t : set α) : -(s ∪ t) = -s ∩ -t :=
by finish [ext_iff]

@[simp] theorem compl_compl (s : set α) : -(-s) = s :=
by finish [ext_iff]

-- ditto
theorem compl_inter (s t : set α) : -(s ∩ t) = -s ∪ -t :=
by finish [ext_iff]

@[simp] theorem compl_univ : -(univ : set α) = ∅ :=
by finish [ext_iff]

theorem union_eq_compl_compl_inter_compl (s t : set α) : s ∪ t = -(-s ∩ -t) :=
by simp [compl_inter, compl_compl]

theorem inter_eq_compl_compl_union_compl (s t : set α) : s ∩ t = -(-s ∪ -t) :=
by simp [compl_compl]

@[simp] theorem union_compl_self (s : set α) : s ∪ -s = univ :=
by finish [ext_iff]

@[simp] theorem compl_union_self (s : set α) : -s ∪ s = univ :=
by finish [ext_iff]

theorem compl_comp_compl : compl ∘ compl = @id (set α) :=
funext compl_compl

theorem compl_subset_comm {s t : set α} : -s ⊆ t ↔ -t ⊆ s :=
by haveI := classical.prop_decidable; exact
forall_congr (λ a, not_imp_comm)

lemma compl_subset_compl {s t : set α} : -s ⊆ -t ↔ t ⊆ s :=
by rw [compl_subset_comm, compl_compl]

theorem compl_subset_iff_union {s t : set α} : -s ⊆ t ↔ s ∪ t = univ :=
iff.symm $ eq_univ_iff_forall.trans $ forall_congr $ λ a,
by haveI := classical.prop_decidable; exact or_iff_not_imp_left

theorem subset_compl_comm {s t : set α} : s ⊆ -t ↔ t ⊆ -s :=
forall_congr $ λ a, imp_not_comm

theorem subset_compl_iff_disjoint {s t : set α} : s ⊆ -t ↔ s ∩ t = ∅ :=
iff.trans (forall_congr $ λ a, and_imp.symm) subset_empty_iff

theorem inter_subset (a b c : set α) : a ∩ b ⊆ c ↔ a ⊆ -b ∪ c :=
begin
  haveI := classical.prop_decidable,
  split,
  { intros h x xa, by_cases h' : x ∈ b, simp [h ⟨xa, h'⟩], simp [h'] },
  intros h x, rintro ⟨xa, xb⟩, cases h xa, contradiction, assumption
end

/- set difference -/

theorem diff_eq (s t : set α) : s \ t = s ∩ -t := rfl

@[simp] theorem mem_diff {s t : set α} (x : α) : x ∈ s \ t ↔ x ∈ s ∧ x ∉ t := iff.rfl

theorem mem_diff_of_mem {s t : set α} {x : α} (h1 : x ∈ s) (h2 : x ∉ t) : x ∈ s \ t :=
⟨h1, h2⟩

theorem mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∈ s :=
h.left

theorem not_mem_of_mem_diff {s t : set α} {x : α} (h : x ∈ s \ t) : x ∉ t :=
h.right

theorem union_diff_cancel {s t : set α} (h : s ⊆ t) : s ∪ (t \ s) = t :=
by finish [ext_iff, iff_def, subset_def]

theorem union_diff_cancel_left {s t : set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ s = t :=
by finish [ext_iff, iff_def, subset_def]

theorem union_diff_cancel_right {s t : set α} (h : s ∩ t ⊆ ∅) : (s ∪ t) \ t = s :=
by finish [ext_iff, iff_def, subset_def]

theorem union_diff_left {s t : set α} : (s ∪ t) \ s = t \ s :=
by finish [ext_iff, iff_def]

theorem union_diff_right {s t : set α} : (s ∪ t) \ t = s \ t :=
by finish [ext_iff, iff_def]

theorem union_diff_distrib {s t u : set α} : (s ∪ t) \ u = s \ u ∪ t \ u :=
inter_distrib_right _ _ _

theorem inter_diff_assoc (a b c : set α) : (a ∩ b) \ c = a ∩ (b \ c) :=
inter_assoc _ _ _

theorem inter_diff_self (a b : set α) : a ∩ (b \ a) = ∅ :=
by finish [ext_iff]

theorem inter_union_diff (s t : set α) : (s ∩ t) ∪ (s \ t) = s :=
by finish [ext_iff, iff_def]

theorem diff_subset (s t : set α) : s \ t ⊆ s :=
by finish [subset_def]

theorem diff_subset_diff {s₁ s₂ t₁ t₂ : set α} : s₁ ⊆ s₂ → t₂ ⊆ t₁ → s₁ \ t₁ ⊆ s₂ \ t₂ :=
by finish [subset_def]

theorem diff_subset_diff_left {s₁ s₂ t : set α} (h : s₁ ⊆ s₂) : s₁ \ t ⊆ s₂ \ t :=
diff_subset_diff h (by refl)

theorem diff_subset_diff_right {s t u : set α} (h : t ⊆ u) : s \ u ⊆ s \ t :=
diff_subset_diff (subset.refl s) h

theorem compl_eq_univ_diff (s : set α) : -s = univ \ s :=
by finish [ext_iff]

@[simp] lemma empty_diff {α : Type*} (s : set α) : (∅ \ s : set α) = ∅ :=
eq_empty_of_subset_empty $ assume x ⟨hx, _⟩, hx

theorem diff_eq_empty {s t : set α} : s \ t = ∅ ↔ s ⊆ t :=
⟨assume h x hx, classical.by_contradiction $ assume : x ∉ t, show x ∈ (∅ : set α), from h ▸ ⟨hx, this⟩,
  assume h, eq_empty_of_subset_empty $ assume x ⟨hx, hnx⟩, hnx $ h hx⟩

@[simp] theorem diff_empty {s : set α} : s \ ∅ = s :=
ext $ assume x, ⟨assume ⟨hx, _⟩, hx, assume h, ⟨h, not_false⟩⟩

theorem diff_diff {u : set α} : s \ t \ u = s \ (t ∪ u) :=
ext $ by simp [not_or_distrib, and.comm, and.left_comm]

lemma diff_subset_iff {s t u : set α} : s \ t ⊆ u ↔ s ⊆ t ∪ u :=
⟨assume h x xs, classical.by_cases or.inl (assume nxt, or.inr (h ⟨xs, nxt⟩)),
 assume h x ⟨xs, nxt⟩, or.resolve_left (h xs) nxt⟩

lemma diff_subset_comm {s t u : set α} : s \ t ⊆ u ↔ s \ u ⊆ t :=
by rw [diff_subset_iff, diff_subset_iff, union_comm]

@[simp] theorem insert_diff (h : a ∈ t) : insert a s \ t = s \ t :=
ext $ by intro; constructor; simp [or_imp_distrib, h] {contextual := tt}

theorem union_diff_self {s t : set α} : s ∪ (t \ s) = s ∪ t :=
by finish [ext_iff, iff_def]

theorem diff_union_self {s t : set α} : (s \ t) ∪ t = s ∪ t :=
by rw [union_comm, union_diff_self, union_comm]

theorem diff_inter_self {a b : set α} : (b \ a) ∩ a = ∅ :=
ext $ by simp [iff_def] {contextual:=tt}

theorem diff_eq_self {s t : set α} : s \ t = s ↔ t ∩ s ⊆ ∅ :=
by finish [ext_iff, iff_def, subset_def]

@[simp] theorem diff_singleton_eq_self {a : α} {s : set α} (h : a ∉ s) : s \ {a} = s :=
diff_eq_self.2 $ by simp [singleton_inter_eq_empty.2 h]

@[simp] theorem insert_diff_singleton {a : α} {s : set α} :
  insert a (s \ {a}) = insert a s :=
by simp [insert_eq, union_diff_self, -union_singleton, -singleton_union]

@[simp] lemma diff_self {s : set α} : s \ s = ∅ := ext $ by simp

/- powerset -/

theorem mem_powerset {x s : set α} (h : x ⊆ s) : x ∈ powerset s := h

theorem subset_of_mem_powerset {x s : set α} (h : x ∈ powerset s) : x ⊆ s := h

theorem mem_powerset_iff (x s : set α) : x ∈ powerset s ↔ x ⊆ s := iff.rfl

/- inverse image -/

/-- The preimage of `s : set β` by `f : α → β`, written `f ⁻¹' s`,
  is the set of `x : α` such that `f x ∈ s`. -/
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
 assume h, ext $ assume ⟨x, hx⟩, by simp [h]⟩

end preimage

/- function image -/

section image

infix ` '' `:80 := image

/-- Two functions `f₁ f₂ : α → β` are equal on `s`
  if `f₁ x = f₂ x` for all `x ∈ a`. -/
@[reducible] def eq_on (f1 f2 : α → β) (a : set α) : Prop :=
∀ x ∈ a, f1 x = f2 x

-- TODO(Jeremy): use bounded exists in image

theorem mem_image_iff_bex {f : α → β} {s : set α} {y : β} :
  y ∈ f '' s ↔ ∃ x (_ : x ∈ s), f x = y := bex_def.symm

theorem mem_image_eq (f : α → β) (s : set α) (y: β) : y ∈ f '' s = ∃ x, x ∈ s ∧ f x = y := rfl

@[simp] theorem mem_image (f : α → β) (s : set α) (y : β) : y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y := iff.rfl

theorem mem_image_of_mem (f : α → β) {x : α} {a : set α} (h : x ∈ a) : f x ∈ f '' a :=
⟨_, h, rfl⟩

theorem mem_image_of_injective {f : α → β} {a : α} {s : set α} (hf : injective f) :
  f a ∈ f '' s ↔ a ∈ s :=
iff.intro
  (assume ⟨b, hb, eq⟩, (hf eq) ▸ hb)
  (assume h, mem_image_of_mem _ h)

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

theorem mem_image_elim {f : α → β} {s : set α} {C : β → Prop} (h : ∀ (x : α), x ∈ s → C (f x)) :
 ∀{y : β}, y ∈ f '' s → C y
| ._ ⟨a, a_in, rfl⟩ := h a a_in

theorem mem_image_elim_on {f : α → β} {s : set α} {C : β → Prop} {y : β} (h_y : y ∈ f '' s)
  (h : ∀ (x : α), x ∈ s → C (f x)) : C y :=
mem_image_elim h h_y

@[congr] lemma image_congr {f g : α → β} {s : set α}
  (h : ∀a∈s, f a = g a) : f '' s = g '' s :=
by safe [ext_iff, iff_def]

theorem image_eq_image_of_eq_on {f₁ f₂ : α → β} {s : set α} (heq : eq_on f₁ f₂ s) :
  f₁ '' s = f₂ '' s :=
image_congr heq

theorem image_comp (f : β → γ) (g : α → β) (a : set α) : (f ∘ g) '' a = f '' (g '' a) :=
subset.antisymm
  (ball_image_of_ball $ assume a ha, mem_image_of_mem _ $ mem_image_of_mem _ ha)
  (ball_image_of_ball $ ball_image_of_ball $ assume a ha, mem_image_of_mem _ ha)
/- Proof is removed as it uses generated names
TODO(Jeremy): make automatic,
begin
  safe [ext_iff, iff_def, mem_image, (∘)],
  have h' := h_2 (g a_2),
  finish
end -/

theorem image_subset {a b : set α} (f : α → β) (h : a ⊆ b) : f '' a ⊆ f '' b :=
by finish [subset_def, mem_image_eq]

theorem image_union (f : α → β) (s t : set α) :
  f '' (s ∪ t) = f '' s ∪ f '' t :=
by finish [ext_iff, iff_def, mem_image_eq]

@[simp] theorem image_empty (f : α → β) : f '' ∅ = ∅ := ext $ by simp

theorem image_inter_on {f : α → β} {s t : set α} (h : ∀x∈t, ∀y∈s, f x = f y → x = y) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
subset.antisymm
  (assume b ⟨⟨a₁, ha₁, h₁⟩, ⟨a₂, ha₂, h₂⟩⟩,
    have a₂ = a₁, from h _ ha₂ _ ha₁ (by simp *),
    ⟨a₁, ⟨ha₁, this ▸ ha₂⟩, h₁⟩)
  (subset_inter (mono_image $ inter_subset_left _ _) (mono_image $ inter_subset_right _ _))

theorem image_inter {f : α → β} {s t : set α} (H : injective f) :
  f '' s ∩ f '' t = f '' (s ∩ t) :=
image_inter_on (assume x _ y _ h, H h)

theorem image_univ_of_surjective {ι : Type*} {f : ι → β} (H : surjective f) : f '' univ = univ :=
eq_univ_of_forall $ by simp [image]; exact H

@[simp] theorem image_singleton {f : α → β} {a : α} : f '' {a} = {f a} :=
ext $ λ x, by simp [image]; rw eq_comm

@[simp] lemma image_eq_empty {α β} {f : α → β} {s : set α} : f '' s = ∅ ↔ s = ∅ :=
by simp only [eq_empty_iff_forall_not_mem]; exact
⟨λ H a ha, H _ ⟨_, ha, rfl⟩, λ H b ⟨_, ha, _⟩, H _ ha⟩

lemma inter_singleton_ne_empty {α : Type*} {s : set α} {a : α} : s ∩ {a} ≠ ∅ ↔ a ∈ s :=
by finish  [set.inter_singleton_eq_empty]

theorem fix_set_compl (t : set α) : compl t = - t := rfl

-- TODO(Jeremy): there is an issue with - t unfolding to compl t
theorem mem_compl_image (t : set α) (S : set (set α)) :
  t ∈ compl '' S ↔ -t ∈ S :=
begin
  suffices : ∀ x, -x = t ↔ -t = x, {simp [fix_set_compl, this]},
  intro x, split; { intro e, subst e, simp }
end

@[simp] theorem image_id (s : set α) : id '' s = s := ext $ by simp

theorem compl_compl_image (S : set (set α)) :
  compl '' (compl '' S) = S :=
by rw [← image_comp, compl_comp_compl, image_id]

theorem image_insert_eq {f : α → β} {a : α} {s : set α} :
  f '' (insert a s) = insert (f a) (f '' s) :=
ext $ by simp [and_or_distrib_left, exists_or_distrib, eq_comm, or_comm, and_comm]

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

theorem image_compl_subset {f : α → β} {s : set α} (H : injective f) : f '' -s ⊆ -(f '' s) :=
subset_compl_iff_disjoint.2 $ by simp [image_inter H]

theorem subset_image_compl {f : α → β} {s : set α} (H : surjective f) : -(f '' s) ⊆ f '' -s :=
compl_subset_iff_union.2 $
by rw ← image_union; simp [image_univ_of_surjective H]

theorem image_compl_eq {f : α → β} {s : set α} (H : bijective f) : f '' -s = -(f '' s) :=
subset.antisymm (image_compl_subset H.1) (subset_image_compl H.2)

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

theorem preimage_image_eq {f : α → β} (s : set α) (h : injective f) : f ⁻¹' (f '' s) = s :=
subset.antisymm
  (λ x ⟨y, hy, e⟩, h e ▸ hy)
  (subset_preimage_image f s)

theorem image_preimage_eq {f : α → β} {s : set β} (h : surjective f) : f '' (f ⁻¹' s) = s :=
subset.antisymm
  (image_preimage_subset f s)
  (λ x hx, let ⟨y, e⟩ := h x in ⟨y, (e.symm ▸ hx : f y ∈ s), e⟩)

lemma preimage_eq_preimage {f : β → α} (hf : surjective f) : f ⁻¹' s = preimage f t ↔ s = t :=
iff.intro
  (assume eq, by rw [← @image_preimage_eq β α f s hf, ← @image_preimage_eq β α f t hf, eq])
  (assume eq, eq ▸ rfl)

lemma surjective_preimage {f : β → α} (hf : surjective f) : injective (preimage f) :=
assume s t, (preimage_eq_preimage hf).1

theorem compl_image : image (@compl α) = preimage compl :=
image_eq_preimage_of_inverse compl_compl compl_compl

theorem compl_image_set_of {α : Type u} {p : set α → Prop} :
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

lemma injective_image {f : α → β} (hf : injective f) : injective (('') f) :=
assume s t, (image_eq_image hf).1

lemma prod_quotient_preimage_eq_image [s : setoid α] (g : quotient s → β) {h : α → β}
  (Hh : h = g ∘ quotient.mk) (r : set (β × β)) :
  {x : quotient s × quotient s | (g x.1, g x.2) ∈ r} =
  (λ a : α × α, (⟦a.1⟧, ⟦a.2⟧)) '' ((λ a : α × α, (h a.1, h a.2)) ⁻¹' r) :=
Hh.symm ▸ set.ext (λ ⟨a₁, a₂⟩, ⟨quotient.induction_on₂ a₁ a₂
  (λ a₁ a₂ h, ⟨(a₁, a₂), h, rfl⟩),
  λ ⟨⟨b₁, b₂⟩, h₁, h₂⟩, show (g a₁, g a₂) ∈ r, from
  have h₃ : ⟦b₁⟧ = a₁ ∧ ⟦b₂⟧ = a₂ := prod.ext_iff.1 h₂,
    h₃.1 ▸ h₃.2 ▸ h₁⟩)

def image_factorization (f : α → β) (s : set α) : s → f '' s :=
λ p, ⟨f p.1, mem_image_of_mem f p.2⟩

lemma image_factorization_eq {f : α → β} {s : set α} :
  subtype.val ∘ image_factorization f s = f ∘ subtype.val :=
funext $ λ p, rfl

lemma surjective_onto_image {f : α → β} {s : set α} :
  surjective (image_factorization f s) :=
λ ⟨_, ⟨a, ha, rfl⟩⟩, ⟨⟨a, ha⟩, rfl⟩

end image

theorem univ_eq_true_false : univ = ({true, false} : set Prop) :=
eq.symm $ eq_univ_of_forall $ classical.cases (by simp) (by simp)

section range
variables {f : ι → α}
open function

/-- Range of a function.

This function is more flexible than `f '' univ`, as the image requires that the domain is in Type
and not an arbitrary Sort. -/
def range (f : ι → α) : set α := {x | ∃y, f y = x}

@[simp] theorem mem_range {x : α} : x ∈ range f ↔ ∃ y, f y = x := iff.rfl

theorem mem_range_self (i : ι) : f i ∈ range f := ⟨i, rfl⟩

theorem forall_range_iff {p : α → Prop} : (∀ a ∈ range f, p a) ↔ (∀ i, p (f i)) :=
⟨assume h i, h (f i) (mem_range_self _), assume h a ⟨i, (hi : f i = a)⟩, hi ▸ h i⟩

theorem exists_range_iff {p : α → Prop} : (∃ a ∈ range f, p a) ↔ (∃ i, p (f i)) :=
⟨assume ⟨a, ⟨i, eq⟩, h⟩, ⟨i, eq.symm ▸ h⟩, assume ⟨i, h⟩, ⟨f i, mem_range_self _, h⟩⟩

theorem range_iff_surjective : range f = univ ↔ surjective f :=
eq_univ_iff_forall

@[simp] theorem range_id : range (@id α) = univ := range_iff_surjective.2 surjective_id

@[simp] theorem image_univ {ι : Type*} {f : ι → β} : f '' univ = range f :=
ext $ by simp [image, range]

theorem image_subset_range {ι : Type*} (f : ι → β) (s : set ι) : f '' s ⊆ range f :=
by rw ← image_univ; exact image_subset _ (subset_univ _)

theorem range_comp {g : α → β} : range (g ∘ f) = g '' range f :=
subset.antisymm
  (forall_range_iff.mpr $ assume i, mem_image_of_mem g (mem_range_self _))
  (ball_image_iff.mpr $ forall_range_iff.mpr mem_range_self)

theorem range_subset_iff {ι : Type*} {f : ι → β} {s : set β} : range f ⊆ s ↔ ∀ y, f y ∈ s :=
forall_range_iff

lemma nonempty_of_nonempty_range {α : Type*} {β : Type*} {f : α → β} (H : ¬range f = ∅) : nonempty α :=
begin
  cases exists_mem_of_ne_empty H with x h,
  cases mem_range.1 h with y _,
  exact ⟨y⟩
end

@[simp] lemma range_eq_empty {α : Type u} {β : Type v} {f : α → β} : range f = ∅ ↔ ¬ nonempty α :=
by rw ← set.image_univ; simp [-set.image_univ]

theorem image_preimage_eq_inter_range {f : α → β} {t : set β} :
  f '' (f ⁻¹' t) = t ∩ range f :=
ext $ assume x, ⟨assume ⟨x, hx, heq⟩, heq ▸ ⟨hx, mem_range_self _⟩,
  assume ⟨hx, ⟨y, h_eq⟩⟩, h_eq ▸ mem_image_of_mem f $
    show y ∈ f ⁻¹' t, by simp [preimage, h_eq, hx]⟩

lemma image_preimage_eq_of_subset {f : α → β} {s : set β} (hs : s ⊆ range f) :
  f '' (f ⁻¹' s) = s :=
by rw [image_preimage_eq_inter_range, inter_eq_self_of_subset_left hs]

theorem preimage_inter_range {f : α → β} {s : set β} : f ⁻¹' (s ∩ range f) = f ⁻¹' s :=
set.ext $ λ x, and_iff_left ⟨x, rfl⟩

theorem preimage_image_preimage {f : α → β} {s : set β} :
  f ⁻¹' (f '' (f ⁻¹' s)) = f ⁻¹' s :=
by rw [image_preimage_eq_inter_range, preimage_inter_range]

@[simp] theorem quot_mk_range_eq [setoid α] : range (λx : α, ⟦x⟧) = univ :=
range_iff_surjective.2 quot.exists_rep

lemma range_const_subset {c : β} : range (λx:α, c) ⊆ {c} :=
range_subset_iff.2 $ λ x, or.inl rfl

@[simp] lemma range_const [h : nonempty α] {c : β} : range (λx:α, c) = {c} :=
begin
  refine subset.antisymm range_const_subset (λy hy, _),
  rw set.mem_singleton_iff.1 hy,
  rcases exists_mem_of_nonempty α with ⟨x, _⟩,
  exact mem_range_self x
end

def range_factorization (f : ι → β) : ι → range f :=
λ i, ⟨f i, mem_range_self i⟩

lemma range_factorization_eq {f : ι → β} :
  subtype.val ∘ range_factorization f = f :=
funext $ λ i, rfl

lemma surjective_onto_range : surjective (range_factorization f) :=
λ ⟨_, ⟨i, rfl⟩⟩, ⟨i, rfl⟩

end range

/-- The set `s` is pairwise `r` if `r x y` for all *distinct* `x y ∈ s`. -/
def pairwise_on (s : set α) (r : α → α → Prop) := ∀ x ∈ s, ∀ y ∈ s, x ≠ y → r x y

theorem pairwise_on.mono {s t : set α} {r}
  (h : t ⊆ s) (hp : pairwise_on s r) : pairwise_on t r :=
λ x xt y yt, hp x (h xt) y (h yt)

theorem pairwise_on.mono' {s : set α} {r r' : α → α → Prop}
  (H : ∀ a b, r a b → r' a b) (hp : pairwise_on s r) : pairwise_on s r' :=
λ x xs y ys h, H _ _ (hp x xs y ys h)

end set

/- image and preimage on subtypes -/

namespace subtype

variable {α : Type*}

lemma val_image {p : α → Prop} {s : set (subtype p)} :
  subtype.val '' s = {x | ∃h : p x, (⟨x, h⟩ : subtype p) ∈ s} :=
set.ext $ assume a,
⟨assume ⟨⟨a', ha'⟩, in_s, h_eq⟩, h_eq ▸ ⟨ha', in_s⟩,
  assume ⟨ha, in_s⟩, ⟨⟨a, ha⟩, in_s, rfl⟩⟩

@[simp] lemma val_range {p : α → Prop} :
  set.range (@subtype.val _ p) = {x | p x} :=
by rw ← set.image_univ; simp [-set.image_univ, val_image]
theorem val_image_subset (s : set α) (t : set (subtype s)) : t.image val ⊆ s :=
λ x ⟨y, yt, yvaleq⟩, by rw ←yvaleq; exact y.property

theorem val_image_univ (s : set α) : @val _ s '' set.univ = s :=
set.eq_of_subset_of_subset (val_image_subset _ _) (λ x xs, ⟨⟨x, xs⟩, ⟨set.mem_univ _, rfl⟩⟩)

theorem image_preimage_val (s t : set α) :
  (@subtype.val _ s) '' ((@subtype.val _ s) ⁻¹' t) = t ∩ s :=
begin
  ext x, simp, split,
  { rintros ⟨y, ys, yt, yx⟩, rw ←yx, exact ⟨yt, ys⟩ },
  rintros ⟨xt, xs⟩, exact ⟨x, xs, xt, rfl⟩
end

theorem preimage_val_eq_preimage_val_iff (s t u : set α) :
  ((@subtype.val _ s) ⁻¹' t = (@subtype.val _ s) ⁻¹' u) ↔ (t ∩ s = u ∩ s) :=
begin
  rw [←image_preimage_val, ←image_preimage_val],
  split, { intro h, rw h },
  intro h, exact set.injective_image (val_injective) h
end
end subtype

namespace set

section range

variable {α : Type*}

@[simp] lemma subtype.val_range {p : α → Prop} :
  range (@subtype.val _ p) = {x | p x} :=
by rw ← image_univ; simp [-image_univ, subtype.val_image]

@[simp] lemma range_coe_subtype (s : set α): range (coe : s → α) = s :=
subtype.val_range

end range

section prod

variables {α : Type*} {β : Type*} {γ : Type*} {δ : Type*}
variables {s s₁ s₂ : set α} {t t₁ t₂ : set β}

/-- The cartesian product `prod s t` is the set of `(a, b)`
  such that `a ∈ s` and `b ∈ t`. -/
protected def prod (s : set α) (t : set β) : set (α × β) :=
{p | p.1 ∈ s ∧ p.2 ∈ t}

lemma prod_eq (s : set α) (t : set β) : set.prod s t = prod.fst ⁻¹' s ∩ prod.snd ⁻¹' t := rfl

theorem mem_prod_eq {p : α × β} : p ∈ set.prod s t = (p.1 ∈ s ∧ p.2 ∈ t) := rfl

@[simp] theorem mem_prod {p : α × β} : p ∈ set.prod s t ↔ p.1 ∈ s ∧ p.2 ∈ t := iff.rfl

lemma mk_mem_prod {a : α} {b : β} (a_in : a ∈ s) (b_in : b ∈ t) : (a, b) ∈ set.prod s t := ⟨a_in, b_in⟩

@[simp] theorem prod_empty {s : set α} : set.prod s ∅ = (∅ : set (α × β)) :=
ext $ by simp [set.prod]

@[simp] theorem empty_prod {t : set β} : set.prod ∅ t = (∅ : set (α × β)) :=
ext $ by simp [set.prod]

theorem insert_prod {a : α} {s : set α} {t : set β} :
  set.prod (insert a s) t = (prod.mk a '' t) ∪ set.prod s t :=
ext begin simp [set.prod, image, iff_def, or_imp_distrib] {contextual := tt}; cc end

theorem prod_insert {b : β} {s : set α} {t : set β} :
  set.prod s (insert b t) = ((λa, (a, b)) '' s) ∪ set.prod s t :=
ext begin simp [set.prod, image, iff_def, or_imp_distrib] {contextual := tt}; cc end

theorem prod_preimage_eq {f : γ → α} {g : δ → β} :
  set.prod (preimage f s) (preimage g t) = preimage (λp, (f p.1, g p.2)) (set.prod s t) := rfl

theorem prod_mono {s₁ s₂ : set α} {t₁ t₂ : set β} (hs : s₁ ⊆ s₂) (ht : t₁ ⊆ t₂) :
  set.prod s₁ t₁ ⊆ set.prod s₂ t₂ :=
assume x ⟨h₁, h₂⟩, ⟨hs h₁, ht h₂⟩

theorem prod_inter_prod : set.prod s₁ t₁ ∩ set.prod s₂ t₂ = set.prod (s₁ ∩ s₂) (t₁ ∩ t₂) :=
subset.antisymm
  (assume ⟨a, b⟩ ⟨⟨ha₁, hb₁⟩, ⟨ha₂, hb₂⟩⟩, ⟨⟨ha₁, ha₂⟩, ⟨hb₁, hb₂⟩⟩)
  (subset_inter
    (prod_mono (inter_subset_left _ _) (inter_subset_left _ _))
    (prod_mono (inter_subset_right _ _) (inter_subset_right _ _)))

theorem image_swap_prod : (λp:β×α, (p.2, p.1)) '' set.prod t s = set.prod s t :=
ext $ assume ⟨a, b⟩, by simp [mem_image_eq, set.prod, and_comm]; exact
⟨ assume ⟨b', a', ⟨h_a, h_b⟩, h⟩, by subst a'; subst b'; assumption,
  assume h, ⟨b, a, ⟨rfl, rfl⟩, h⟩⟩

theorem image_swap_eq_preimage_swap : image (@prod.swap α β) = preimage prod.swap :=
image_eq_preimage_of_inverse prod.swap_left_inverse prod.swap_right_inverse

theorem prod_image_image_eq {m₁ : α → γ} {m₂ : β → δ} :
  set.prod (image m₁ s) (image m₂ t) = image (λp:α×β, (m₁ p.1, m₂ p.2)) (set.prod s t) :=
ext $ by simp [-exists_and_distrib_right, exists_and_distrib_right.symm, and.left_comm, and.assoc, and.comm]

theorem prod_range_range_eq {α β γ δ} {m₁ : α → γ} {m₂ : β → δ} :
  set.prod (range m₁) (range m₂) = range (λp:α×β, (m₁ p.1, m₂ p.2)) :=
ext $ by simp [range]

@[simp] theorem prod_singleton_singleton {a : α} {b : β} :
  set.prod {a} {b} = ({(a, b)} : set (α×β)) :=
ext $ by simp [set.prod]

theorem prod_neq_empty_iff {s : set α} {t : set β} :
  set.prod s t ≠ ∅ ↔ (s ≠ ∅ ∧ t ≠ ∅) :=
by simp [not_eq_empty_iff_exists]

theorem prod_eq_empty_iff {s : set α} {t : set β} :
  set.prod s t = ∅ ↔ (s = ∅ ∨ t = ∅) :=
suffices (¬ set.prod s t ≠ ∅) ↔ (¬ s ≠ ∅ ∨ ¬ t ≠ ∅), by simpa only [(≠), classical.not_not],
by classical; rw [prod_neq_empty_iff, not_and_distrib]

@[simp] theorem prod_mk_mem_set_prod_eq {a : α} {b : β} {s : set α} {t : set β} :
  (a, b) ∈ set.prod s t = (a ∈ s ∧ b ∈ t) := rfl

@[simp] theorem univ_prod_univ : set.prod (@univ α) (@univ β) = univ :=
ext $ assume ⟨a, b⟩, by simp

lemma prod_sub_preimage_iff {W : set γ} {f : α × β → γ} :
  set.prod s t ⊆ f ⁻¹' W ↔ ∀ a b, a ∈ s → b ∈ t → f (a, b) ∈ W :=
by simp [subset_def]

end prod

section pi
variables {α : Type*} {π : α → Type*}

def pi (i : set α) (s : Πa, set (π a)) : set (Πa, π a) := { f | ∀a∈i, f a ∈ s a }

@[simp] lemma pi_empty_index (s : Πa, set (π a)) : pi ∅ s = univ := by ext; simp [pi]

@[simp] lemma pi_insert_index (a : α) (i : set α) (s : Πa, set (π a)) :
  pi (insert a i) s = ((λf, f a) ⁻¹' s a) ∩ pi i s :=
by ext; simp [pi, or_imp_distrib, forall_and_distrib]

@[simp] lemma pi_singleton_index (a : α) (s : Πa, set (π a)) :
  pi {a} s = ((λf:(Πa, π a), f a) ⁻¹' s a) :=
by ext; simp [pi]

lemma pi_if {p : α → Prop} [h : decidable_pred p] (i : set α) (s t : Πa, set (π a)) :
  pi i (λa, if p a then s a else t a) = pi {a ∈ i | p a} s ∩ pi {a ∈ i | ¬ p a} t :=
begin
  ext f,
  split,
  { assume h, split; { rintros a ⟨hai, hpa⟩, simpa [*] using h a } },
  { rintros ⟨hs, ht⟩ a hai,
    by_cases p a; simp [*, pi] at * }
end

end pi

end set
