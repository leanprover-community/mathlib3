/-
Copyright (c) 2018 Johan Commelin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Johan Commelin, Johannes Hölzl, Mitchell Rowett, Scott Morrison

This file is a modification of `subgroup.lean` by
Johannes Hölzl, Mitchell Rowett, Scott Morrison.
The only thing it does is translating all the multiplicative
notions into their additive counterparts.
-/
import .add_submonoid
open set function

variables {α : Type*} {β : Type*} {s : set α} {a a₁ a₂ b c: α}

section add_group
variable [add_group α]

lemma injective_add {a : α} : injective ((+) a) :=
assume a₁ a₂ h,
have -a + a + a₁ = -a + a + a₂, by rw [add_assoc, add_assoc, h],
by rwa [neg_add_self, zero_add, zero_add] at this

/-- `s` is an additive subgroup: a set containing 0 and closed under addition and negation. -/
class is_add_subgroup [add_group α] (s : set α) extends is_add_submonoid s : Prop :=
(neg_mem {a} : a ∈ s → -a ∈ s)

instance subtype.add_group {s : set α} [is_add_subgroup s] : add_group s :=
{ neg          := λa, ⟨-(a.1), is_add_subgroup.neg_mem a.2⟩,
  add_left_neg := assume ⟨a, _⟩, subtype.eq $ add_left_neg _,
  .. subtype.add_monoid }

theorem is_add_subgroup.of_sub [group α] (s : set α)
  (zero_mem : (0:α) ∈ s) (sub_mem : ∀{a b:α}, a ∈ s → b ∈ s → a - b ∈ s):
  is_add_subgroup s :=
have neg_mem : ∀a, a ∈ s → -a ∈ s, from
  assume a ha,
  have 0 - a ∈ s, from sub_mem zero_mem ha,
  by simpa,
{ neg_mem := neg_mem,
  add_mem := assume a b ha hb,
    have a - - b ∈ s, from sub_mem ha (neg_mem b hb),
    by simpa,
  zero_mem := zero_mem }

def gmultiples (x : α) : set α := {y | ∃i:ℤ, gsmul i x = y}

instance gmultiples.is_add_subgroup (x : α) : is_add_subgroup (gmultiples x) :=
{ zero_mem := ⟨(0:ℤ), by simp⟩,
  add_mem := assume x₁ x₂ ⟨i₁, h₁⟩ ⟨i₂, h₂⟩, ⟨i₁ + i₂, by simp [add_gsmul, *]⟩,
  neg_mem := assume x₀ ⟨i, h⟩, ⟨-i, by simp [h.symm]⟩ }

lemma is_add_subgroup.gsmul_mem {a : α} {s : set α} [is_add_subgroup s] (h : a ∈ s) : ∀{i:ℤ}, gsmul i a ∈ s
| (n : ℕ) := is_add_submonoid.smul_mem h
| -[1+ n] := is_add_subgroup.neg_mem (is_add_submonoid.smul_mem h)

lemma mem_gmultiples {a : α} : a ∈ gmultiples a :=
⟨1, by simp⟩

end add_group

namespace is_add_subgroup
open is_add_submonoid
variable (s)
variables [add_group α] [is_add_subgroup s]

lemma neg_mem_iff : -a ∈ s ↔ a ∈ s :=
iff.intro (assume h, have - -a ∈ s, from neg_mem h, by simpa) neg_mem

lemma add_mem_cancel_left (h : a ∈ s) : b + a ∈ s ↔ b ∈ s :=
iff.intro
  (assume hba,
    have (b + a) + -a ∈ s, from add_mem hba (neg_mem h),
    by simpa)
  (assume hb, add_mem hb h)

lemma add_mem_cancel_right (h : a ∈ s) : a + b ∈ s ↔ b ∈ s :=
iff.intro
  (assume hab,
    have -a + (a + b) ∈ s, from add_mem (neg_mem h) hab,
    by simpa)
  (add_mem h)

end is_add_subgroup

namespace add_group
open is_add_submonoid is_add_subgroup

variable [add_group α]

inductive in_closure (s : set α) : α → Prop
| basic {a : α} : a ∈ s → in_closure a
| zero : in_closure 0
| neg {a : α} : in_closure a → in_closure (-a)
| add {a b : α} : in_closure a → in_closure b → in_closure (a + b)

/-- `add_group.closure s` is the additive subgroup closed over `s`, i.e. the smallest subgroup containg s. -/
def closure (s : set α) : set α := {a | in_closure s a }

lemma mem_closure {a : α} : a ∈ s → a ∈ closure s := in_closure.basic

instance closure.is_add_subgroup (s : set α) : is_add_subgroup (closure s) :=
{ zero_mem := in_closure.zero s, add_mem := assume a b, in_closure.add, neg_mem := assume a, in_closure.neg }

theorem subset_closure {s : set α} : s ⊆ closure s :=
assume a, in_closure.basic

theorem closure_subset {s t : set α} [is_add_subgroup t] (h : s ⊆ t) : closure s ⊆ t :=
assume a ha, by induction ha; simp [h _, *, zero_mem, add_mem, neg_mem_iff]

theorem gmultiples_eq_closure {a : α} : gmultiples a = closure {a} :=
subset.antisymm
  (assume x h, match x, h with _, ⟨i, rfl⟩ := gsmul_mem (mem_closure $ by simp) end)
  (closure_subset $ by  simp [mem_gmultiples])

end add_group

class normal_add_subgroup [add_group α] (s : set α) extends is_add_subgroup s : Prop :=
(normal : ∀ n ∈ s, ∀ g : α, g + n - g ∈ s)

namespace is_add_subgroup
variable [add_group α]

-- Normal subgroup properties
lemma mem_norm_comm {a b : α} {s : set α} [normal_add_subgroup s] (hab : a + b ∈ s) : b + a ∈ s :=
have h : -a + (a + b) - -a ∈ s, from normal_add_subgroup.normal (a + b) hab (-a),
by simp at h; exact h

lemma mem_norm_comm_iff {a b : α} {s : set α} [normal_add_subgroup s] : a + b ∈ s ↔ b + a ∈ s :=
iff.intro mem_norm_comm mem_norm_comm

/-- The trivial subgroup -/
def trivial (α : Type*) [add_group α] : set α := {0}

@[simp] lemma mem_trivial [add_group α] {g : α} : g ∈ trivial α ↔ g = 0 :=
by simp [trivial]

instance trivial_normal : normal_add_subgroup (trivial α) :=
by refine {..}; simp [trivial] {contextual := tt}

lemma trivial_eq_closure : trivial α = add_group.closure ∅ :=
subset.antisymm
  (by simp [set.subset_def, is_add_submonoid.zero_mem])
  (add_group.closure_subset $ by simp)

instance univ_add_subgroup : normal_add_subgroup (@univ α) :=
by refine {..}; simp

def center (α : Type*) [add_group α] : set α := {z | ∀ g, g + z = z + g}

lemma mem_center {a : α} : a ∈ center α ↔ (∀g, g + a = a + g) :=
iff.refl _

instance center_normal : normal_add_subgroup (center α) :=
{ zero_mem := by simp [center],
  add_mem := assume a b ha hb g,
    by rw [←add_assoc, mem_center.2 ha g, add_assoc, mem_center.2 hb g, ←add_assoc],
  neg_mem := assume a ha g,
    calc
      g + -a = -a + (g + a) + -a : by simp [ha g]
      ...     = -a + g             : by rw [←add_assoc, add_assoc]; simp,
  normal := assume n ha g h,
    calc
      h + (g + n - g) = h + n           : by simp [ha g, add_assoc]
      ...               = g + - g + n + h : by rw ha h; simp
      ...               = g + n - g + h : by rw [add_assoc g, ha (-g), ←add_assoc]; simp }

end is_add_subgroup
