/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/

namespace option

instance has_mem {α : Type*} : has_mem α (option α) := ⟨λ a b, b = some a⟩

@[simp] lemma mem_def {α : Type*} {a : α} {b : option α} : a ∈ b ↔ b = some a :=
iff.rfl

@[simp] lemma some_inj {α : Type*} {a b : α} : some a = some b ↔ a = b :=
⟨by intro h; injection h, congr_arg some⟩

@[simp] lemma bind_some {α β : Type*} {a : α} {f : α → option β} : some a >>= f = f a :=
rfl

@[reducible] def iget {α : Type*} [inhabited α] : option α → α
| (some x) := x
| none     := arbitrary α

def guard {α : Type*} (p : α → Prop) [decidable_pred p] (a : α) : option α :=
if p a then some a else none

def filter {α : Type*} (p : α → Prop) [decidable_pred p] (o : option α) : option α :=
o.bind (guard p)

@[simp] lemma guard_eq_some {α : Type*} {p : α → Prop} [decidable_pred p] {a b : α} :
  option.guard p a = some b ↔ a = b ∧ p a :=
by by_cases p a; simp [option.guard, h]; intro; contradiction

end option
