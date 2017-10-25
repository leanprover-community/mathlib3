/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import logic.basic data.bool

namespace option
universe u
variables {α β : Type u}

instance has_mem : has_mem α (option α) := ⟨λ a b, b = some a⟩

@[simp] lemma mem_def {a : α} {b : option α} : a ∈ b ↔ b = some a :=
iff.rfl

@[simp] lemma some_inj {a b : α} : some a = some b ↔ a = b :=
⟨by intro h; injection h, congr_arg some⟩

@[simp] lemma none_ne_some (a : α) : none ≠ some a
| h := option.no_confusion h

@[simp] lemma bind_none {f : α → option β} : none >>= f = none := rfl

@[simp] lemma bind_some {a : α} {f : α → option β} : some a >>= f = f a := rfl

@[simp] lemma bind_eq_some {x : option α} {f : α → option β} {b : β} : x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

@[simp] lemma map_none {f : α → β} : f <$> none = none := rfl

@[simp] lemma map_some {a : α} {f : α → β} : f <$> some a = some (f a) := rfl

@[simp] lemma map_eq_some {x : option α} {f : α → β} {b : β} : f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b :=
by cases x; simp

lemma is_some_iff_exists {x : option α} : is_some x ↔ ∃ a, x = some a :=
by cases x; simp [is_some]; exact show ∃ a', a = a', from ⟨_, rfl⟩

@[reducible] def iget [inhabited α] : option α → α
| (some x) := x
| none     := arbitrary α

def guard (p : α → Prop) [decidable_pred p] (a : α) : option α :=
if p a then some a else none

def filter (p : α → Prop) [decidable_pred p] (o : option α) : option α :=
o.bind (guard p)

@[simp] lemma guard_eq_some {p : α → Prop} [decidable_pred p] {a b : α} :
  option.guard p a = some b ↔ a = b ∧ p a :=
by by_cases p a; simp [option.guard, h]; intro; contradiction

end option
