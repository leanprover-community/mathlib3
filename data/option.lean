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

lemma some_inj {a b : α} : some a = some b ↔ a = b := by simp

@[simp] lemma none_bind (f : α → option β) : none >>= f = none := rfl

@[simp] lemma some_bind (a : α) (f : α → option β) : some a >>= f = f a := rfl

@[simp] lemma bind_some : ∀ x : option α, x >>= some = x :=
@bind_pure α option _ _

@[simp] lemma bind_eq_some {x : option α} {f : α → option β} {b : β} : x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

@[simp] lemma map_none {f : α → β} : f <$> none = none := rfl

@[simp] lemma map_some {a : α} {f : α → β} : f <$> some a = some (f a) := rfl

@[simp] lemma map_eq_some {x : option α} {f : α → β} {b : β} : f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b :=
by cases x; simp

@[simp] lemma map_id' : option.map (@id α) = id := map_id

@[simp] lemma seq_some {a : α} {f : α → β} : some f <*> some a = some (f a) := rfl

lemma is_some_iff_exists {x : option α} : is_some x ↔ ∃ a, x = some a :=
by cases x; simp [is_some]; exact ⟨_, rfl⟩

/-- inhabited `get` function. Returns `a` if the input is `some a`,
  otherwise returns `default`. -/
@[reducible] def iget [inhabited α] : option α → α
| (some x) := x
| none     := default α

/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
def guard (p : α → Prop) [decidable_pred p] (a : α) : option α :=
if p a then some a else none

/-- `filter p o` returns `some a` if `o` is `some a`
  and `p a` holds, otherwise `none`. -/
def filter (p : α → Prop) [decidable_pred p] (o : option α) : option α :=
o.bind (guard p)

@[simp] lemma guard_eq_some {p : α → Prop} [decidable_pred p] {a b : α} :
  option.guard p a = some b ↔ a = b ∧ p a :=
by by_cases p a; simp [option.guard, h]; intro; contradiction

def to_list {α} : option α → list α 
| none     := []
| (some a) := [a]

end option
