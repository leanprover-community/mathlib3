/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro

Extra definitions on option.
-/

namespace option
variables {α : Type*} {β : Type*}

/-- An elimination principle for `option`. It is a nondependent version of `option.rec_on`. -/
protected def elim : option α → β → (α → β) → β
| (some x) y f := f x
| none     y f := y

instance has_mem : has_mem α (option α) := ⟨λ a b, b = some a⟩

@[simp] theorem mem_def {a : α} {b : option α} : a ∈ b ↔ b = some a :=
iff.rfl

theorem is_none_iff_eq_none {o : option α} : o.is_none = tt ↔ o = none :=
⟨option.eq_none_of_is_none, λ e, e.symm ▸ rfl⟩

theorem some_inj {a b : α} : some a = some b ↔ a = b := by simp

instance decidable_eq_none {o : option α} : decidable (o = none) :=
decidable_of_decidable_of_iff (bool.decidable_eq _ _) is_none_iff_eq_none

instance decidable_forall_mem {p : α → Prop} [decidable_pred p] :
  ∀ o : option α, decidable (∀ a ∈ o, p a)
| none     := is_true (by simp)
| (some a) := if h : p a
  then is_true $ λ o e, some_inj.1 e ▸ h
  else is_false $ mt (λ H, H _ rfl) h

instance decidable_exists_mem {p : α → Prop} [decidable_pred p] :
  ∀ o : option α, decidable (∃ a ∈ o, p a)
| none     := is_false (λ ⟨a, ⟨h, _⟩⟩, by cases h)
| (some a) := if h : p a
  then is_true $ ⟨_, rfl, h⟩
  else is_false $ λ ⟨_, ⟨rfl, hn⟩⟩, h hn

/-- inhabited `get` function. Returns `a` if the input is `some a`,
  otherwise returns `default`. -/
@[reducible] def iget [inhabited α] : option α → α
| (some x) := x
| none     := default α

@[simp] theorem iget_some [inhabited α] {a : α} : (some a).iget = a := rfl

/-- `guard p a` returns `some a` if `p a` holds, otherwise `none`. -/
def guard (p : α → Prop) [decidable_pred p] (a : α) : option α :=
if p a then some a else none

/-- `filter p o` returns `some a` if `o` is `some a`
  and `p a` holds, otherwise `none`. -/
def filter (p : α → Prop) [decidable_pred p] (o : option α) : option α :=
o.bind (guard p)

def to_list : option α → list α
| none     := []
| (some a) := [a]

@[simp] theorem mem_to_list {a : α} {o : option α} : a ∈ to_list o ↔ a ∈ o :=
by cases o; simp [to_list, eq_comm]

def lift_or_get (f : α → α → α) : option α → option α → option α
| none     none     := none
| (some a) none     := some a       -- get a
| none     (some b) := some b       -- get b
| (some a) (some b) := some (f a b) -- lift f

instance lift_or_get_comm (f : α → α → α) [h : is_commutative α f] :
  is_commutative (option α) (lift_or_get f) :=
⟨λ a b, by cases a; cases b; simp [lift_or_get, h.comm]⟩

instance lift_or_get_assoc (f : α → α → α) [h : is_associative α f] :
  is_associative (option α) (lift_or_get f) :=
⟨λ a b c, by cases a; cases b; cases c; simp [lift_or_get, h.assoc]⟩

instance lift_or_get_idem (f : α → α → α) [h : is_idempotent α f] :
  is_idempotent (option α) (lift_or_get f) :=
⟨λ a, by cases a; simp [lift_or_get, h.idempotent]⟩

instance lift_or_get_is_left_id (f : α → α → α) :
  is_left_id (option α) (lift_or_get f) none :=
⟨λ a, by cases a; simp [lift_or_get]⟩

instance lift_or_get_is_right_id (f : α → α → α) :
  is_right_id (option α) (lift_or_get f) none :=
⟨λ a, by cases a; simp [lift_or_get]⟩

inductive rel (r : α → β → Prop) : option α → option β → Prop
| some {a b} : r a b → rel (some a) (some b)
| none {}    : rel none none

protected def {u v} traverse {F : Type u → Type v} [applicative F] {α β : Type*} (f : α → F β) :
  option α → F (option β)
| none := pure none
| (some x) := some <$> f x

end option
