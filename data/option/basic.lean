/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import logic.basic data.bool data.option.defs tactic.interactive

namespace option
variables {α : Type*} {β : Type*}

@[simp] theorem get_mem : ∀ {o : option α} (h : is_some o), option.get h ∈ o
| (some a) _ := rfl

theorem get_of_mem {a : α} : ∀ {o : option α} (h : is_some o), a ∈ o → option.get h = a
| _ _ rfl := rfl

theorem mem_unique {o : option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
option.some.inj $ ha.symm.trans hb

theorem injective_some (α : Type*) : function.injective (@some α) :=
λ _ _, some_inj.mp

@[extensionality] theorem ext : ∀ {o₁ o₂ : option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
| none     none     H := rfl
| (some a) o        H := ((H _).1 rfl).symm
| o        (some b) H := (H _).2 rfl

theorem eq_none_iff_forall_not_mem {o : option α} :
  o = none ↔ (∀ a, a ∉ o) :=
⟨λ e a h, by rw e at h; cases h, λ h, ext $ by simpa⟩

@[simp] theorem none_bind {α β} (f : α → option β) : none >>= f = none := rfl

@[simp] theorem some_bind {α β} (a : α) (f : α → option β) : some a >>= f = f a := rfl

@[simp] theorem none_bind' (f : α → option β) : none.bind f = none := rfl

@[simp] theorem some_bind' (a : α) (f : α → option β) : (some a).bind f = f a := rfl

@[simp] theorem bind_some : ∀ x : option α, x >>= some = x :=
@bind_pure α option _ _

@[simp] theorem bind_eq_some {α β} {x : option α} {f : α → option β} {b : β} : x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

@[simp] theorem bind_eq_some' {x : option α} {f : α → option β} {b : β} : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

lemma bind_comm {α β γ} {f : α → β → option γ} (a : option α) (b : option β) :
  a.bind (λx, b.bind (f x)) = b.bind (λy, a.bind (λx, f x y)) :=
by cases a; cases b; refl

@[simp] theorem map_none {α β} {f : α → β} : f <$> none = none := rfl

@[simp] theorem map_some {α β} {a : α} {f : α → β} : f <$> some a = some (f a) := rfl

@[simp] theorem map_none' {f : α → β} : option.map f none = none := rfl

@[simp] theorem map_some' {a : α} {f : α → β} : option.map f (some a) = some (f a) := rfl

@[simp] theorem map_eq_some {α β} {x : option α} {f : α → β} {b : β} : f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b :=
by cases x; simp

@[simp] theorem map_eq_some' {x : option α} {f : α → β} {b : β} : x.map f = some b ↔ ∃ a, x = some a ∧ f a = b :=
by cases x; simp

@[simp] theorem map_id' : option.map (@id α) = id := map_id

@[simp] theorem seq_some {α β} {a : α} {f : α → β} : some f <*> some a = some (f a) := rfl

@[simp] theorem some_orelse' (a : α) (x : option α) : (some a).orelse x = some a := rfl

@[simp] theorem some_orelse (a : α) (x : option α) : (some a <|> x) = some a := rfl

@[simp] theorem none_orelse' (x : option α) : none.orelse x = x :=
by cases x; refl

@[simp] theorem none_orelse (x : option α) : (none <|> x) = x := none_orelse' x

@[simp] theorem orelse_none' (x : option α) : x.orelse none = x :=
by cases x; refl

@[simp] theorem orelse_none (x : option α) : (x <|> none) = x := orelse_none' x

@[simp] theorem is_some_none : @is_some α none = ff := rfl

@[simp] theorem is_some_some {a : α} : is_some (some a) = tt := rfl

theorem is_some_iff_exists {x : option α} : is_some x ↔ ∃ a, x = some a :=
by cases x; simp [is_some]; exact ⟨_, rfl⟩

@[simp] theorem is_none_none : @is_none α none = tt := rfl

@[simp] theorem is_none_some {a : α} : is_none (some a) = ff := rfl

@[simp] theorem not_is_some {a : option α} : is_some a = ff ↔ a.is_none = tt :=
by cases a; simp

theorem iget_mem [inhabited α] : ∀ {o : option α}, is_some o → o.iget ∈ o
| (some a) _ := rfl

theorem iget_of_mem [inhabited α] {a : α} : ∀ {o : option α}, a ∈ o → o.iget = a
| _ rfl := rfl

@[simp] theorem guard_eq_some {p : α → Prop} [decidable_pred p] {a b : α} :
  guard p a = some b ↔ a = b ∧ p a :=
by by_cases p a; simp [option.guard, h]; intro; contradiction

@[simp] theorem guard_eq_some' {p : Prop} [decidable p] :
  ∀ u, _root_.guard p = some u ↔ p
| () := by by_cases p; simp [guard, h, pure]; intro; contradiction

theorem lift_or_get_choice {f : α → α → α} (h : ∀ a b, f a b = a ∨ f a b = b) :
  ∀ o₁ o₂, lift_or_get f o₁ o₂ = o₁ ∨ lift_or_get f o₁ o₂ = o₂
| none     none     := or.inl rfl
| (some a) none     := or.inl rfl
| none     (some b) := or.inr rfl
| (some a) (some b) := by simpa [lift_or_get] using h a b

end option
