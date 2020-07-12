/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import tactic.basic

namespace option
variables {α : Type*} {β : Type*} {γ : Type*}

lemma some_ne_none (x : α) : some x ≠ none := λ h, option.no_confusion h

@[simp] theorem get_mem : ∀ {o : option α} (h : is_some o), option.get h ∈ o
| (some a) _ := rfl

theorem get_of_mem {a : α} : ∀ {o : option α} (h : is_some o), a ∈ o → option.get h = a
| _ _ rfl := rfl

@[simp] lemma not_mem_none (a : α) : a ∉ (none : option α) :=
λ h, option.no_confusion h

@[simp] lemma some_get : ∀ {x : option α} (h : is_some x), some (option.get h) = x
| (some x) hx := rfl

@[simp] lemma get_some (x : α) (h : is_some (some x)) : option.get h = x := rfl

@[simp] lemma get_or_else_some (x y : α) : option.get_or_else (some x) y = x := rfl

lemma get_or_else_of_ne_none {x : option α} (hx : x ≠ none) (y : α) : some (x.get_or_else y) = x :=
by cases x; [contradiction, rw get_or_else_some]

theorem mem_unique {o : option α} {a b : α} (ha : a ∈ o) (hb : b ∈ o) : a = b :=
option.some.inj $ ha.symm.trans hb

theorem some_injective (α : Type*) : function.injective (@some α) :=
λ _ _, some_inj.mp

/-- `option.map f` is injective if `f` is injective. -/
theorem map_injective {f : α → β} (Hf : function.injective f) : function.injective (option.map f)
| none      none      H := rfl
| (some a₁) (some a₂) H := by rw Hf (option.some.inj H)

@[ext] theorem ext : ∀ {o₁ o₂ : option α}, (∀ a, a ∈ o₁ ↔ a ∈ o₂) → o₁ = o₂
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

@[simp] theorem bind_eq_some {α β} {x : option α} {f : α → option β} {b : β} :
  x >>= f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

@[simp] theorem bind_eq_some' {x : option α} {f : α → option β} {b : β} :
  x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b :=
by cases x; simp

@[simp] theorem bind_eq_none' {o : option α} {f : α → option β} :
  o.bind f = none ↔ (∀ b a, a ∈ o → b ∉ f a) :=
by simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some']

@[simp] theorem bind_eq_none {α β} {o : option α} {f : α → option β} :
  o >>= f = none ↔ (∀ b a, a ∈ o → b ∉ f a) :=
bind_eq_none'

lemma bind_comm {α β γ} {f : α → β → option γ} (a : option α) (b : option β) :
  a.bind (λx, b.bind (f x)) = b.bind (λy, a.bind (λx, f x y)) :=
by cases a; cases b; refl

lemma bind_assoc (x : option α) (f : α → option β) (g : β → option γ) :
  (x.bind f).bind g = x.bind (λ y, (f y).bind g) := by cases x; refl

@[simp] theorem map_none {α β} {f : α → β} : f <$> none = none := rfl

@[simp] theorem map_some {α β} {a : α} {f : α → β} : f <$> some a = some (f a) := rfl

@[simp] theorem map_none' {f : α → β} : option.map f none = none := rfl

@[simp] theorem map_some' {a : α} {f : α → β} : option.map f (some a) = some (f a) := rfl

@[simp] theorem map_eq_some {α β} {x : option α} {f : α → β} {b : β} :
  f <$> x = some b ↔ ∃ a, x = some a ∧ f a = b :=
by cases x; simp

@[simp] theorem map_eq_some' {x : option α} {f : α → β} {b : β} :
  x.map f = some b ↔ ∃ a, x = some a ∧ f a = b :=
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

lemma eq_some_iff_get_eq {o : option α} {a : α} :
  o = some a ↔ ∃ h : o.is_some, option.get h = a :=
by cases o; simp

lemma not_is_some_iff_eq_none {o : option α} :  ¬o.is_some ↔ o = none :=
by cases o; simp

lemma ne_none_iff_is_some {o : option α} : o ≠ none ↔ o.is_some :=
by cases o; simp

lemma bex_ne_none {p : option α → Prop} :
  (∃ x ≠ none, p x) ↔ ∃ x, p (some x) :=
⟨λ ⟨x, hx, hp⟩, ⟨get $ ne_none_iff_is_some.1 hx, by rwa [some_get]⟩,
  λ ⟨x, hx⟩, ⟨some x, some_ne_none x, hx⟩⟩

lemma ball_ne_none {p : option α → Prop} :
  (∀ x ≠ none, p x) ↔ ∀ x, p (some x) :=
⟨λ h x, h (some x) (some_ne_none x),
  λ h x hx, by simpa only [some_get] using h (get $ ne_none_iff_is_some.1 hx)⟩

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

@[simp] lemma lift_or_get_none_left {f} {b : option α} : lift_or_get f none b = b :=
by cases b; refl

@[simp] lemma lift_or_get_none_right {f} {a : option α} : lift_or_get f a none = a :=
by cases a; refl

@[simp] lemma lift_or_get_some_some {f} {a b : α} :
  lift_or_get f (some a) (some b) = f a b := rfl

/-- given an element of `a : option α`, a default element `b : β` and a function `α → β`, apply this
function to `a` if it comes from `α`, and return `b` otherwise. -/
def cases_on' : option α → β → (α → β) → β
| none     n s := n
| (some a) n s := s a

end option
