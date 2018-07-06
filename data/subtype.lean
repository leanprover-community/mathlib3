/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/

section subtype
variables {α : Sort*} {β : α → Prop}

protected lemma subtype.eq' : ∀ {a1 a2 : {x // β x}}, a1.val = a2.val → a1 = a2
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

lemma subtype.ext {a1 a2 : {x // β x}} : a1 = a2 ↔ a1.val = a2.val :=
⟨congr_arg _, subtype.eq'⟩

theorem subtype.val_injective : function.injective (@subtype.val _ β) :=
λ a b, subtype.eq'

@[simp] theorem subtype.coe_eta {α : Type*} {β : α → Prop}
 (a : {a // β a}) (h : β a) : subtype.mk ↑a h = a := subtype.eta _ _

@[simp] theorem subtype.coe_mk {α : Type*} {β : α → Prop}
 (a h) : (@subtype.mk α β a h : α) = a := rfl

@[simp] theorem subtype.mk_eq_mk {α : Type*} {β : α → Prop}
 {a h a' h'} : @subtype.mk α β a h = @subtype.mk α β a' h' ↔ a = a' :=
⟨λ H, by injection H, λ H, by congr; assumption⟩

@[simp] theorem subtype.forall {p : {a // β a} → Prop} :
  (∀ x, p x) ↔ (∀ a b, p ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem subtype.exists {p : {a // β a} → Prop} :
  (∃ x, p x) ↔ (∃ a b, p ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

end subtype

namespace subtype
variables {α : Sort*} {β : Sort*} {γ : Sort*}

/-- Restriction of a function to a function on subtypes. -/
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀a, p a → q (f a)) :
  subtype p → subtype q
| ⟨v, hv⟩ := ⟨f v, h v hv⟩

theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : subtype p}
  (f : α → β) (h : ∀a, p a → q (f a)) (g : β → γ) (l : ∀a, q a → r (g a)) :
  map g l (map f h x) = map (g ∘ f) (assume a ha, l (f a) $ h a ha) x :=
by cases x with v h; refl

theorem map_id {p : α → Prop} {h : ∀a, p a → p (id a)} : map (@id α) h = id :=
funext $ assume ⟨v, h⟩, rfl

end subtype
