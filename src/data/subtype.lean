/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/

-- Lean complains if this section is turned into a namespace
section subtype
variables {α : Sort*} {p : α → Prop}

@[simp] theorem subtype.forall {q : {a // p a} → Prop} :
  (∀ x, q x) ↔ (∀ a b, q ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem subtype.exists {q : {a // p a} → Prop} :
  (∃ x, q x) ↔ (∃ a b, q ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

end subtype

namespace subtype
variables {α : Sort*} {β : Sort*} {γ : Sort*} {p : α → Prop}

protected lemma eq' : ∀ {a1 a2 : {x // p x}}, a1.val = a2.val → a1 = a2
| ⟨x, h1⟩ ⟨.(x), h2⟩ rfl := rfl

lemma ext {a1 a2 : {x // p x}} : a1 = a2 ↔ a1.val = a2.val :=
⟨congr_arg _, subtype.eq'⟩

lemma coe_ext {a1 a2 : {x // p x}} : a1 = a2 ↔ (a1 : α) = a2 :=
ext

theorem val_injective : function.injective (@val _ p) :=
λ a b, subtype.eq'

/-- Restriction of a function to a function on subtypes. -/
def map {p : α → Prop} {q : β → Prop} (f : α → β) (h : ∀a, p a → q (f a)) :
  subtype p → subtype q :=
λ x, ⟨f x.1, h x.1 x.2⟩

theorem map_comp {p : α → Prop} {q : β → Prop} {r : γ → Prop} {x : subtype p}
  (f : α → β) (h : ∀a, p a → q (f a)) (g : β → γ) (l : ∀a, q a → r (g a)) :
  map g l (map f h x) = map (g ∘ f) (assume a ha, l (f a) $ h a ha) x :=
rfl

theorem map_id {p : α → Prop} {h : ∀a, p a → p (id a)} : map (@id α) h = id :=
funext $ assume ⟨v, h⟩, rfl

instance [has_equiv α] (p : α → Prop) : has_equiv (subtype p) :=
⟨λ s t, s.val ≈ t.val⟩

theorem equiv_iff [has_equiv α] {p : α → Prop} {s t : subtype p} :
  s ≈ t ↔ s.val ≈ t.val :=
iff.rfl

variables [setoid α]

protected theorem refl (s : subtype p) : s ≈ s :=
setoid.refl s.val

protected theorem symm {s t : subtype p} (h : s ≈ t) : t ≈ s :=
setoid.symm h

protected theorem trans {s t u : subtype p} (h₁ : s ≈ t) (h₂ : t ≈ u) : s ≈ u :=
setoid.trans h₁ h₂

theorem equivalence (p : α → Prop) : equivalence (@has_equiv.equiv (subtype p) _) :=
mk_equivalence _ subtype.refl (@subtype.symm _ p _) (@subtype.trans _ p _)

instance (p : α → Prop) : setoid (subtype p) :=
setoid.mk (≈) (equivalence p)

end subtype

namespace subtype
variables {α : Type*} {β : Type*} {γ : Type*} {p : α → Prop}

@[simp] theorem coe_eta {α : Type*} {p : α → Prop}
 (a : {a // p a}) (h : p a) : mk ↑a h = a := eta _ _

@[simp] theorem coe_mk {α : Type*} {p : α → Prop}
 (a h) : (@mk α p a h : α) = a := rfl

@[simp] theorem mk_eq_mk {α : Type*} {p : α → Prop}
 {a h a' h'} : @mk α p a h = @mk α p a' h' ↔ a = a' :=
⟨λ H, by injection H, λ H, by congr; assumption⟩

@[simp] lemma val_prop {S : set α} (a : {a // a ∈ S}) : a.val ∈ S := a.property

@[simp] lemma val_prop' {S : set α} (a : {a // a ∈ S}) : ↑a ∈ S := a.property

end subtype
