/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/

section sigma
variables {α : Type*} {β : α → Type*}

instance [inhabited α] [inhabited (β (default α))] : inhabited (sigma β) :=
⟨⟨default α, default (β (default α))⟩⟩

instance [h₁ : decidable_eq α] [h₂ : ∀a, decidable_eq (β a)] : decidable_eq (sigma β)
| ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ := match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
  | _, b₁, _, b₂, is_true (eq.refl a) :=
    match b₁, b₂, h₂ a b₁ b₂ with
    | _, _, is_true (eq.refl b) := is_true rfl
    | b₁, b₂, is_false n := is_false (assume h, sigma.no_confusion h (λe₁ e₂, n $ eq_of_heq e₂))
    end
  | a₁, _, a₂, _, is_false n := is_false (assume h, sigma.no_confusion h (λe₁ e₂, n e₁))
  end

@[simp] theorem sigma.mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  sigma.mk a₁ b₁ = ⟨a₂, b₂⟩ ↔ (a₁ = a₂ ∧ b₁ == b₂) :=
⟨sigma.mk.inj, λ ⟨h₁, h₂⟩, by congr; assumption⟩

@[simp] theorem sigma.forall {p : (Σ a, β a) → Prop} :
  (∀ x, p x) ↔ (∀ a b, p ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem sigma.exists {p : (Σ a, β a) → Prop} :
  (∃ x, p x) ↔ (∃ a b, p ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

variables {α₁ : Type*} {α₂ : Type*} {β₁ : α₁ → Type*} {β₂ : α₂ → Type*}

/-- Map the left and right components of a sigma -/
def sigma.map (f₁ : α₁ → α₂) (f₂ : Πa, β₁ a → β₂ (f₁ a)) : sigma β₁ → sigma β₂
| ⟨a, b⟩ := ⟨f₁ a, f₂ a b⟩

end sigma

section psigma
variables {α : Sort*} {β : α → Sort*}

instance [inhabited α] [inhabited (β (default α))] : inhabited (psigma β) :=
⟨⟨default α, default (β (default α))⟩⟩

instance [h₁ : decidable_eq α] [h₂ : ∀a, decidable_eq (β a)] : decidable_eq (psigma β)
| ⟨a₁, b₁⟩ ⟨a₂, b₂⟩ := match a₁, b₁, a₂, b₂, h₁ a₁ a₂ with
  | _, b₁, _, b₂, is_true (eq.refl a) :=
    match b₁, b₂, h₂ a b₁ b₂ with
    | _, _, is_true (eq.refl b) := is_true rfl
    | b₁, b₂, is_false n := is_false (assume h, psigma.no_confusion h (λe₁ e₂, n $ eq_of_heq e₂))
    end
  | a₁, _, a₂, _, is_false n := is_false (assume h, psigma.no_confusion h (λe₁ e₂, n e₁))
  end

theorem psigma.mk.inj_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  @psigma.mk α β a₁ b₁ = @psigma.mk α β a₂ b₂ ↔ (a₁ = a₂ ∧ b₁ == b₂) :=
iff.intro psigma.mk.inj $
  assume ⟨h₁, h₂⟩, match a₁, a₂, b₁, b₂, h₁, h₂ with _, _, _, _, eq.refl a, heq.refl b := rfl end

variables {α₁ : Sort*} {α₂ : Sort*} {β₁ : α₁ → Sort*} {β₂ : α₂ → Sort*}

/-- Map the left and right components of a sigma -/
def psigma.map (f₁ : α₁ → α₂) (f₂ : Πa, β₁ a → β₂ (f₁ a)) : psigma β₁ → psigma β₂
| ⟨a, b⟩ := ⟨f₁ a, f₂ a b⟩

end psigma

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
