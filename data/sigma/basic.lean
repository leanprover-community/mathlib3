/-
Copyright (c) 2017 Johannes Hölzl. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Johannes Hölzl
-/

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

namespace sigma

lemma mk_eq_mk_iff {a₁ a₂ : α} {b₁ : β a₁} {b₂ : β a₂} :
  @sigma.mk α β a₁ b₁ = @sigma.mk α β a₂ b₂ ↔ (a₁ = a₂ ∧ b₁ == b₂) :=
iff.intro sigma.mk.inj $
  assume ⟨h₁, h₂⟩, match a₁, a₂, b₁, b₂, h₁, h₂ with _, _, _, _, eq.refl a, heq.refl b := rfl end

variables {α₁ : Type*} {α₂ : Type*} {β₁ : α₁ → Type*} {β₂ : α₂ → Type*}

def map (f₁ : α₁ → α₂) (f₂ : Πa, β₁ a → β₂ (f₁ a)) : sigma β₁ → sigma β₂
| ⟨a, b⟩ := ⟨f₁ a, f₂ a b⟩

end sigma