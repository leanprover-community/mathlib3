/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/
import logic.basic

/-!
# Extra facts about `pprod`
-/

open function
variables {α β γ δ : Sort*}

namespace pprod

@[simp] lemma mk.eta {p : pprod α β} : pprod.mk p.1 p.2 = p :=
pprod.cases_on p (λ a b, rfl)

@[simp] theorem «forall» {p : pprod α β → Prop} : (∀ x, p x) ↔ (∀ a b, p ⟨a, b⟩) :=
⟨assume h a b, h ⟨a, b⟩, assume h ⟨a, b⟩, h a b⟩

@[simp] theorem «exists» {p : pprod α β → Prop} : (∃ x, p x) ↔ (∃ a b, p ⟨a, b⟩) :=
⟨assume ⟨⟨a, b⟩, h⟩, ⟨a, b, h⟩, assume ⟨a, b, h⟩, ⟨⟨a, b⟩, h⟩⟩

theorem forall' {p : α → β → Prop} : (∀ x : pprod α β, p x.1 x.2) ↔ ∀ a b, p a b :=
pprod.forall

theorem exists' {p : α → β → Prop} : (∃ x : pprod α β, p x.1 x.2) ↔ ∃ a b, p a b :=
pprod.exists

end pprod

lemma function.injective.pprod_map {f : α → β} {g : γ → δ} (hf : injective f) (hg : injective g) :
  injective (λ x, ⟨f x.1, g x.2⟩ : pprod α γ → pprod β δ) :=
λ ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h,
have A : _ := congr_arg pprod.fst h,
have B : _ := congr_arg pprod.snd h,
congr_arg2 pprod.mk (hf A) (hg B)
