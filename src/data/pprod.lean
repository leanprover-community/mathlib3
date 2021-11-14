/-
Copyright (c) 2020 Eric Wieser. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Eric Wieser
-/

/-!
# Extra facts about `pprod`
-/

variables {α : Sort*} {β : Sort*}

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
