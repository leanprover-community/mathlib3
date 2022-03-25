/-
Copyright (c) 2022 Anatole Dedecker. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anatole Dedecker
-/
import topology.bornology.basic

/-!
# TODO
-/

open set filter function

variables {α β : Type*} {b₁ b₂ : bornology α}

namespace bornology

lemma cobounded_injective : injective (@cobounded α) :=
λ b₁ b₂ h, by ext; rw h

instance : partial_order (bornology α) := partial_order.lift
  (_ : bornology α → order_dual (filter α)) cobounded_injective

protected lemma le_def : b₁ ≤ b₂ ↔ b₂.cobounded ≤ b₁.cobounded := iff.rfl
protected lemma le_iff : b₁ ≤ b₂ ↔ (∀ s, @is_bounded _ b₁ s → @is_bounded _ b₂ s) := sorry

instance : has_Inf (bornology α) :=
⟨λ S, ⟨Sup (@cobounded α '' S), Sup_le (λ f ⟨b, hb, hbf⟩, hbf ▸ b.le_cofinite)⟩⟩

instance : has_Sup (bornology α) :=
⟨λ S, ⟨filter.cofinite ⊓ (Inf (@cobounded α '' S)), inf_le_left⟩⟩

instance : has_inf (bornology α) :=
⟨λ b₁ b₂, ⟨@cobounded α b₁ ⊔ @cobounded α b₂, sup_le b₁.le_cofinite b₂.le_cofinite⟩⟩

instance : has_sup (bornology α) :=
⟨λ b₁ b₂, ⟨@cobounded α b₁ ⊓ @cobounded α b₂, inf_le_of_left_le b₁.le_cofinite⟩⟩

instance : has_bot (bornology α) :=
⟨bornology.cofinite⟩

instance : has_top (bornology α) :=
⟨⟨⊥, bot_le⟩⟩

instance : complete_lattice (bornology α) := injective.complete_lattice
  (_ : bornology α → order_dual (filter α))
  cobounded_injective _ _ _ _ _ _

end bornology
