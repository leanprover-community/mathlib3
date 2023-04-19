/-
Copyright (c) 2018 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro, Kenny Lau
-/

import data.finset.basic

/-!
# Finsets of ordered types

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

universes u v w
variables {α : Type u}

theorem directed.finset_le {r : α → α → Prop} [is_trans α r]
  {ι} [hι : nonempty ι] {f : ι → α} (D : directed r f) (s : finset ι) :
  ∃ z, ∀ i ∈ s, r (f i) (f z) :=
show ∃ z, ∀ i ∈ s.1, r (f i) (f z), from
multiset.induction_on s.1 (let ⟨z⟩ := hι in ⟨z, λ _, false.elim⟩) $
λ i s ⟨j, H⟩, let ⟨k, h₁, h₂⟩ := D i j in
⟨k, λ a h, or.cases_on (multiset.mem_cons.1 h)
  (λ h, h.symm ▸ h₁)
  (λ h, trans (H _ h) h₂)⟩

lemma finset.exists_le [nonempty α] [preorder α] [is_directed α (≤)] (s : finset α) :
  ∃ M, ∀ i ∈ s, i ≤ M :=
directed_id.finset_le _
