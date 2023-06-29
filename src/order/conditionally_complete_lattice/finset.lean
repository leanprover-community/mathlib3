/-
Copyright (c) 2018 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import order.conditionally_complete_lattice.basic
import data.set.finite

/-!
# Conditionally complete lattices and finite sets.

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

-/

open set

variables {α β γ : Type*}

section conditionally_complete_lattice
variables [conditionally_complete_lattice α] {s t : set α} {a b : α}

lemma finset.nonempty.sup'_eq_cSup_image {s : finset β} (hs : s.nonempty) (f : β → α) :
  s.sup' hs f = Sup (f '' s) :=
eq_of_forall_ge_iff $ λ a,
  by simp [cSup_le_iff (s.finite_to_set.image f).bdd_above (hs.to_set.image f)]

lemma finset.nonempty.sup'_id_eq_cSup {s : finset α} (hs : s.nonempty) :
  s.sup' hs id = Sup s :=
by rw [hs.sup'_eq_cSup_image, image_id]

end conditionally_complete_lattice

section conditionally_complete_linear_order
variables [conditionally_complete_linear_order α] {s t : set α} {a b : α}

lemma finset.nonempty.cSup_eq_max' {s : finset α} (h : s.nonempty) : Sup ↑s = s.max' h :=
eq_of_forall_ge_iff $ λ a, (cSup_le_iff s.bdd_above h.to_set).trans (s.max'_le_iff h).symm

lemma finset.nonempty.cInf_eq_min' {s : finset α} (h : s.nonempty) : Inf ↑s = s.min' h :=
@finset.nonempty.cSup_eq_max' αᵒᵈ _ s h

lemma finset.nonempty.cSup_mem {s : finset α} (h : s.nonempty) : Sup (s : set α) ∈ s :=
by { rw h.cSup_eq_max', exact s.max'_mem _ }

lemma finset.nonempty.cInf_mem {s : finset α} (h : s.nonempty) : Inf (s : set α) ∈ s :=
@finset.nonempty.cSup_mem αᵒᵈ _ _ h

lemma set.nonempty.cSup_mem (h : s.nonempty) (hs : s.finite) : Sup s ∈ s :=
by { lift s to finset α using hs, exact finset.nonempty.cSup_mem h }

lemma set.nonempty.cInf_mem (h : s.nonempty) (hs : s.finite) : Inf s ∈ s :=
@set.nonempty.cSup_mem αᵒᵈ _ _ h hs

lemma set.finite.cSup_lt_iff (hs : s.finite) (h : s.nonempty) : Sup s < a ↔ ∀ x ∈ s, x < a :=
⟨λ h x hx, (le_cSup hs.bdd_above hx).trans_lt h, λ H, H _ $ h.cSup_mem hs⟩

lemma set.finite.lt_cInf_iff (hs : s.finite) (h : s.nonempty) : a < Inf s ↔ ∀ x ∈ s, a < x :=
@set.finite.cSup_lt_iff αᵒᵈ _ _ _ hs h

end conditionally_complete_linear_order

/-!
### Relation between `Sup` / `Inf` and `finset.sup'` / `finset.inf'`

Like the `Sup` of a `conditionally_complete_lattice`, `finset.sup'` also requires the set to be
non-empty. As a result, we can translate between the two.
-/

namespace finset

lemma sup'_eq_cSup_image [conditionally_complete_lattice β] (s : finset α) (H) (f : α → β) :
  s.sup' H f = Sup (f '' s) :=
begin
  apply le_antisymm,
  { refine (finset.sup'_le _ _ $ λ a ha, _),
    refine le_cSup ⟨s.sup' H f, _⟩ ⟨a, ha, rfl⟩,
    rintros i ⟨j, hj, rfl⟩,
    exact finset.le_sup' _ hj },
  { apply cSup_le ((coe_nonempty.mpr H).image _),
    rintros _ ⟨a, ha, rfl⟩,
    exact finset.le_sup' _ ha, }
end

lemma inf'_eq_cInf_image [conditionally_complete_lattice β] (s : finset α) (H) (f : α → β) :
  s.inf' H f = Inf (f '' s) :=
@sup'_eq_cSup_image _ βᵒᵈ _ _ H _

lemma sup'_id_eq_cSup [conditionally_complete_lattice α] (s : finset α) (H) :
  s.sup' H id = Sup s :=
by rw [sup'_eq_cSup_image s H, set.image_id]

lemma inf'_id_eq_cInf [conditionally_complete_lattice α] (s : finset α) (H) :
  s.inf' H id = Inf s :=
@sup'_id_eq_cSup αᵒᵈ _ _ H

end finset
