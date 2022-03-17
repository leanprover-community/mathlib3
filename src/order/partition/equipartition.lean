/-
Copyright (c) 2022 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import data.set.equitable
import order.partition.finpartition

/-!
# Finite equipartitions

This file defines finite equipartitions, the partitions whose parts all are the same size up to a
difference of `1`.

## Main declarations

* `finpartition.is_equipartition`: Predicate for a `finpartition` to be an equipartition.
-/

open finset fintype

namespace finpartition
variables {α : Type*} [decidable_eq α] {s t : finset α} (P : finpartition s)

/-- An equipartition is a partition whose parts are all the same size, up to a difference of `1`. -/
def is_equipartition : Prop := (P.parts : set (finset α)).equitable_on card

lemma is_equipartition_iff_card_parts_eq_average : P.is_equipartition ↔
  ∀ a : finset α, a ∈ P.parts → a.card = s.card/P.parts.card ∨ a.card = s.card/P.parts.card + 1 :=
by simp_rw [is_equipartition, finset.equitable_on_iff, P.sum_card_parts]

variables {P}

lemma _root_.set.subsingleton.is_equipartition (h : (P.parts : set (finset α)).subsingleton) :
  P.is_equipartition :=
h.equitable_on _

lemma is_equipartition.average_le_card_part (hP : P.is_equipartition) (ht : t ∈ P.parts) :
  s.card / P.parts.card ≤ t.card :=
by { rw ←P.sum_card_parts, exact equitable_on.le hP ht }

lemma is_equipartition.card_part_le_average_add_one (hP : P.is_equipartition) (ht : t ∈ P.parts) :
  t.card ≤ s.card / P.parts.card + 1 :=
by { rw ←P.sum_card_parts, exact equitable_on.le_add_one hP ht }

/-! ### Discrete and indiscrete finpartition -/

variables (s)

lemma bot_is_equipartition : (⊥ : finpartition s).is_equipartition :=
set.equitable_on_iff_exists_eq_eq_add_one.2 ⟨1, by simp⟩

lemma top_is_equipartition : (⊤ : finpartition s).is_equipartition :=
(parts_top_subsingleton _).is_equipartition

lemma indiscrete_is_equipartition {hs : s ≠ ∅} : (indiscrete hs).is_equipartition :=
by { rw [is_equipartition, indiscrete_parts, coe_singleton], exact set.equitable_on_singleton s _ }

end finpartition
