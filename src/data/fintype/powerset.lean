/-
Copyright (c) 2017 Mario Carneiro. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Carneiro
-/
import data.fintype.card
import data.finset.powerset

/-!
# fintype instance for `set α`, when `α` is a fintype

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.
-/

variables {α : Type*}

open finset

instance finset.fintype [fintype α] : fintype (finset α) :=
⟨univ.powerset, λ x, finset.mem_powerset.2 (finset.subset_univ _)⟩

@[simp] lemma fintype.card_finset [fintype α] :
  fintype.card (finset α) = 2 ^ (fintype.card α) :=
finset.card_powerset finset.univ

@[simp] lemma finset.powerset_univ [fintype α] : (univ : finset α).powerset = univ :=
coe_injective $ by simp [-coe_eq_univ]

@[simp] lemma finset.powerset_eq_univ [fintype α] {s : finset α} : s.powerset = univ ↔ s = univ :=
by rw [←finset.powerset_univ, powerset_inj]

lemma finset.mem_powerset_len_univ_iff [fintype α] {s : finset α} {k : ℕ} :
  s ∈ powerset_len k (univ : finset α) ↔ card s = k :=
mem_powerset_len.trans $ and_iff_right $ subset_univ _

@[simp] lemma finset.univ_filter_card_eq (α : Type*) [fintype α] (k : ℕ) :
  (finset.univ : finset (finset α)).filter (λ s, s.card = k) = finset.univ.powerset_len k :=
by { ext, simp [finset.mem_powerset_len] }

@[simp] lemma fintype.card_finset_len [fintype α] (k : ℕ) :
  fintype.card {s : finset α // s.card = k} = nat.choose (fintype.card α) k :=
by simp [fintype.subtype_card, finset.card_univ]

instance set.fintype [fintype α] : fintype (set α) :=
⟨(@finset.univ α _).powerset.map ⟨coe, coe_injective⟩, λ s, begin
  classical, refine mem_map.2 ⟨finset.univ.filter s, mem_powerset.2 (subset_univ _), _⟩,
  apply (coe_filter _ _).trans, rw [coe_univ, set.sep_univ], refl
end⟩

-- Not to be confused with `set.finite`, the predicate
instance set.finite' [finite α] : finite (set α) :=
by { casesI nonempty_fintype α, apply_instance }

@[simp] lemma fintype.card_set [fintype α] : fintype.card (set α) = 2 ^ fintype.card α :=
(finset.card_map _).trans (finset.card_powerset _)
