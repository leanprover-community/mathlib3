/-
Copyright (c) 2022 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import data.finset.pointwise
import group_theory.group_action.fixing_subgroup

/-!
# Kneser's theorem

This file proves Kneser's theorem. This states that `|s + H| + |t + H| - |H| ≤ |s + t|` where `s`,
`t` are finite nonempty sets in a commutative group and `H` is the stabilizer of `s + t`.

## Main declarations

* `finset.mul_stab`: The stabilizer of a **nonempty** finset as a finset.
* `finset.mul_kneser`: Kneser's theorem.

## References

* [Imre Ruzsa, *Sumsets and structure][ruzsa2009]
-/

open_locale pointwise

namespace finset
variables {ι α : Type*}

/-! ### Stabilizer of a finset -/

section stab
variables [group α] [decidable_eq α] {s t : finset α} {a : α}

/-- The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`.-/
@[to_additive "The stabilizer of `s` as a finset. As an exception, this sends `∅` to `∅`."]
def mul_stab (s : finset α) : finset α := (s / s).filter $ λ a, ∀ ⦃b⦄, b ∈ s → a * b ∈ s

@[simp, to_additive]
lemma mem_mul_stab (hs : s.nonempty) : a ∈ s.mul_stab ↔ ∀ ⦃b⦄, b ∈ s → a * b ∈ s :=
begin
  rw [mul_stab, mem_filter, mem_div, and_iff_right_of_imp],
  obtain ⟨b, hb⟩ := hs,
  exact λ h, ⟨_, _, h hb, hb, mul_div_cancel'' _ _⟩,
end

@[simp, to_additive] lemma mul_stab_empty : mul_stab (∅ : finset α) = ∅ := by simp [mul_stab]
@[simp, to_additive] lemma mul_stab_singleton (a : α) : mul_stab ({a} : finset α) = 1 :=
by simp [mul_stab, singleton_one]

@[to_additive] lemma nonempty.of_mul_stab : s.mul_stab.nonempty → s.nonempty :=
by { simp_rw [nonempty_iff_ne_empty, not_imp_not], rintro rfl, exact mul_stab_empty }

@[simp, to_additive] lemma one_mem_mul_stab : (1 : α) ∈ s.mul_stab ↔ s.nonempty :=
⟨λ h, nonempty.of_mul_stab ⟨_, h⟩, λ h, (mem_mul_stab h).2 $ λ a ha, by rwa one_mul⟩

@[to_additive] lemma nonempty.mul_stab (h : s.nonempty) : s.mul_stab.nonempty :=
⟨_, one_mem_mul_stab.2 h⟩

@[simp, to_additive] lemma mul_stab_nonempty : s.mul_stab.nonempty ↔ s.nonempty :=
⟨nonempty.of_mul_stab, nonempty.mul_stab⟩

@[to_additive] lemma le_card_union_add_card_mul_stab_union :
  min (s.card + s.mul_stab.card) (t.card + t.mul_stab.card) ≤
    (s ∪ t).card + (s ∪ t).mul_stab.card := sorry

end stab

variables [comm_group α] [decidable_eq α] {s t : finset α} {a : α}

/-- **Kneser's theorem**: A bound on the size of `s * t` in terms of its stabilizer. -/
@[to_additive "**Kneser's theorem**: A bound on the size of `s + t` in terms of its stabilizer."]
lemma mul_kneser (s t : finset α) :
  (s * (s * t).mul_stab).card + (t * (s * t).mul_stab).card ≤
    (s * t).card + (s * t).mul_stab.card :=
begin
  classical,
  have key : ∀ b, ∃ n (s' t' : finset α), (b ∈ t → b ∈ t') ∧ t'.card = n ∧
    s.card + t.card = s'.card + t'.card ∧ s ⊆ s' ∧ s' * t' ⊆ s * t :=
    λ b, ⟨_, s, t, id, rfl, rfl, subset.rfl, subset.rfl⟩,
  choose s' t' htt' ht' hst hss' hst' using λ b, nat.find_spec (key b),
  have hUnion : t.bUnion (λ b, s' b * t' b) = s * t,
  { exact subset.antisymm (bUnion_subset.2 $ λ b hb, hst' _)
    (mul_subset_iff.2 $ λ a ha b hb, mem_bUnion.2 ⟨b, hb, mul_mem_mul (hss' _ ha) $ htt' _ hb⟩) },
  sorry
end

end finset
