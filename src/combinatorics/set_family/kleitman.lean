/-
Copyright (c) 2022 Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies
-/
import combinatorics.set_family.harris_kleitman
import combinatorics.set_family.intersecting

/-!
# Kleitman's bound on the size of intersecting families

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

An intersecting family on `n` elements has size at most `2ⁿ⁻¹`, so we could naïvely think that two
intersecting families could cover all `2ⁿ` sets. But actually that's not case because for example
none of them can contain the empty set. Intersecting families are in some sense correlated.
Kleitman's bound stipulates that `k` intersecting families cover at most `2ⁿ - 2ⁿ⁻ᵏ` sets.

## Main declarations

* `finset.card_bUnion_le_of_intersecting`: Kleitman's theorem.

## References

* [D. J. Kleitman, *Families of non-disjoint subsets*][kleitman1966]
-/

open finset fintype (card)

variables {ι α : Type*} [fintype α] [decidable_eq α] [nonempty α]

/-- **Kleitman's theorem**. An intersecting family on `n` elements contains at most `2ⁿ⁻¹` sets, and
each further intersecting family takes at most half of the sets that are in no previous family. -/
lemma finset.card_bUnion_le_of_intersecting (s : finset ι) (f : ι → finset (finset α))
  (hf : ∀ i ∈ s, (f i : set (finset α)).intersecting) :
  (s.bUnion f).card ≤ 2 ^ card α - 2 ^ (card α - s.card) :=
begin
  obtain hs | hs := le_total (card α) s.card,
  { rw [tsub_eq_zero_of_le hs, pow_zero],
    refine (card_le_of_subset $  bUnion_subset.2 $ λ i hi a ha, mem_compl.2 $ not_mem_singleton.2 $
      (hf _ hi).ne_bot ha).trans_eq _,
    rw [card_compl, fintype.card_finset, card_singleton] },
  induction s using finset.cons_induction with i s hi ih generalizing f,
  { simp },
  classical,
  set f' : ι → finset (finset α) := λ j,
    if hj : j ∈ cons i s hi then (hf j hj).exists_card_eq.some else ∅ with hf',
  have hf₁ : ∀ j, j ∈ cons i s hi →
    f j ⊆ f' j ∧ 2 * (f' j).card = 2 ^ card α ∧ (f' j : set (finset α)).intersecting,
  { rintro j hj,
    simp_rw [hf', dif_pos hj, ←fintype.card_finset],
    exact classical.some_spec (hf j hj).exists_card_eq },
  have hf₂ : ∀ j, j ∈ cons i s hi → is_upper_set (f' j : set (finset α)),
  { refine λ j hj, (hf₁ _ hj).2.2.is_upper_set' ((hf₁ _ hj).2.2.is_max_iff_card_eq.2 _),
    rw fintype.card_finset,
    exact (hf₁ _ hj).2.1 },
  refine (card_le_of_subset $ bUnion_mono $ λ j hj, (hf₁ _ hj).1).trans _,
  nth_rewrite 0 cons_eq_insert i,
  rw bUnion_insert,
  refine (card_mono $ @le_sup_sdiff _ _ _ $ f' i).trans ((card_union_le _ _).trans _),
  rw [union_sdiff_left, sdiff_eq_inter_compl],
  refine le_of_mul_le_mul_left _ (pow_pos zero_lt_two $ card α + 1),
  rw [pow_succ', mul_add, mul_assoc, mul_comm _ 2, mul_assoc],
  refine (add_le_add ((mul_le_mul_left $ pow_pos (zero_lt_two' ℕ) _).2
    (hf₁ _ $ mem_cons_self _ _).2.2.card_le) $ (mul_le_mul_left $ zero_lt_two' ℕ).2 $
    is_upper_set.card_inter_le_finset _ _).trans _,
  { rw coe_bUnion,
    exact is_upper_set_Union₂ (λ i hi, hf₂ _ $ subset_cons _ hi) },
  { rw coe_compl,
    exact (hf₂ _ $ mem_cons_self _ _).compl },
  rw [mul_tsub, card_compl, fintype.card_finset, mul_left_comm, mul_tsub,
    (hf₁ _ $ mem_cons_self _ _).2.1, two_mul, add_tsub_cancel_left, ←mul_tsub, ←mul_two, mul_assoc,
    ←add_mul, mul_comm],
  refine mul_le_mul_left' _ _,
  refine (add_le_add_left (ih ((card_le_of_subset $ subset_cons _).trans hs) _ $ λ i hi,
    (hf₁ _ $ subset_cons _ hi).2.2) _).trans _,
  rw [mul_tsub, two_mul, ←pow_succ, ←add_tsub_assoc_of_le (pow_le_pow' (one_le_two : (1 : ℕ) ≤ 2)
    tsub_le_self), tsub_add_eq_add_tsub hs, card_cons, add_tsub_add_eq_tsub_right],
end
