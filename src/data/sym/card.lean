/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import data.sym.sym2

/-!
# Stars and bars

In this file, we prove the case `k = 2` of stars and bars.

## Informal statement

If we have `n` objects to put in `k` boxes, we can do so in exactly `(n + k - 1).choose n` ways.

## Formal statement

We can identify the `k` boxes with the elements of a fintype `α` of card `k`. Then placing `n`
elements in those boxes corresponds to choosing how many of each element of `α` appear in a multiset
of card `n`. `sym α n` being the subtype of `multiset α` of multisets of card `n`, our type stars
and bars can be written as
```lean
lemma stars_and_bars {α : Type*} [fintype α] (n : ℕ) :
  card (sym α n) = (card α + n - 1).choose (card α) := sorry
```

## TODO

Prove the general case of stars and bars.
-/

open finset fintype

namespace sym2
variables {α : Type*} [decidable_eq α]

/-- The `off_diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.card.choose 2`. -/
lemma card_image_off_diag (s : finset α) :
  (s.off_diag.image quotient.mk).card = s.card.choose 2 :=
begin
  rw [nat.choose_two_right, nat.mul_sub_left_distrib, mul_one, ←off_diag_card],
  refine (nat.div_eq_of_eq_mul_right zero_lt_two _).symm,
  rw [card_eq_sum_card_fiberwise
    (λ x, mem_image_of_mem _ : ∀ x ∈ s.off_diag, quotient.mk x ∈ s.off_diag.image quotient.mk),
    sum_const_nat (quotient.ind _), mul_comm],
  rintro ⟨x, y⟩ hxy,
  simp_rw [mem_image, exists_prop, mem_off_diag, quotient.eq] at hxy,
  obtain ⟨a, ⟨ha₁, ha₂, ha⟩, h⟩ := hxy,
  obtain ⟨hx, hy, hxy⟩ : x ∈ s ∧ y ∈ s ∧ x ≠ y,
  { cases h; have := ha.symm; exact ⟨‹_›, ‹_›, ‹_›⟩ },
  have hxy' : y ≠ x := hxy.symm,
  have : s.off_diag.filter (λ z, ⟦z⟧ = ⟦(x, y)⟧) = ({(x, y), (y, x)} : finset _),
  { ext ⟨x₁, y₁⟩,
    rw [mem_filter, mem_insert, mem_singleton, sym2.eq_iff, prod.mk.inj_iff, prod.mk.inj_iff,
      and_iff_right_iff_imp],
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); rw mem_off_diag; exact ⟨‹_›, ‹_›, ‹_›⟩ },
  rw [this, card_insert_of_not_mem, card_singleton],
  simp only [not_and, prod.mk.inj_iff, mem_singleton],
  exact λ _, hxy',
end

lemma card_sym2_not_diag [fintype α] :
  (univ.filter (λ (a : sym2 α), ¬a.is_diag)).card = (card α).choose 2 :=
begin
  convert card_image_off_diag (univ : finset α),
  rw ←filter_image_quotient_mk,
  congr,
end

protected lemma card [fintype α] :
  card (sym2 α) = card α * (card α + 1) / 2 :=
begin
  have h : univ.filter (is_diag : sym2 α → Prop) = univ.image sym2.diag,
  { ext x,
    rw [mem_filter, mem_image, is_diag_iff_mem_range_diag, set.mem_range],
    exact ⟨λ ⟨_, a, ha⟩, ⟨a, mem_univ _, ha⟩, λ ⟨a, _, ha⟩, ⟨mem_univ _, a, ha⟩⟩ },
  rw [←card_univ, ←filter_card_add_filter_neg_card_eq_card sym2.is_diag, h,
    card_image_of_injective _ sym2.diag_injective, card_sym2_not_diag,
    nat.choose_two_right, card_univ, add_comm, ←nat.triangle_succ, nat.succ_sub_one,
    mul_comm],
end

end sym2
