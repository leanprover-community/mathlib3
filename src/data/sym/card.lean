/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import data.fintype.card
import data.sym.sym2

/-!
# Stars and bars

In this file, we prove the case `n = 2` of stars and bars.

## Informal statement

If we have `n` objects to put in `k` boxes, we can do so in exactly `(n + k - 1).choose n` ways.

## Formal statement

We can identify the `k` boxes with the elements of a fintype `α` of card `k`. Then placing `n`
elements in those boxes corresponds to choosing how many of each element of `α` appear in a multiset
of card `n`. `sym α n` being the subtype of `multiset α` of multisets of card `n`, writing stars
and bars using types gives
```lean
-- TODO: this lemma is not yet proven
lemma stars_and_bars {α : Type*} [fintype α] (n : ℕ) :
  card (sym α n) = (card α + n - 1).choose (card α) := sorry
```

## TODO

Prove the general case of stars and bars.

## Tags

stars and bars
-/

open finset fintype

namespace sym2
variables {α : Type*} [decidable_eq α]

/-- The `diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.card`. -/
lemma card_image_diag (s : finset α) :
  (s.diag.image quotient.mk).card = s.card :=
begin
  rw [card_image_of_inj_on, diag_card],
  rintro ⟨x₀, x₁⟩ hx _ _ h,
  cases quotient.eq.1 h,
  { refl },
  { simp only [mem_coe, mem_diag] at hx,
    rw hx.2 }
end

lemma two_mul_card_image_off_diag (s : finset α) :
  2 * (s.off_diag.image quotient.mk).card = s.off_diag.card :=
begin
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
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩); rw mem_off_diag; exact ⟨‹_›, ‹_›, ‹_›⟩ }, -- hxy' is used here
  rw [this, card_insert_of_not_mem, card_singleton],
  simp only [not_and, prod.mk.inj_iff, mem_singleton],
  exact λ _, hxy',
end

/-- The `off_diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.off_diag.card / 2`.
This is because every element `⟦(x, y)⟧` of `sym2 α` not on the diagonal comes from exactly two
pairs: `(x, y)` and `(y, x)`. -/
lemma card_image_off_diag (s : finset α) :
  (s.off_diag.image quotient.mk).card = s.card.choose 2 :=
by rw [nat.choose_two_right, mul_tsub, mul_one, ←off_diag_card,
  nat.div_eq_of_eq_mul_right zero_lt_two (two_mul_card_image_off_diag s).symm]

lemma card_subtype_diag [fintype α] :
  card {a : sym2 α // a.is_diag} = card α :=
begin
  convert card_image_diag (univ : finset α),
  rw [fintype.card_of_subtype, ←filter_image_quotient_mk_is_diag],
  rintro x,
  rw [mem_filter, univ_product_univ, mem_image],
  obtain ⟨a, ha⟩ := quotient.exists_rep x,
  exact and_iff_right ⟨a, mem_univ _, ha⟩,
end

lemma card_subtype_not_diag [fintype α] :
  card {a : sym2 α // ¬a.is_diag} = (card α).choose 2 :=
begin
  convert card_image_off_diag (univ : finset α),
  rw [fintype.card_of_subtype, ←filter_image_quotient_mk_not_is_diag],
  rintro x,
  rw [mem_filter, univ_product_univ, mem_image],
  obtain ⟨a, ha⟩ := quotient.exists_rep x,
  exact and_iff_right ⟨a, mem_univ _, ha⟩,
end

protected lemma card [fintype α] :
  card (sym2 α) = card α * (card α + 1) / 2 :=
by rw [←fintype.card_congr (@equiv.sum_compl _ is_diag (sym2.is_diag.decidable_pred α)),
  fintype.card_sum, card_subtype_diag, card_subtype_not_diag, nat.choose_two_right, add_comm,
  ←nat.triangle_succ, nat.succ_sub_one, mul_comm]

end sym2
