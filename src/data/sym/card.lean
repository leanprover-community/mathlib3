/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta, Huỳnh Trần Khanh, Stuart Presnell
-/
import algebra.big_operators.basic
import data.finset.sym
import data.fintype.sum

/-!
# Stars and bars

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

In this file, we prove (in `sym.card_sym_eq_multichoose`) that the function `multichoose n k`
defined in `data/nat/choose/basic` counts the number of multisets of cardinality `k` over an
alphabet of cardinality `n`. In conjunction with `nat.multichoose_eq` proved in
`data/nat/choose/basic`, which shows that `multichoose n k = choose (n + k - 1) k`,
this is central to the "stars and bars" technique in combinatorics, where we switch between
counting multisets of size `k` over an alphabet of size `n` to counting strings of `k` elements
("stars") separated by `n-1` dividers ("bars").

## Informal statement

Many problems in mathematics are of the form of (or can be reduced to) putting `k` indistinguishable
objects into `n` distinguishable boxes; for example, the problem of finding natural numbers
`x1, ..., xn` whose sum is `k`. This is equivalent to forming a multiset of cardinality `k` from
an alphabet of cardinality `n` -- for each box `i ∈ [1, n]` the multiset contains as many copies
of `i` as there are items in the `i`th box.

The "stars and bars" technique arises from another way of presenting the same problem. Instead of
putting `k` items into `n` boxes, we take a row of `k` items (the "stars") and separate them by
inserting `n-1` dividers (the "bars").  For example, the pattern `*|||**|*|` exhibits 4 items
distributed into 6 boxes -- note that any box, including the first and last, may be empty.
Such arrangements of `k` stars and `n-1` bars are in 1-1 correspondence with multisets of size `k`
over an alphabet of size `n`, and are counted by `choose (n + k - 1) k`.

Note that this problem is one component of Gian-Carlo Rota's "Twelvefold Way"
https://en.wikipedia.org/wiki/Twelvefold_way

## Formal statement

Here we generalise the alphabet to an arbitrary fintype `α`, and we use `sym α k` as the type of
multisets of size `k` over `α`. Thus the statement that these are counted by `multichoose` is:
`sym.card_sym_eq_multichoose : card (sym α k) = multichoose (card α) k`
while the "stars and bars" technique gives
`sym.card_sym_eq_choose : card (sym α k) = choose (card α + k - 1) k`


## Tags

stars and bars, multichoose
-/

open finset fintype function sum nat

variables {α β : Type*}

namespace sym

section sym
variables (α) (n : ℕ)

/--
Over `fin n+1`, the multisets of size `k+1` containing `0` are equivalent to those of size `k`,
as demonstrated by respectively erasing or appending `0`.
-/
protected def E1 {n k : ℕ} :
  {s : sym (fin n.succ) k.succ // ↑0 ∈ s} ≃ sym (fin n.succ) k :=
{ to_fun    := λ s, s.1.erase 0 s.2,
  inv_fun   := λ s, ⟨cons 0 s, mem_cons_self 0 s⟩,
  left_inv  := λ s, by simp,
  right_inv := λ s, by simp }

/--
The multisets of size `k` over `fin n+2` not containing `0`
are equivalent to those of size `k` over `fin n+1`,
as demonstrated by respectively decrementing or incrementing every element of the multiset.
-/
protected def E2 {n k : ℕ} :
  {s : sym (fin n.succ.succ) k // ↑0 ∉ s} ≃ sym (fin n.succ) k :=
{ to_fun    := λ s, map (fin.pred_above 0) s.1,
  inv_fun   := λ s, ⟨map (fin.succ_above 0) s,
    (mt mem_map.1) (not_exists.2 (λ t, (not_and.2 (λ _, (fin.succ_above_ne _ t)))))⟩,
  left_inv  := λ s, by
  { obtain ⟨s, hs⟩ := s,
    simp only [map_map, comp_app],
    nth_rewrite_rhs 0 ←(map_id' s),
    refine sym.map_congr (λ v hv,  _),
    simp [fin.pred_above_zero (ne_of_mem_of_not_mem hv hs)] },
  right_inv := λ s, by
  { simp only [fin.zero_succ_above, map_map, comp_app],
    nth_rewrite_rhs 0 ←(map_id' s),
    refine sym.map_congr (λ v hv,  _),
    rw [←fin.zero_succ_above v, ←@fin.cast_succ_zero n.succ, fin.pred_above_succ_above 0 v] } }

lemma card_sym_fin_eq_multichoose (n k : ℕ) : card (sym (fin n) k) = multichoose n k :=
begin
  apply @pincer_recursion (λ n k, card (sym (fin n) k) = multichoose n k),
  { simp },
  { intros b,
    induction b with b IHb, { simp },
    rw [multichoose_zero_succ, card_eq_zero_iff],
    apply_instance },
  { intros x y h1 h2,
    rw [multichoose_succ_succ, ←h1, ←h2, add_comm],
    cases x,
    { simp only [card_eq_zero_iff, card_unique, self_eq_add_right],
      apply_instance },
    rw ←card_sum,
    refine fintype.card_congr (equiv.symm _),
    apply (equiv.sum_congr sym.E1.symm sym.E2.symm).trans,
    apply equiv.sum_compl },
end

/-- For any fintype `α` of cardinality `n`, `card (sym α k) = multichoose (card α) k` -/
lemma card_sym_eq_multichoose (α : Type*) (k : ℕ) [fintype α] [fintype (sym α k)] :
  card (sym α k) = multichoose (card α) k :=
by { rw ←card_sym_fin_eq_multichoose, exact card_congr (equiv_congr (equiv_fin α)) }

/-- The *stars and bars* lemma: the cardinality of `sym α k` is equal to
`nat.choose (card α + k - 1) k`. -/
lemma card_sym_eq_choose {α : Type*} [fintype α] (k : ℕ) [fintype (sym α k)] :
  card (sym α k) = (card α + k - 1).choose k :=
by rw [card_sym_eq_multichoose, nat.multichoose_eq]

end sym
end sym

namespace sym2
variables [decidable_eq α]

/-- The `diag` of `s : finset α` is sent on a finset of `sym2 α` of card `s.card`. -/
lemma card_image_diag (s : finset α) : (s.diag.image quotient.mk).card = s.card :=
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

/-- Finset **stars and bars** for the case `n = 2`. -/
lemma _root_.finset.card_sym2 (s : finset α) : s.sym2.card = s.card * (s.card + 1) / 2 :=
begin
  rw [←image_diag_union_image_off_diag, card_union_eq, sym2.card_image_diag,
    sym2.card_image_off_diag, nat.choose_two_right, add_comm, ←nat.triangle_succ, nat.succ_sub_one,
    mul_comm],
  rw disjoint_left,
  rintro m ha hb,
  rw [mem_image] at ha hb,
  obtain ⟨⟨a, ha, rfl⟩, ⟨b, hb, hab⟩⟩ := ⟨ha, hb⟩,
  refine not_is_diag_mk_of_mem_off_diag hb _,
  rw hab,
  exact is_diag_mk_of_mem_diag ha,
end

/-- Type **stars and bars** for the case `n = 2`. -/
protected lemma card [fintype α] : card (sym2 α) = card α * (card α + 1) / 2 := finset.card_sym2 _

end sym2
