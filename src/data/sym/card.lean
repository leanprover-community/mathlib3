/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import data.finset.sym
import tactic.slim_check

/-!
# Stars and bars

In this file, we prove stars and bars.

## Informal statement

If we have `k` objects to put in `n` boxes, we can do so in exactly `(n + k - 1).choose k` ways.
Equivalently, given an alphabet of `n` letters, the number of multisets of size `k` we can form
over this alphabet is `(n + k - 1).choose k`.

## Formal statement

We can identify the `n` boxes with the elements of a fintype `α` of card `n`. Then placing `k`
elements in those boxes corresponds to choosing how many of each element of `α` appear in a multiset
of card `k`. `sym α k` being the subtype of `multiset α` of multisets of card `k`,
the statement of stars and bars is:
```lean
lemma stars_and_bars {α : Type*} [fintype α] (k : ℕ) :
  card (sym α k) = (card α + k - 1).choose k := sorry
```

## Tags

stars and bars
-/

open finset fintype function sum

variables {α β : Type*}

namespace sym

section
variables (α) (n : ℕ)

/-- The `encode` function produces a `sym α n.succ` if the input doesn't contain `none` by casting
`option α` to `α`. Otherwise, the function removes an occurrence of `none` from the input and
produces a `sym (option α) n`. -/
def encode [decidable_eq α] (s : sym (option α) n.succ) : sym α n.succ ⊕ sym (option α) n :=
if h : none ∈ s
then inr (s.erase none h)
else inl (s.attach.map $ λ o,
  option.get $ option.ne_none_iff_is_some.1 $ ne_of_mem_of_not_mem o.2 h)

/-- From the output of `encode`, the `decode` function reconstructs the original input. If the
output contains `n + 1` elements, the original input can be reconstructed by casting `α` back
to `option α`. Otherwise, an instance of `none` has been removed and the input can be
reconstructed by adding it back. -/
def decode : sym α n.succ ⊕ sym (option α) n → sym (option α) n.succ
| (inl s) := s.map embedding.coe_option
| (inr s) := none :: s

variables {α n}

@[simp] lemma decode_inl (s : sym α n.succ) : decode α n (inl s) = s.map embedding.coe_option := rfl
@[simp] lemma decode_inr (s : sym (option α) n) : decode α n (inr s) = none :: s := rfl

variables (α n)

/-- As `encode` and `decode` are inverses of each other, `sym (option α) n.succ` is equivalent
to `sym α n.succ ⊕ sym (option α) n`. -/
def option_succ_equiv [decidable_eq α] : sym (option α) n.succ ≃ sym α n.succ ⊕ sym (option α) n :=
{ to_fun := encode α n,
  inv_fun := decode α n,
  left_inv := λ s, begin
    unfold encode,
    split_ifs,
    { exact cons_erase _ },
    { simp only [decode, map_map, subtype.mk.inj_eq, comp, option.coe_get,
        embedding.coe_option_apply, subtype.val_eq_coe, map_map],
      convert s.attach_map_coe, },
  end,
  right_inv := begin
    rintro (s | s),
    { unfold encode,
      split_ifs,
      { obtain ⟨a, _, ha⟩ := multiset.mem_map.mp h,
        exact option.some_ne_none _ ha },
      { refine map_injective (option.some_injective _) _ _,
        convert eq.trans _ (decode α n (inl s)).attach_map_coe,
        simp } },
    { exact (dif_pos $ mem_cons_self _ _).trans (congr_arg _ $ erase_cons_head s _ _) }
  end }

end

/-- `multichoose n k` is the number of multisets of cardinality `k` from a type of cardinality `n`.
That is, it's the number of ways to select `k` items (up to permutation) from `n` items
with replacement.

This is defined as `nat.choose (n + k - 1) k`. It is related to the cardinality of `sym` in
`sym.multichoose_eq`. -/
def multichoose (n k : ℕ) := (n + k - 1).choose k

lemma card_sym_rec (n : ℕ)
  [fintype (sym (option α) n.succ)] [fintype (sym α n.succ)] [fintype (sym (option α) n)] :
  card (sym (option α) n.succ) = card (sym α n.succ) + card (sym (option α) n) :=
by { classical, simpa only [card_sum.symm] using fintype.card_congr (option_succ_equiv α n) }

lemma multichoose_rec (n k : ℕ) :
  multichoose n.succ k.succ = multichoose n k.succ + multichoose n.succ k :=
by simp [multichoose, nat.choose_succ_succ, nat.add_comm, nat.add_succ]

lemma multichoose_eq (α : Type*) [hα : fintype α] (k : ℕ) [fintype (sym α k)] :
  multichoose (card α) k = card (sym α k) :=
begin
  classical,
  generalize hn : card α + k = n,
  unfreezingI { induction n with n ih generalizing α k },
  { unfreezingI { obtain ⟨hn, rfl⟩ := add_eq_zero_iff.mp hn },
    simp [multichoose, hn], },
  { have : 0 < card α + k := by convert nat.succ_pos',
    unfreezingI { cases k },
    { haveI hne : nonempty α := card_pos_iff.mp this,
      simp [multichoose], },
    { obtain (hi|hi) := is_empty_or_nonempty α; haveI := hi,
      { simp [multichoose, fintype.card_eq_zero], },
      { haveI : inhabited α := classical.inhabited_of_nonempty (by assumption),
        obtain ⟨β, βeqv⟩ := equiv.sigma_equiv_option_of_inhabited α,
        haveI : fintype β := fintype_of_option_equiv βeqv,
        have βc : card β + k + 1 = n,
        { simpa [fintype.card_congr βeqv,
            nat.add_succ, nat.succ_add, add_zero, card_option] using hn },
        have ih' := ih _ (k + 1) βc,
        transitivity card (sym (option β) k.succ),
        { rw [card_sym_rec, ← ih', fintype.card_congr βeqv, card_option, multichoose_rec],
          have ih'' := ih α k,
          rw [fintype.card_congr βeqv, card_option] at ih'',
          specialize ih'' (by simpa [add_comm, add_assoc, add_left_comm] using βc),
          rw [add_right_inj, ih''],
          apply fintype.card_congr (sym.equiv_congr βeqv), },
        { apply fintype.card_congr (sym.equiv_congr βeqv.symm), } } } },
end

/-- The *stars and bars* lemma: the cardinality of `sym α k` is equal to
`nat.choose (card α + k - 1) k`. -/
lemma stars_and_bars {α : Type*} [fintype α] (k : ℕ) [fintype (sym α k)] :
  card (sym α k) = (card α + k - 1).choose k :=
by simpa only [multichoose] using (multichoose_eq α k).symm

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
  rintro m he,
  rw [inf_eq_inter, mem_inter, mem_image, mem_image] at he,
  obtain ⟨⟨a, ha, rfl⟩, b, hb, hab⟩ := he,
  refine not_is_diag_mk_of_mem_off_diag hb _,
  rw hab,
  exact is_diag_mk_of_mem_diag ha,
end

/-- Type **stars and bars** for the case `n = 2`. -/
protected lemma card [fintype α] : card (sym2 α) = card α * (card α + 1) / 2 := finset.card_sym2 _

end sym2
