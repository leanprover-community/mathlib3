/-
Copyright (c) 2021 Yaël Dillies, Bhavik Mehta. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yaël Dillies, Bhavik Mehta
-/
import algebra.big_operators.basic
import data.sym.sym2

/-!
# Stars and bars

In this file, we prove the case `n = 2` of stars and bars.

## Informal statement

If we have `n` objects to put in `k` boxes, we can do so in exactly `(n + k - 1).choose k` ways.

## Formal statement

We can identify the `k` boxes with the elements of a fintype `α` of card `k`. Then placing `n`
elements in those boxes corresponds to choosing how many of each element of `α` appear in a multiset
of card `n`. `sym α n` being the subtype of `multiset α` of multisets of card `n`, writing stars
and bars using types gives
```lean
lemma stars_and_bars {α : Type*} [fintype α] (n : ℕ) :
  card (sym α n) = (card α + n - 1).choose n := sorry
```

## TODO

Prove the general case of stars and bars.

## Tags

stars and bars
-/

def multichoose1 (n k : ℕ) := fintype.card (sym (fin n) k)

def multichoose2 (n k : ℕ) := (n + k - 1).choose k

def encode (n k : ℕ) (x : sym (fin n.succ) k.succ) : sym (fin n) k.succ ⊕ sym (fin n.succ) k :=
if h : fin.last n ∈ x then
  sum.inr ⟨x.val.erase (fin.last n), by { rw [multiset.card_erase_of_mem h, x.property], refl }⟩
else begin
  refine sum.inl (x.map (λ a, ⟨if (a : ℕ) = n then 0 else a, _⟩)),
  { split_ifs,
    { rw pos_iff_ne_zero,
      rintro rfl,
      obtain ⟨w, r⟩ := @multiset.exists_mem_of_ne_zero _ x.val (λ h, by simpa [h] using x.property),
      simpa [subsingleton.elim w 0] using r, },
    { cases lt_or_eq_of_le (nat.le_of_lt_succ a.property); solve_by_elim } },
end

def decode (n k : ℕ) : sym (fin n) k.succ ⊕ sym (fin n.succ) k → sym (fin n.succ) k.succ
| (sum.inl x) := x.map (λ a, ⟨a.val, a.property.step⟩)
| (sum.inr x) := (fin.last n)::x

lemma equivalent (n k : ℕ) : sym (fin n.succ) k.succ ≃ sym (fin n) k.succ ⊕ sym (fin n.succ) k :=
{ to_fun := encode n k,
  inv_fun := decode n k,
  left_inv := λ x, begin
    rw encode,
    split_ifs,
    { cases x,
      simpa [decode, sym.cons, sym.erase, subtype.mk.inj_eq] using multiset.cons_erase h },
    { simp only [decode, sym.map_map, subtype.mk.inj_eq, function.comp],
      convert @sym.map_congr _ _ _ _ id _ _,
      { rw sym.map_id },
      { intros a h',
        cases a,
        split_ifs,
        { norm_num at h_1,
          simp_rw h_1 at h',
          exact (h h').elim },
        { norm_num } } },
  end,
  right_inv := begin
    rintro (x|x),
    { cases x with x hx,
      rw [decode, encode],
      split_ifs,
      { obtain ⟨y, v, b⟩ := multiset.mem_map.mp h,
        rw [fin.last, subtype.mk_eq_mk] at b,
        have := y.property,
        rw b at this,
        exact nat.lt_asymm this this, },
      { simp only [sym.map_map, function.comp, fin.val_eq_coe, subtype.mk_eq_mk, fin.coe_mk],
        convert sym.map_congr _,
        { rw multiset.map_id, },
        { rintros ⟨g, hg⟩ h',
          split_ifs with h'',
          { simp only [fin.coe_mk] at h'',
            subst g,
            exact (nat.lt_asymm hg hg).elim, },
          { refl } } } },
    { rw [decode, encode],
      split_ifs,
      { cases x, simp [sym.cons] },
      { apply h,
        cases x,
        simp only [sym.cons],
        apply multiset.mem_cons_self } }
  end }

lemma multichoose1_rec (n k : ℕ) :
  multichoose1 n.succ k.succ = multichoose1 n k.succ + multichoose1 n.succ k :=
by simpa only [multichoose1, fintype.card_sum.symm] using fintype.card_congr (equivalent n k)

lemma multichoose2_rec (n k : ℕ) :
  multichoose2 n.succ k.succ = multichoose2 n k.succ + multichoose2 n.succ k :=
by simp [multichoose2, nat.choose_succ_succ, nat.add_comm, nat.add_succ]

lemma multichoose1_eq_multichoose2 : ∀ (n k : ℕ), multichoose1 n k = multichoose2 n k
| 0 0 := by simp [multichoose1, multichoose2]
| 0 (k + 1) := by simp [multichoose1, multichoose2, fintype.card]
| (n + 1) 0 := by simp [multichoose1, multichoose2]
| (n + 1) (k + 1) :=
by simp only [multichoose1_rec, multichoose2_rec, multichoose1_eq_multichoose2 n k.succ,
  multichoose1_eq_multichoose2 n.succ k]

open finset fintype

namespace sym

lemma stars_and_bars {α : Type*} [decidable_eq α] [fintype α] (n : ℕ) :
  fintype.card (sym α n) = (fintype.card α + n - 1).choose n :=
begin
  have start := multichoose1_eq_multichoose2 (fintype.card α) n,
  simp only [multichoose1, multichoose2] at start,
  rw start.symm,
  exact fintype.card_congr (equiv_congr ((@fintype.equiv_fin_of_card_eq α _ (fintype.card α) rfl))),
end

end sym

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
