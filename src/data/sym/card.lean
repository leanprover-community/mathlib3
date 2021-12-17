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

def encode (n k : ℕ) (x : sym (fin n.succ) k.succ) : (sym (fin n) k.succ) ⊕ (sym (fin n.succ) k) :=
  if h : fin.last n ∈ x.val then sum.inr ⟨x.val.erase (fin.last n), begin
    have := multiset.card_erase_of_mem h,
    rw this,
    rw x.property,
    refl,
  end⟩ else sum.inl ⟨x.val.map (λ a, ⟨if a.val = n then 0 else a.val, begin
    have not_zero : n ≠ 0 := begin
      intro g,
      have := h begin
        cases n,
        { have zero_is_mem := @multiset.exists_mem_of_ne_zero _ x.val begin
            have := x.property,
            intro h,
            rw h at this,
            norm_num at this,
          end,
          cases zero_is_mem with w r,
          rw (subsingleton.elim w 0) at r,
          exact r },
        { norm_num at g },
      end,
      norm_num at this,
    end,
    split_ifs,
    { exact pos_iff_ne_zero.mpr not_zero },
    { have two_branches := lt_or_eq_of_le (nat.le_of_lt_succ a.property),
      cases two_branches,
      { assumption },
      {
        exfalso,
        exact h_1 two_branches,
      } },
  end⟩), begin
    rw multiset.card_map,
    exact x.property,
  end⟩

def decode (n k : ℕ) (x : (sym (fin n) k.succ) ⊕ (sym (fin n.succ) k)) : sym (fin n.succ) k.succ := begin
  cases x,
  { exact ⟨x.val.map (λ a, ⟨a.val, nat.lt.step a.property⟩ : fin n → fin n.succ), begin
      rw multiset.card_map,
      exact x.property,
    end⟩ },
  { exact ⟨multiset.cons (fin.last n) x.val, begin
      rw multiset.card_cons,
      rw x.property,
    end⟩ },
end

lemma equivalent (n k : ℕ) : sym (fin n.succ) k.succ ≃ sym (fin n) k.succ ⊕ sym (fin n.succ) k := begin
  refine ⟨encode n k, decode n k, _, _⟩,
  { rw function.left_inverse,
    intro x,
    rw encode,
    split_ifs,
    { rw decode,
      norm_num,
      have := multiset.cons_erase h,
      norm_num at this,
      simp_rw this,
      norm_num },
    { rw decode,
      simp only [],
      simp_rw multiset.map_map,
      have unpack : x = ⟨x.val, x.property⟩ := begin
        norm_num,
      end,
      conv begin
        to_rhs,
        rw unpack,
      end,
      rw subtype.mk.inj_eq,
      conv begin
        to_rhs,
        rw (@multiset.map_id _ x.val).symm,
      end,
      apply multiset.map_congr,
      intros g hg,
      simp only [function.comp],
      split_ifs,
      { have unpack : g = ⟨g.val, g.property⟩ := begin
          norm_num,
        end,
        have : g = fin.last n := begin
          rw unpack,
          simp_rw [h_1, fin.last],
        end,
        rw this at hg,
        tauto },
      { norm_num } } },
  { rw function.right_inverse,
    rw function.left_inverse,
    intro x,
    cases x,
    { rw decode,
      simp only [],
      rw encode,
      split_ifs,
      { simp only [] at h,
        have y := multiset.mem_map.mp h,
        cases y with y v,
        cases v with v b,
        have u := subtype.mk.inj b,
        have i := y.property,
        rw u at i,
        exact nat.lt_asymm i i },
      { simp_rw multiset.map_map,
        simp only [function.comp],
        have unpack : x = ⟨x.val, x.property⟩ := begin
          norm_num,
        end,
        conv begin
          to_rhs,
          rw unpack,
        end,
        rw subtype.mk.inj_eq,
        conv begin
          to_rhs,
          rw (@multiset.map_id _ x.val).symm,
        end,
        apply multiset.map_congr,
        intros g hg,
        split_ifs,
        { have i := g.property,
          rw h_1 at i,
          exfalso,
          exact lt_irrefl n i },
        { rw id,
          norm_num } },
    },
    { rw decode,
      simp only [],
      rw encode,
      split_ifs,
      { simp_rw multiset.erase_cons_head,
        norm_num },
      { norm_num at h } } },
end

lemma multichoose1_rec (n k : ℕ) : multichoose1 n.succ k.succ = multichoose1 n k.succ + multichoose1 n.succ k := begin
  simp only [multichoose1],
  rw fintype.card_sum.symm,
  exact fintype.card_congr (equivalent n k),
end

lemma multichoose2_rec (n k : ℕ) : multichoose2 n.succ k.succ = multichoose2 n k.succ + multichoose2 n.succ k := begin
  simp only [multichoose2],
  norm_num,
  rw nat.add_succ,
  rw nat.choose_succ_succ,
  ring,
end

lemma multichoose1_eq_multichoose2 : ∀ (n k : ℕ), multichoose1 n k = multichoose2 n k
| 0 0 := begin
  simp only [multichoose1, multichoose2],
  norm_num,
  dec_trivial,
end
| 0 (k + 1) := begin
  simp only [multichoose1, multichoose2],
  norm_num,
  have no_inhabitants : sym (fin 0) k.succ → false := begin
    intro h,
    rw sym at h,
    have w := @multiset.exists_mem_of_ne_zero _ h.val begin
      intro y,
      have z := h.property,
      rw y at z,
      norm_num at z,
    end,
    cases w with w q,
    cases w,
    norm_num at w_property,
  end,
  exact (@fintype.card_eq_zero_iff (sym (fin 0) k.succ) _).mpr ⟨no_inhabitants⟩,
end
| (n + 1) 0 := begin
  simp only [multichoose1, multichoose2],
  norm_num,
  dec_trivial,
end
| (n + 1) (k + 1) := begin
  simp only [multichoose1_rec, multichoose2_rec],
  rw multichoose1_eq_multichoose2 n k.succ,
  rw multichoose1_eq_multichoose2 n.succ k,
end

open finset fintype

namespace sym2

lemma stars_and_bars {α : Type*} [decidable_eq α] [fintype α] (n : ℕ) :
  fintype.card (sym α n) = (fintype.card α + n - 1).choose n := begin
  have start := multichoose1_eq_multichoose2 (fintype.card α) n,
  simp only [multichoose1, multichoose2] at start,
  rw start.symm,
  have bundle := (@fintype.equiv_fin_of_card_eq α _ (fintype.card α) rfl),
  apply fintype.card_congr,
  refine ⟨_, _, _, _⟩,
  { intro x,
    refine ⟨_, _⟩,
    { exact x.val.map (bundle.to_fun) },
    { rw multiset.card_map,
      rw x.property } },
  { intro x,
    refine ⟨_, _⟩,
    { exact x.val.map (bundle.inv_fun) },
    { rw multiset.card_map,
      rw x.property } },
  { rw function.left_inverse,
    intro x,
    simp_rw multiset.map_map,
    have temp := bundle.left_inv,
    rw function.left_inverse at temp,
    simp_rw function.comp,
    have unpack : x = ⟨x.val, x.property⟩ := begin
      norm_num,
    end,
    conv begin
      to_rhs,
      rw unpack,
    end,
    rw subtype.mk.inj_eq,
    conv begin
      to_rhs,
      rw (@multiset.map_id _ x.val).symm,
    end,
    apply multiset.map_congr,
    intros b u,
    rw id,
    rw temp },
  { rw function.right_inverse,
    rw function.left_inverse,
    intro x,
    simp_rw multiset.map_map,
    have temp := bundle.right_inv,
    rw function.right_inverse at temp,
    simp_rw function.comp,
    have unpack : x = ⟨x.val, x.property⟩ := begin
      norm_num,
    end,
    conv begin
      to_rhs,
      rw unpack,
    end,
    rw subtype.mk.inj_eq,
    conv begin
      to_rhs,
      rw (@multiset.map_id _ x.val).symm,
    end,
    apply multiset.map_congr,
    intros b u,
    rw id,
    rw temp },
end

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
