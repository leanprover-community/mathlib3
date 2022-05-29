/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.big_operators.order
import algebra.order.rearrangement
import group_theory.perm.cycle.concrete
import tactic.interval_cases

/-!
# Chebyshev inequality

This file proves the Chebyshev inequality.

Chebyshev's inequality states `(∑ i in s, f i) * ∑ i in s, g i ≤ s.card * ∑ i in s, f i * g i` when
`f g : ι → α` monovary, and the reverse inequality when `f` and `g` antivary.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because it is easily deducible from the `monovary` API.
-/

namespace finset
variables {α : Type*} [fintype α] {s : finset α}

@[simp] lemma coe_eq_univ : (s : set α) = set.univ ↔ s = univ := by rw [←coe_univ, coe_inj]

end finset

section cycle

open equiv equiv.perm set order_dual
open_locale big_operators

variables {α β : Type*} {σ : perm α} {s : set α} {t : set β} {a : α}

lemma list.nodup.is_cycle_on_form_perm [decidable_eq α] {l : list α} (h : l.nodup) :
  l.form_perm.is_cycle_on {a | a ∈ l} :=
begin
  sorry
end

-- where to move?
lemma set.product_self (π : perm α) (hπ : π.is_cycle_on s) :
  s ×ˢ s = ⋃ n : ℤ, (λ a, (a, (π ^ n) a)) '' s :=
begin
  ext,
  simp,
end

end cycle

section to_move

open equiv equiv.perm set order_dual
open_locale big_operators

variables {ι α β : Type*} [semiring α] [add_comm_monoid β] [module α β] {s : set ι} {σ : perm ι}
  {f : ι → α} {g : ι → β} {i : ι}

-- where to move?
lemma sum_mul_sum_eq_sum_perm [decidable_eq ι] (s : finset ι) (π : perm s) (hπ : π.is_cycle)
  (hπs : π.support = finset.univ) : (∑ i in s, f i) • (∑ i in s, g i) =
    ∑ k in finset.range s.card, (∑ i in s, f i • g ((π^k).subtype_congr (equiv.refl _) i)) :=
begin
  rw [finset.sum_smul_sum, finset.product_self_eq_range_bUnion_perm π hπ hπs, finset.sum_bUnion _],
end

-- where to move?
lemma finset.product_self [decidable_eq ι] (π : perm ι) (hπ : π.is_cycle_on s) :
  s.product s =
  (finset.range s.card).bUnion (λ k, s.map ⟨λ i, (i, (π ^ k) i), λ i j, congr_arg prod.fst⟩) :=
begin
  ext,
  obtain hs | hs := eq_or_ne s.card 0,
  { simp only [finset.card_eq_zero.mp hs, mem_product, not_mem_empty, and_self, card_empty,
      range_zero, bUnion_empty] },
  simp only [mem_bUnion, mem_range, mem_singleton, exists_prop, mem_product],
  refine ⟨λ h, _, λ h, _⟩,
  { have hπ1 : π ⟨a.1, h.1⟩ ≠ ⟨a.1, h.1⟩,
    { simp only [← equiv.perm.mem_support, hπs, mem_univ] },
    have hπ2 : π ⟨a.2, h.2⟩ ≠ ⟨a.2, h.2⟩,
    { simp only [← equiv.perm.mem_support, hπs, mem_univ] },
    cases hπ.exists_pow_eq hπ1 hπ2 with i hi,
    replace hi : (π ^ (i % s.card)) ⟨a.fst, _⟩ = ⟨a.snd, _⟩,
    { convert hi using 2,
      convert (eq.symm pow_eq_mod_order_of),
      simp only [equiv.perm.order_of_is_cycle hπ, hπs, univ_eq_attach, card_attach] },
    refine ⟨i % s.card, _, a.1, h.1, _⟩,
    { exact nat.mod_lt _ (pos_iff_ne_zero.mpr hs) },
    { ext, refl,
      rw equiv.perm.subtype_congr.left_apply,
      { simp only [hi, subtype.coe_mk] },
      { exact h.1 } } },
  { rcases h with ⟨k, hk, b, hbs, h⟩,
    rw h,
    refine ⟨by simpa using hbs, _⟩,
    rw equiv.perm.subtype_congr.left_apply,
    simp only [coe_mem],
    exact hbs }
end

-- where to move?
lemma finset.product_self_eq_range_bUnion_perm [decidable_eq ι] (π : perm s) (hπ : π.is_cycle)
  (hπs : π.support = univ) : s.product s =
  (finset.range s.card).bUnion (λ k, s.bUnion $ λ i, {(i, (π^k).subtype_congr (equiv.refl _) i)}) :=
begin
  ext,
  obtain hs | hs := eq_or_ne s.card 0,
  { simp only [finset.card_eq_zero.mp hs, mem_product, not_mem_empty, and_self, card_empty,
      range_zero, bUnion_empty] },
  simp only [mem_bUnion, mem_range, mem_singleton, exists_prop, mem_product],
  refine ⟨λ h, _, λ h, _⟩,
  { have hπ1 : π ⟨a.1, h.1⟩ ≠ ⟨a.1, h.1⟩,
    { simp only [← equiv.perm.mem_support, hπs, mem_univ] },
    have hπ2 : π ⟨a.2, h.2⟩ ≠ ⟨a.2, h.2⟩,
    { simp only [← equiv.perm.mem_support, hπs, mem_univ] },
    cases hπ.exists_pow_eq hπ1 hπ2 with i hi,
    replace hi : (π ^ (i % s.card)) ⟨a.fst, _⟩ = ⟨a.snd, _⟩,
    { convert hi using 2,
      convert (eq.symm pow_eq_mod_order_of),
      simp only [equiv.perm.order_of_is_cycle hπ, hπs, univ_eq_attach, card_attach] },
    refine ⟨i % s.card, _, a.1, h.1, _⟩,
    { exact nat.mod_lt _ (pos_iff_ne_zero.mpr hs) },
    { ext, refl,
      rw equiv.perm.subtype_congr.left_apply,
      { simp only [hi, subtype.coe_mk] },
      { exact h.1 } } },
  { rcases h with ⟨k, hk, b, hbs, h⟩,
    rw h,
    refine ⟨by simpa using hbs, _⟩,
    rw equiv.perm.subtype_congr.left_apply,
    simp only [coe_mem],
    exact hbs }
end

-- where to move?
lemma sum_mul_sum_eq_sum_perm [decidable_eq ι] (s : finset ι) (π : perm s) (hπ : π.is_cycle)
  (hπs : π.support = univ) : (∑ i in s, f i) • (∑ i in s, g i) =
    ∑ k in finset.range s.card, (∑ i in s, f i • g ((π^k).subtype_congr (equiv.refl _) i)) :=
begin
  rw [finset.sum_smul_sum, finset.product_self_eq_range_bUnion_perm π hπ hπs, finset.sum_bUnion _],
  { refine finset.sum_congr rfl (λ x hx, _),
    rw finset.sum_bUnion _,
    { exact finset.sum_congr rfl (λ y hy, sum_singleton) },
    rintros a ha b hb hab ⟨c, d⟩ h,
    simp only [inf_eq_inter, mem_inter, mem_singleton, prod.mk.inj_iff] at h,
    exfalso, apply hab,
    rw [← h.1.1, h.2.1] },
  rintros a ha b hb hab ⟨c, d⟩ h,
  simp only [inf_eq_inter, mem_inter, mem_bUnion, mem_singleton, prod.mk.inj_iff,
    exists_prop] at h,
  rcases h with ⟨⟨e, he⟩, ⟨f, hf⟩⟩,
  have h : ((π ^ a).subtype_congr (equiv.refl {a // a ∉ s})) c =
    ((π ^ b).subtype_congr (equiv.refl {a // a ∉ s})) c,
  { conv_lhs { rw [he.2.1, ← he.2.2, hf.2.2, ← hf.2.1] } },
  have hc : c ∈ s := by simp only [he.2.1, he.1],
  replace h : (π ^ a) ⟨c, hc⟩ = (π ^ b) ⟨c, hc⟩,
  { rw [subtype_congr.left_apply _] at h,
    swap, exact hc,
    rw [subtype_congr.left_apply _] at h,
    swap, exact hc,
    simp only [← @subtype.coe_inj ι _ _, h] },
  replace h : π ^ a = π ^ b,
  { rw is_cycle.pow_eq_pow_iff hπ,
    exact ⟨⟨c, hc⟩, mem_support.1 $ by simp only [hπs, mem_univ], h⟩ },
  simp only [pow_eq_pow_iff_modeq, equiv.perm.order_of_is_cycle hπ, hπs,
    univ_eq_attach, card_attach] at h,
  exfalso,
  apply hab,
  rw [nat.modeq.eq_of_modeq_of_abs_lt h _],
  rw abs_sub_lt_iff,
  simp only [mem_coe, mem_range] at *,
  split; linarith
end

end to_move

open equiv equiv.perm finset function order_dual
open_locale big_operators

variables {ι α β : Type*}

/-! ### Scalar multiplication versions -/

section smul
variables [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {s : finset ι} {σ : perm ι} {f : ι → α} {g : ι → β}

/-- **Chebyshev Inequality**: When `f` and `g` monovary together, the scalar product of their sum is
less than the size of the set times their scalar product. -/
lemma monovary_on.sum_smul_sum_le_card_smul_sum (hfg : monovary_on f g s) :
  (∑ i in s, f i) • ∑ i in s, g i ≤ s.card • ∑ i in s, f i • g i :=
begin
  classical,
  set π : perm ι := s.to_list.form_perm with hπ,
  have hπc : π.is_cycle_on s,
  { convert s.nodup_to_list.is_cycle_on_form_perm,
    simp_rw [mem_to_list, set_of_mem] },
  rw sum_smul_sum,
  rw sum_product,
  dsimp,
  -- rw sum_mul_sum_eq_sum_perm s π hπc hπs,
  -- have : ∑ (k : ℕ) in range s.card,
  -- ∑ (i : ι) in s, f i • g (((π ^ k).subtype_congr (equiv.refl _)) i) ≤
  --   ∑ (k : ℕ) in range s.card, ∑ (i : ι) in s, f i • g i,
  -- { refine finset.sum_le_sum (λ k hk, _),
  --   convert monovary_on.sum_smul_comp_perm_le_sum_smul hfg (λ x hx, _),
  --   contrapose! hx,
  --   simp only [set.mem_set_of_eq, not_not],
  --   rw equiv.perm.subtype_congr.right_apply,
  --   simp only [coe_refl, id.def, subtype.coe_mk],
  --   contrapose! hx,
  --   exact mem_coe.mpr hx },
  -- rwa [sum_const, card_range] at this,
end

/-- **Chebyshev Inequality**: When `f` and `g` antivary together, the scalar product of their sum is
less than the size of the set times their scalar product. -/
lemma antivary_on.card_smul_sum_le_sum_smul_sum (hfg : antivary_on f g s) :
  s.card • ∑ i in s, f i • g i ≤ (∑ i in s, f i) • ∑ i in s, g i :=
by convert hfg.dual_right.sum_smul_sum_le_card_smul_sum

variables [fintype ι]

/-- **Chebyshev Inequality**: When `f` and `g` monovary together, the scalar product of their sum is
less than the size of the set times their scalar product. -/
lemma monovary.sum_smul_sum_le_card_smul_sum (hfg : monovary f g) :
  (∑ i, f i) • ∑ i, g i ≤ fintype.card ι • ∑ i, f i • g i :=
(hfg.monovary_on _).sum_smul_sum_le_card_smul_sum

/-- **Chebyshev Inequality**: When `f` and `g` antivary together, the scalar product of their sum is
less than the size of the set times their scalar product. -/
lemma antivary.card_smul_sum_le_sum_smul_sum (hfg : antivary f g) :
  fintype.card ι • ∑ i, f i • g i ≤ (∑ i, f i) • ∑ i, g i :=
by convert (hfg.dual_right.monovary_on _).sum_smul_sum_le_card_smul_sum

end smul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/

section mul
variables [linear_ordered_ring α] {s : finset ι} {σ : perm ι} {f g : ι → α}

/-- **Chebyshev Inequality**: When `f` and `g` monovary together, the product of their sum is
less than the size of the set times their scalar product. -/
lemma monovary_on.sum_mul_sum_le_card_mul_sum (hfg : monovary_on f g s) :
  (∑ i in s, f i) * ∑ i in s, g i ≤ s.card * ∑ i in s, f i * g i :=
by { rw ←nsmul_eq_mul, exact hfg.sum_smul_sum_le_card_smul_sum }

/-- **Chebyshev Inequality**: When `f` and `g` antivary together, the product of their sum is
greater than the size of the set times their scalar product. -/
lemma antivary_on.card_mul_sum_le_sum_mul_sum (hfg : antivary_on f g s) :
  (s.card : α) * ∑ i in s, f i * g i ≤ (∑ i in s, f i) * ∑ i in s, g i :=
by { rw ←nsmul_eq_mul, exact hfg.card_smul_sum_le_sum_smul_sum }

/-- **Chebyshev Inequality**: The square of the sum is less than the size of the set times the sum
of the squares. -/
lemma sq_sum_le_card_mul_sum_sq : (∑ i in s, f i)^2 ≤ s.card * ∑ i in s, f i ^ 2 :=
by { simp_rw sq, exact (monovary_on_self _ _).sum_mul_sum_le_card_mul_sum }

variables [fintype ι]

/-- **Chebyshev Inequality**: When `f` and `g` monovary together, the product of their sum is less
than the size of the set times their scalar product. -/
lemma monovary.sum_mul_sum_le_card_mul_sum (hfg : monovary f g) :
  (∑ i, f i) * ∑ i, g i ≤ fintype.card ι * ∑ i, f i * g i :=
(hfg.monovary_on _).sum_mul_sum_le_card_mul_sum

/-- **Chebyshev Inequality**: When `f` and `g` antivary together, the product of their sum is less
than the size of the set times their scalar product. -/
lemma antivary.card_mul_sum_le_sum_mul_sum (hfg : antivary f g) :
  (fintype.card ι : α) * ∑ i, f i * g i ≤ (∑ i, f i) * ∑ i, g i :=
(hfg.antivary_on _).card_mul_sum_le_sum_mul_sum

end mul
