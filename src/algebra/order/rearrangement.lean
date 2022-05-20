/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.big_operators.order
import algebra.order.module
import data.prod.lex
import group_theory.perm.concrete_cycle
import order.monovary
import tactic.interval_cases

/-!
# Rearrangement inequality

This file proves the rearrangement inequality and Chebyshev's inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

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

open equiv equiv.perm finset order_dual
open_locale big_operators

variables {ι α β : Type*}

/-! ### Rearrangement inequality -/

/-! #### Scalar multiplication versions -/

section smul
variables [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {s : finset ι} {σ : perm ι} {f : ι → α} {g : ι → β}

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `g`.  -/
lemma monovary_on.sum_smul_comp_perm_le_sum_smul (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g (σ i) ≤ ∑ i in s, f i • g i :=
begin
  classical,
  revert hσ σ hfg,
  apply finset.induction_on_max_value (λ i, to_lex (g i, f i)) s,
  { simp only [le_rfl, finset.sum_empty, implies_true_iff] },
  intros a s has hamax hind σ hfg hσ,
  set τ : perm ι := σ.trans (swap a (σ a)) with hτ,
  have hτs : {x | τ x ≠ x} ⊆ s,
  { intros x hx,
    simp only [ne.def, set.mem_set_of_eq, equiv.coe_trans, equiv.swap_comp_apply] at hx,
    split_ifs at hx with h₁ h₂ h₃,
    { obtain rfl | hax := eq_or_ne x a,
      { contradiction },
      { exact mem_of_mem_insert_of_ne (hσ $ λ h, hax $ h.symm.trans h₁) hax } },
    { exact (hx $ σ.injective h₂.symm).elim },
    { exact mem_of_mem_insert_of_ne (hσ hx) (ne_of_apply_ne _ h₂) } },
  specialize hind (hfg.subset $ subset_insert _ _) hτs,
  simp_rw sum_insert has,
  refine le_trans _ (add_le_add_left hind _),
  obtain hσa | hσa := eq_or_ne a (σ a),
  { rw [←hσa, swap_self, trans_refl] at hτ,
    rw [←hσa, hτ] },
  have h1s : σ⁻¹ a ∈ s,
  { rw [ne.def, ←inv_eq_iff_eq] at hσa,
    refine mem_of_mem_insert_of_ne (hσ $ λ h, hσa _) hσa,
    rwa [apply_inv_self, eq_comm] at h },
  simp only [← s.sum_erase_add _ h1s, add_comm],
  rw [← add_assoc, ← add_assoc],
  refine add_le_add _ (sum_congr rfl $ λ x hx, _).le,
  { simp only [hτ, swap_apply_left, function.comp_app, equiv.coe_trans, apply_inv_self],
    suffices : 0 ≤ (f a - f (σ⁻¹ a)) • (g a - g (σ a)),
    { rw ← sub_nonneg,
      convert this,
      simp only [smul_sub, sub_smul],
      abel },
    refine smul_nonneg (sub_nonneg_of_le _) (sub_nonneg_of_le _),
    { specialize hamax (σ⁻¹ a) h1s,
      rw prod.lex.le_iff at hamax,
      cases hamax,
      { exact hfg (mem_insert_of_mem h1s) (mem_insert_self _ _) hamax },
      { exact hamax.2 } },
    { specialize hamax (σ a) (mem_of_mem_insert_of_ne (hσ $ σ.injective.ne hσa.symm) hσa.symm),
      rw prod.lex.le_iff at hamax,
      cases hamax,
      { exact hamax.le },
      { exact hamax.1.le } } },
  { congr' 2,
    rw [eq_comm, hτ],
    rw [mem_erase, ne.def, eq_inv_iff_eq] at hx,
    refine swap_apply_of_ne_of_ne hx.1 (σ.injective.ne _),
    rintro rfl,
    exact has hx.2 }
end

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_smul_le_sum_smul (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) • g i ≤ ∑ i in s, f i • g i :=
begin
  convert hfg.sum_smul_comp_perm_le_sum_smul
    (show {x | σ⁻¹ x ≠ x} ⊆ s, by simp only [set_support_inv_eq, hσ]) using 1,
  exact σ.sum_comp' s (λ i j, f i • g j) hσ,
end

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`.-/
lemma antivary_on.sum_smul_le_sum_smul_comp_perm (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f i • g (σ i) :=
hfg.dual_right.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_smul_le_sum_comp_perm_smul (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f (σ i) • g i :=
hfg.dual_right.sum_comp_perm_smul_le_sum_smul hσ

variables [fintype ι]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `g`.  -/
lemma monovary.sum_smul_comp_perm_le_sum_smul (hfg : monovary f g) :
  ∑ i, f i • g (σ i) ≤ ∑ i, f i • g i :=
(hfg.monovary_on _).sum_smul_comp_perm_le_sum_smul $ λ i _, mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `f`. -/
lemma monovary.sum_comp_perm_smul_le_sum_smul (hfg : monovary f g) :
  ∑ i, f (σ i) • g i ≤ ∑ i, f i • g i :=
(hfg.monovary_on _).sum_comp_perm_smul_le_sum_smul $ λ i _, mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`.-/
lemma antivary.sum_smul_le_sum_smul_comp_perm (hfg : antivary f g) :
  ∑ i, f i • g i ≤ ∑ i, f i • g (σ i) :=
(hfg.antivary_on _).sum_smul_le_sum_smul_comp_perm $ λ i _, mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_smul_le_sum_comp_perm_smul (hfg : antivary f g) :
  ∑ i, f i • g i ≤ ∑ i, f (σ i) • g i :=
(hfg.antivary_on _).sum_smul_le_sum_comp_perm_smul $ λ i _, mem_univ _

end smul

/-!
#### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/

section mul
variables [linear_ordered_ring α] {s : finset ι} {σ : perm ι} {f g : ι → α}

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `g`.  -/
lemma monovary_on.sum_mul_comp_perm_le_sum_mul (hfg : monovary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g (σ i) ≤ ∑ i in s, f i * g i :=
hfg.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_mul_le_sum_mul (hfg : monovary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) * g i ≤ ∑ i in s, f i * g i :=
hfg.sum_comp_perm_smul_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`.-/
lemma antivary_on.sum_mul_le_sum_mul_comp_perm (hfg : antivary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g i ≤ ∑ i in s, f i * g (σ i) :=
hfg.sum_smul_le_sum_smul_comp_perm hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_mul_le_sum_comp_perm_mul (hfg : antivary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g i ≤ ∑ i in s, f (σ i) * g i :=
hfg.sum_smul_le_sum_comp_perm_smul hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and a permutation of `f` is
maximized when the permutation is the identity.  -/
lemma sum_mul_comp_perm_le_sum_sq_of_subset (f : ι → α) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * f (σ i) ≤ ∑ i in s, f i ^ 2 :=
by { simp_rw sq, exact (monovary_on_self _ _).sum_mul_comp_perm_le_sum_mul hσ }

/-- **Rearrangement Inequality**: Pointwise multiplication of a permutation of `f` and `f` is
maximized when the permutation is the identity.  -/
lemma sum_comp_perm_mul_le_sum_sq_of_subset (f : ι → α) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) * f i ≤ ∑ i in s, f i ^ 2 :=
by { simp_rw sq, exact (monovary_on_self _ _).sum_comp_perm_mul_le_sum_mul hσ }

variables [fintype ι]

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `g`.  -/
lemma monovary.sum_mul_comp_perm_le_sum_mul (hfg : monovary f g) :
  ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i :=
hfg.sum_smul_comp_perm_le_sum_smul

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `f`. -/
lemma monovary.sum_comp_perm_mul_le_sum_mul (hfg : monovary f g) :
  ∑ i, f (σ i) * g i ≤ ∑ i, f i * g i :=
hfg.sum_comp_perm_smul_le_sum_smul

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`.-/
lemma antivary.sum_mul_le_sum_mul_comp_perm (hfg : antivary f g) :
  ∑ i, f i * g i ≤ ∑ i, f i * g (σ i) :=
hfg.sum_smul_le_sum_smul_comp_perm

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_mul_le_sum_comp_perm_mul (hfg : antivary f g) :
  ∑ i, f i * g i ≤ ∑ i, f (σ i) * g i :=
hfg.sum_smul_le_sum_comp_perm_smul

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and a permutation of `f` is
maximized when the permutation is the identity.  -/
lemma sum_mul_comp_perm_le_sum_mul (f : ι → α) (σ : perm ι) : ∑ i, f i * f (σ i) ≤ ∑ i, f i ^ 2 :=
sum_mul_comp_perm_le_sum_sq_of_subset _ $ by { rw coe_univ, exact set.subset_univ _ }

/-- **Rearrangement Inequality**: Pointwise multiplication of a permutation of `f` and `f` is
maximized when the permutation is the identity.  -/
lemma sum_comp_perm_mul_le_sum_sq (f : ι → α) (σ : perm ι) : ∑ i, f (σ i) * f i ≤ ∑ i, f i ^ 2 :=
sum_comp_perm_mul_le_sum_sq_of_subset _ $ by { rw coe_univ, exact set.subset_univ _ }

end mul

/-! ### Chebyshev inequality -/

/-! #### Scalar multiplication versions -/

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
#### Multiplication versions

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
