/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.order.module
import data.prod.lex
import group_theory.perm.support
import order.monovary
import tactic.abel

/-!
# Rearrangement inequality

This file proves the rearrangement inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because it is easily deducible from the `monovary` API.
-/

open equiv equiv.perm finset order_dual
open_locale big_operators

variables {ι α β : Type*}

/-! ### Scalar multiplication versions -/

section smul
variables [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {s : finset ι} {σ : perm ι} {f : ι → α} {g : ι → β}

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `g`.  -/
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
`f` and `g` vary together. Stated by permuting the entries of `f`. -/
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
`f` and `g` vary together. Stated by permuting the entries of `g`.  -/
lemma monovary.sum_smul_comp_perm_le_sum_smul (hfg : monovary f g) :
  ∑ i, f i • g (σ i) ≤ ∑ i, f i • g i :=
(hfg.monovary_on _).sum_smul_comp_perm_le_sum_smul $ λ i _, mem_univ _

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` vary together. Stated by permuting the entries of `f`. -/
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
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/

section mul
variables [linear_ordered_ring α] {s : finset ι} {σ : perm ι} {f g : ι → α}

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `g`.  -/
lemma monovary_on.sum_mul_comp_perm_le_sum_mul (hfg : monovary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g (σ i) ≤ ∑ i in s, f i * g i :=
hfg.sum_smul_comp_perm_le_sum_smul hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `f`. -/
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

variables [fintype ι]

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `g`.  -/
lemma monovary.sum_mul_comp_perm_le_sum_mul (hfg : monovary f g) :
  ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i :=
hfg.sum_smul_comp_perm_le_sum_smul

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` vary together. Stated by permuting the entries of `f`. -/
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

end mul
