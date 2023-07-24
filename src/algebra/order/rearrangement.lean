/-
Copyright (c) 2022 Mantas Bakšys. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys
-/
import algebra.big_operators.basic
import algebra.order.module
import data.prod.lex
import group_theory.perm.support
import order.monotone.monovary
import tactic.abel

/-!
# Rearrangement inequality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the rearrangement inequality and deduces the conditions for equality and strict
inequality.

The rearrangement inequality tells you that for two functions `f g : ι → α`, the sum
`∑ i, f i * g (σ i)` is maximized over all `σ : perm ι` when `g ∘ σ` monovaries with `f` and
minimized when `g ∘ σ` antivaries with `f`.

The inequality also tells you that `∑ i, f i * g (σ i) = ∑ i, f i * g i` if and only if `g ∘ σ`
monovaries with `f` when `g` monovaries with `f`. The above equality also holds if and only if
`g ∘ σ` antivaries with `f` when `g` antivaries with `f`.

From the above two statements, we deduce that the inequality is strict if and only if `g ∘ σ` does
not monovary with `f` when `g` monovaries with `f`. Analogously, the inequality is strict if and
only if `g ∘ σ` does not antivary with `f` when `g` antivaries with `f`.

## Implementation notes

In fact, we don't need much compatibility between the addition and multiplication of `α`, so we can
actually decouple them by replacing multiplication with scalar multiplication and making `f` and `g`
land in different types.
As a bonus, this makes the dual statement trivial. The multiplication versions are provided for
convenience.

The case for `monotone`/`antitone` pairs of functions over a `linear_order` is not deduced in this
file because it is easily deducible from the `monovary` API.
-/

open equiv equiv.perm finset function order_dual
open_locale big_operators

variables {ι α β : Type*}

/-! ### Scalar multiplication versions -/

section smul
variables [linear_ordered_ring α] [linear_ordered_add_comm_group β] [module α β]
  [ordered_smul α β] {s : finset ι} {σ : perm ι} {f : ι → α} {g : ι → β}

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `g`. -/
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
  { rw [hτ, ←hσa, swap_self, trans_refl] },
  have h1s : σ⁻¹ a ∈ s,
  { rw [ne.def, ←inv_eq_iff_eq] at hσa,
    refine mem_of_mem_insert_of_ne (hσ $ λ h, hσa _) hσa,
    rwa [apply_inv_self, eq_comm] at h },
  simp only [← s.sum_erase_add _ h1s, add_comm],
  rw [← add_assoc, ← add_assoc],
  simp only [hτ, swap_apply_left, function.comp_app, equiv.coe_trans, apply_inv_self],
  refine add_le_add (smul_add_smul_le_smul_add_smul' _ _) (sum_congr rfl $ λ x hx, _).le,
  { specialize hamax (σ⁻¹ a) h1s,
    rw prod.lex.le_iff at hamax,
    cases hamax,
    { exact hfg (mem_insert_of_mem h1s) (mem_insert_self _ _) hamax },
    { exact hamax.2 } },
  { specialize hamax (σ a) (mem_of_mem_insert_of_ne (hσ $ σ.injective.ne hσa.symm) hσa.symm),
    rw prod.lex.le_iff at hamax,
    cases hamax,
    { exact hamax.le },
    { exact hamax.1.le } },
  { rw [mem_erase, ne.def, eq_inv_iff_eq] at hx,
    rw swap_apply_of_ne_of_ne hx.1 (σ.injective.ne _),
    rintro rfl,
    exact has hx.2 }
end

/-- **Equality case of Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
lemma monovary_on.sum_smul_comp_perm_eq_sum_smul_iff (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g (σ i) = ∑ i in s, f i • g i ↔ monovary_on f (g ∘ σ) s :=
begin
  classical,
  refine ⟨not_imp_not.1 $ λ h, _, λ h, (hfg.sum_smul_comp_perm_le_sum_smul hσ).antisymm _⟩,
  { rw monovary_on at h,
    push_neg at h,
    obtain ⟨x, hx, y, hy, hgxy, hfxy⟩ := h,
    set τ : perm ι := (swap x y).trans σ,
    have hτs : {x | τ x ≠ x} ⊆ s,
    { refine (set_support_mul_subset σ $ swap x y).trans (set.union_subset hσ $ λ z hz, _),
      obtain ⟨_, rfl | rfl⟩ := swap_apply_ne_self_iff.1 hz; assumption },
    refine ((hfg.sum_smul_comp_perm_le_sum_smul hτs).trans_lt' _).ne,
    obtain rfl | hxy := eq_or_ne x y,
    { cases lt_irrefl _ hfxy },
    simp only [←s.sum_erase_add _ hx, ←(s.erase x).sum_erase_add _ (mem_erase.2 ⟨hxy.symm, hy⟩),
      add_assoc, equiv.coe_trans, function.comp_app, swap_apply_right, swap_apply_left],
    refine add_lt_add_of_le_of_lt (finset.sum_congr rfl $ λ z hz, _).le
      (smul_add_smul_lt_smul_add_smul hfxy hgxy),
    simp_rw mem_erase at hz,
    rw swap_apply_of_ne_of_ne hz.2.1 hz.1 },
  { convert h.sum_smul_comp_perm_le_sum_smul ((set_support_inv_eq _).subset.trans hσ) using 1,
    simp_rw [function.comp_app, apply_inv_self] }
end

/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
lemma monovary_on.sum_smul_comp_perm_lt_sum_smul_iff (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g (σ i) < ∑ i in s, f i • g i ↔ ¬ monovary_on f (g ∘ σ) s :=
by simp [←hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ,
  lt_iff_le_and_ne, hfg.sum_smul_comp_perm_le_sum_smul hσ]

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

/-- **Equality case of Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_smul_eq_sum_smul_iff (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) • g i = ∑ i in s, f i • g i ↔ monovary_on (f ∘ σ) g s :=
begin
  have hσinv : {x | σ⁻¹ x ≠ x} ⊆ s := (set_support_inv_eq _).subset.trans hσ,
  refine (iff.trans _ $ hfg.sum_smul_comp_perm_eq_sum_smul_iff hσinv).trans ⟨λ h, _, λ h, _⟩,
  { simpa only [σ.sum_comp' s (λ i j, f i • g j) hσ] },
  { convert h.comp_right σ,
    { rw [comp.assoc, inv_def, symm_comp_self, comp.right_id] },
    { rw [σ.eq_preimage_iff_image_eq, set.image_perm hσ] } },
  { convert h.comp_right σ.symm,
    { rw [comp.assoc, self_comp_symm, comp.right_id] },
    { rw σ.symm.eq_preimage_iff_image_eq,
      exact set.image_perm hσinv } }
end

/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not monovary together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_smul_lt_sum_smul_iff (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) • g i < ∑ i in s, f i • g i ↔ ¬ monovary_on (f ∘ σ) g s :=
by simp [←hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ,
  lt_iff_le_and_ne, hfg.sum_comp_perm_smul_le_sum_smul hσ]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`. -/
lemma antivary_on.sum_smul_le_sum_smul_comp_perm (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f i • g (σ i) :=
hfg.dual_right.sum_smul_comp_perm_le_sum_smul hσ

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
lemma antivary_on.sum_smul_eq_sum_smul_comp_perm_iff (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g (σ i) = ∑ i in s, f i • g i ↔ antivary_on f (g ∘ σ) s :=
(hfg.dual_right.sum_smul_comp_perm_eq_sum_smul_iff hσ).trans monovary_on_to_dual_right

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
lemma antivary_on.sum_smul_lt_sum_smul_comp_perm_iff (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i < ∑ i in s, f i • g (σ i) ↔ ¬ antivary_on f (g ∘ σ) s :=
by simp [←hfg.sum_smul_eq_sum_smul_comp_perm_iff hσ, lt_iff_le_and_ne, eq_comm,
  hfg.sum_smul_le_sum_smul_comp_perm hσ]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_smul_le_sum_comp_perm_smul (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i ≤ ∑ i in s, f (σ i) • g i :=
hfg.dual_right.sum_comp_perm_smul_le_sum_smul hσ

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_smul_eq_sum_comp_perm_smul_iff (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) • g i = ∑ i in s, f i • g i ↔ antivary_on (f ∘ σ) g s :=
(hfg.dual_right.sum_comp_perm_smul_eq_sum_smul_iff hσ).trans monovary_on_to_dual_right

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_smul_lt_sum_comp_perm_smul_iff (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g i < ∑ i in s, f (σ i) • g i ↔ ¬ antivary_on (f ∘ σ) g s :=
by simp [←hfg.sum_smul_eq_sum_comp_perm_smul_iff hσ, eq_comm, lt_iff_le_and_ne,
  hfg.sum_smul_le_sum_comp_perm_smul hσ]

variables [fintype ι]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_smul_comp_perm_le_sum_smul (hfg : monovary f g) :
  ∑ i, f i • g (σ i) ≤ ∑ i, f i • g i :=
(hfg.monovary_on _).sum_smul_comp_perm_le_sum_smul $ λ i _, mem_univ _

/-- **Equality case of Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_smul_comp_perm_eq_sum_smul_iff (hfg : monovary f g) :
  ∑ i, f i • g (σ i) = ∑ i, f i • g i ↔ monovary f (g ∘ σ) :=
by simp [(hfg.monovary_on _).sum_smul_comp_perm_eq_sum_smul_iff (λ i _, mem_univ _)]

/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_smul_comp_perm_lt_sum_smul_iff (hfg : monovary f g) :
  ∑ i, f i • g (σ i) < ∑ i, f i • g i ↔ ¬ monovary f (g ∘ σ) :=
by simp [(hfg.monovary_on _).sum_smul_comp_perm_lt_sum_smul_iff (λ i _, mem_univ _)]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is maximized when
`f` and `g` monovary together. Stated by permuting the entries of `f`. -/
lemma monovary.sum_comp_perm_smul_le_sum_smul (hfg : monovary f g) :
  ∑ i, f (σ i) • g i ≤ ∑ i, f i • g i :=
(hfg.monovary_on _).sum_comp_perm_smul_le_sum_smul $ λ i _, mem_univ _

/-- **Equality case of Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_comp_perm_smul_eq_sum_smul_iff (hfg : monovary f g) :
  ∑ i, f (σ i) • g i = ∑ i, f i • g i ↔ monovary (f ∘ σ) g :=
by simp [(hfg.monovary_on _).sum_comp_perm_smul_eq_sum_smul_iff (λ i _, mem_univ _)]

/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_comp_perm_smul_lt_sum_smul_iff (hfg : monovary f g) :
   ∑ i, f (σ i) • g i < ∑ i, f i • g i ↔ ¬ monovary (f ∘ σ) g :=
by simp [(hfg.monovary_on _).sum_comp_perm_smul_lt_sum_smul_iff (λ i _, mem_univ _)]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `g`. -/
lemma antivary.sum_smul_le_sum_smul_comp_perm (hfg : antivary f g) :
  ∑ i, f i • g i ≤ ∑ i, f i • g (σ i) :=
(hfg.antivary_on _).sum_smul_le_sum_smul_comp_perm $ λ i _, mem_univ _

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
lemma antivary.sum_smul_eq_sum_smul_comp_perm_iff (hfg : antivary f g) :
  ∑ i, f i • g (σ i) = ∑ i, f i • g i ↔ antivary f (g ∘ σ) :=
by simp [(hfg.antivary_on _).sum_smul_eq_sum_smul_comp_perm_iff (λ i _, mem_univ _)]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
lemma antivary.sum_smul_lt_sum_smul_comp_perm_iff (hfg : antivary f g) :
  ∑ i, f i • g i < ∑ i, f i • g (σ i) ↔ ¬ antivary f (g ∘ σ) :=
by simp [(hfg.antivary_on _).sum_smul_lt_sum_smul_comp_perm_iff (λ i _, mem_univ _)]

/-- **Rearrangement Inequality**: Pointwise scalar multiplication of `f` and `g` is minimized when
`f` and `g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_smul_le_sum_comp_perm_smul (hfg : antivary f g) :
  ∑ i, f i • g i ≤ ∑ i, f (σ i) • g i :=
(hfg.antivary_on _).sum_smul_le_sum_comp_perm_smul $ λ i _, mem_univ _

/-- **Equality case of the Rearrangement Inequality**: Pointwise scalar multiplication of `f` and
`g`, which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_smul_eq_sum_comp_perm_smul_iff (hfg : antivary f g) :
  ∑ i, f (σ i) • g i = ∑ i, f i • g i ↔ antivary (f ∘ σ) g :=
by simp [(hfg.antivary_on _).sum_smul_eq_sum_comp_perm_smul_iff (λ i _, mem_univ _)]

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_smul_lt_sum_comp_perm_smul_iff (hfg : antivary f g) :
  ∑ i, f i • g i < ∑ i, f (σ i) • g i ↔ ¬ antivary (f ∘ σ) g :=
by simp [(hfg.antivary_on _).sum_smul_lt_sum_comp_perm_smul_iff (λ i _, mem_univ _)]

end smul

/-!
### Multiplication versions

Special cases of the above when scalar multiplication is actually multiplication.
-/

section mul
variables [linear_ordered_ring α] {s : finset ι} {σ : perm ι} {f g : ι → α}

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `g`. -/
lemma monovary_on.sum_mul_comp_perm_le_sum_mul (hfg : monovary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g (σ i) ≤ ∑ i in s, f i * g i :=
hfg.sum_smul_comp_perm_le_sum_smul hσ

/-- **Equality case of Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
lemma monovary_on.sum_mul_comp_perm_eq_sum_mul_iff (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g (σ i) = ∑ i in s, f i * g i ↔ monovary_on f (g ∘ σ) s :=
hfg.sum_smul_comp_perm_eq_sum_smul_iff hσ

/-- **Strict inequality case of Rearrangement Inequality**: Pointwise scalar multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
lemma monovary_on.sum_mul_comp_perm_lt_sum_mul_iff (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i • g (σ i) < ∑ i in s, f i • g i ↔ ¬ monovary_on f (g ∘ σ) s :=
hfg.sum_smul_comp_perm_lt_sum_smul_iff hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_mul_le_sum_mul (hfg : monovary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) * g i ≤ ∑ i in s, f i * g i :=
hfg.sum_comp_perm_smul_le_sum_smul hσ

/-- **Equality case of Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_mul_eq_sum_mul_iff (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) * g i = ∑ i in s, f i * g i ↔ monovary_on (f ∘ σ) g s :=
hfg.sum_comp_perm_smul_eq_sum_smul_iff hσ

/-- **Strict inequality case of Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not monovary together. Stated by permuting the entries of `f`. -/
lemma monovary_on.sum_comp_perm_mul_lt_sum_mul_iff (hfg : monovary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) * g i < ∑ i in s, f i * g i ↔ ¬ monovary_on (f ∘ σ) g s :=
hfg.sum_comp_perm_smul_lt_sum_smul_iff hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`. -/
lemma antivary_on.sum_mul_le_sum_mul_comp_perm (hfg : antivary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g i ≤ ∑ i in s, f i * g (σ i) :=
hfg.sum_smul_le_sum_smul_comp_perm hσ

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
lemma antivary_on.sum_mul_eq_sum_mul_comp_perm_iff (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g (σ i) = ∑ i in s, f i * g i ↔ antivary_on f (g ∘ σ) s :=
hfg.sum_smul_eq_sum_smul_comp_perm_iff hσ

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
lemma antivary_on.sum_mul_lt_sum_mul_comp_perm_iff (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g i < ∑ i in s, f i * g (σ i) ↔ ¬ antivary_on f (g ∘ σ) s :=
hfg.sum_smul_lt_sum_smul_comp_perm_iff hσ

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_mul_le_sum_comp_perm_mul (hfg : antivary_on f g s) (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g i ≤ ∑ i in s, f (σ i) * g i :=
hfg.sum_smul_le_sum_comp_perm_smul hσ

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_mul_eq_sum_comp_perm_mul_iff (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f (σ i) * g i = ∑ i in s, f i * g i ↔ antivary_on (f ∘ σ) g s :=
hfg.sum_smul_eq_sum_comp_perm_smul_iff hσ

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
lemma antivary_on.sum_mul_lt_sum_comp_perm_mul_iff (hfg : antivary_on f g s)
  (hσ : {x | σ x ≠ x} ⊆ s) :
  ∑ i in s, f i * g i < ∑ i in s, f (σ i) * g i ↔ ¬ antivary_on (f ∘ σ) g s :=
hfg.sum_smul_lt_sum_comp_perm_smul_iff hσ

variables [fintype ι]

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_mul_comp_perm_le_sum_mul (hfg : monovary f g) :
  ∑ i, f i * g (σ i) ≤ ∑ i, f i * g i :=
hfg.sum_smul_comp_perm_le_sum_smul

/-- **Equality case of Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` monovary
together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_mul_comp_perm_eq_sum_mul_iff (hfg : monovary f g) :
  ∑ i, f i * g (σ i) = ∑ i, f i * g i ↔ monovary f (g ∘ σ) :=
hfg.sum_smul_comp_perm_eq_sum_smul_iff

/-- **Strict inequality case of Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_mul_comp_perm_lt_sum_mul_iff (hfg : monovary f g) :
  ∑ i, f i * g (σ i) < ∑ i, f i * g i ↔ ¬ monovary f (g ∘ σ) :=
hfg.sum_smul_comp_perm_lt_sum_smul_iff

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is maximized when `f` and
`g` monovary together. Stated by permuting the entries of `f`. -/
lemma monovary.sum_comp_perm_mul_le_sum_mul (hfg : monovary f g) :
  ∑ i, f (σ i) * g i ≤ ∑ i, f i * g i :=
hfg.sum_comp_perm_smul_le_sum_smul

/-- **Equality case of Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which monovary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` monovary
together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_comp_perm_mul_eq_sum_mul_iff (hfg : monovary f g) :
  ∑ i, f (σ i) * g i = ∑ i, f i * g i ↔ monovary (f ∘ σ) g :=
hfg.sum_comp_perm_smul_eq_sum_smul_iff

/-- **Strict inequality case of Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which monovary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not monovary together. Stated by permuting the entries of `g`. -/
lemma monovary.sum_comp_perm_mul_lt_sum_mul_iff (hfg : monovary f g) :
   ∑ i, f (σ i) * g i < ∑ i, f i * g i ↔ ¬ monovary (f ∘ σ) g :=
hfg.sum_comp_perm_smul_lt_sum_smul_iff

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `g`. -/
lemma antivary.sum_mul_le_sum_mul_comp_perm (hfg : antivary f g) :
  ∑ i, f i * g i ≤ ∑ i, f i * g (σ i) :=
hfg.sum_smul_le_sum_smul_comp_perm

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f` and `g ∘ σ` antivary
together. Stated by permuting the entries of `g`. -/
lemma antivary.sum_mul_eq_sum_mul_comp_perm_iff (hfg : antivary f g) :
  ∑ i, f i * g (σ i) = ∑ i, f i * g i ↔ antivary f (g ∘ σ) :=
hfg.sum_smul_eq_sum_smul_comp_perm_iff

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f` and `g ∘ σ` do not antivary together. Stated by permuting the entries of `g`. -/
lemma antivary.sum_mul_lt_sum_mul_comp_perm_iff (hfg : antivary f g) :
  ∑ i, f i • g i < ∑ i, f i • g (σ i) ↔ ¬ antivary f (g ∘ σ) :=
hfg.sum_smul_lt_sum_smul_comp_perm_iff

/-- **Rearrangement Inequality**: Pointwise multiplication of `f` and `g` is minimized when `f` and
`g` antivary together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_mul_le_sum_comp_perm_mul (hfg : antivary f g) :
  ∑ i, f i * g i ≤ ∑ i, f (σ i) * g i :=
hfg.sum_smul_le_sum_comp_perm_smul

/-- **Equality case of the Rearrangement Inequality**: Pointwise multiplication of `f` and `g`,
which antivary together, is unchanged by a permutation if and only if `f ∘ σ` and `g` antivary
together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_mul_eq_sum_comp_perm_mul_iff (hfg : antivary f g) :
  ∑ i, f (σ i) * g i = ∑ i, f i * g i ↔ antivary (f ∘ σ) g :=
hfg.sum_smul_eq_sum_comp_perm_smul_iff

/-- **Strict inequality case of the Rearrangement Inequality**: Pointwise multiplication of
`f` and `g`, which antivary together, is strictly decreased by a permutation if and only if
`f ∘ σ` and `g` do not antivary together. Stated by permuting the entries of `f`. -/
lemma antivary.sum_mul_lt_sum_comp_perm_mul_iff (hfg : antivary f g) :
  ∑ i, f i * g i < ∑ i, f (σ i) * g i ↔ ¬ antivary (f ∘ σ) g :=
hfg.sum_smul_lt_sum_comp_perm_smul_iff

end mul
