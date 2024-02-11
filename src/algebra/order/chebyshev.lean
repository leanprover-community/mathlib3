/-
Copyright (c) 2023 Mantas Bakšys, Yaël Dillies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mantas Bakšys, Yaël Dillies
-/
import algebra.big_operators.order
import algebra.order.rearrangement
import group_theory.perm.cycle.basic

/-!
# Chebyshev's sum inequality

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

This file proves the Chebyshev sum inequality.

Chebyshev's inequality states `(∑ i in s, f i) * (∑ i in s, g i) ≤ s.card * ∑ i in s, f i * g i`
when `f g : ι → α` monovary, and the reverse inequality when `f` and `g` antivary.


## Main declarations

* `monovary_on.sum_mul_sum_le_card_mul_sum`: Chebyshev's inequality.
* `antivary_on.card_mul_sum_le_sum_mul_sum`: Chebyshev's inequality, dual version.
* `sq_sum_le_card_mul_sum_sq`: Special case of Chebyshev's inequality when `f = g`.

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

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
lemma monovary_on.sum_smul_sum_le_card_smul_sum (hfg : monovary_on f g s) :
  (∑ i in s, f i) • ∑ i in s, g i ≤ s.card • ∑ i in s, f i • g i :=
begin
  classical,
  obtain ⟨σ, hσ, hs⟩ := s.countable_to_set.exists_cycle_on,
  rw [←card_range s.card, sum_smul_sum_eq_sum_perm hσ],
  exact sum_le_card_nsmul _ _ _ (λ n _, hfg.sum_smul_comp_perm_le_sum_smul $ λ x hx, hs $ λ h, hx $
    is_fixed_pt.perm_pow h _),
end

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
lemma antivary_on.card_smul_sum_le_sum_smul_sum (hfg : antivary_on f g s) :
  s.card • ∑ i in s, f i • g i ≤ (∑ i in s, f i) • ∑ i in s, g i :=
by convert hfg.dual_right.sum_smul_sum_le_card_smul_sum

variables [fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
lemma monovary.sum_smul_sum_le_card_smul_sum (hfg : monovary f g) :
  (∑ i, f i) • ∑ i, g i ≤ fintype.card ι • ∑ i, f i • g i :=
(hfg.monovary_on _).sum_smul_sum_le_card_smul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the scalar product of their sum is less than the size of the set times their
scalar product. -/
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

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
lemma monovary_on.sum_mul_sum_le_card_mul_sum (hfg : monovary_on f g s) :
  (∑ i in s, f i) * (∑ i in s, g i) ≤ s.card * ∑ i in s, f i * g i :=
by { rw ←nsmul_eq_mul, exact hfg.sum_smul_sum_le_card_smul_sum }

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the product of their sum is greater than the size of the set times their scalar
product. -/
lemma antivary_on.card_mul_sum_le_sum_mul_sum (hfg : antivary_on f g s) :
  (s.card : α) * ∑ i in s, f i * g i ≤ (∑ i in s, f i) * (∑ i in s, g i) :=
by { rw ←nsmul_eq_mul, exact hfg.card_smul_sum_le_sum_smul_sum }

/-- Special case of **Chebyshev's Sum Inequality** or the **Cauchy-Schwarz Inequality**: The square
of the sum is less than the size of the set times the sum of the squares. -/
lemma sq_sum_le_card_mul_sum_sq : (∑ i in s, f i)^2 ≤ s.card * ∑ i in s, f i ^ 2 :=
by { simp_rw sq, exact (monovary_on_self _ _).sum_mul_sum_le_card_mul_sum }

variables [fintype ι]

/-- **Chebyshev's Sum Inequality**: When `f` and `g` monovary together (eg they are both
monotone/antitone), the product of their sum is less than the size of the set times their scalar
product. -/
lemma monovary.sum_mul_sum_le_card_mul_sum (hfg : monovary f g) :
  (∑ i, f i) * (∑ i, g i) ≤ fintype.card ι * ∑ i, f i * g i :=
(hfg.monovary_on _).sum_mul_sum_le_card_mul_sum

/-- **Chebyshev's Sum Inequality**: When `f` and `g` antivary together (eg one is monotone, the
other is antitone), the product of their sum is less than the size of the set times their scalar
product. -/
lemma antivary.card_mul_sum_le_sum_mul_sum (hfg : antivary f g) :
  (fintype.card ι : α) * ∑ i, f i * g i ≤ (∑ i, f i) * (∑ i, g i) :=
(hfg.antivary_on _).card_mul_sum_le_sum_mul_sum

end mul

variables [linear_ordered_field α] {s : finset ι} {f : ι → α}

lemma sum_div_card_sq_le_sum_sq_div_card :
  ((∑ i in s, f i) / s.card) ^ 2 ≤ (∑ i in s, f i ^ 2) / s.card :=
begin
  obtain rfl | hs := s.eq_empty_or_nonempty,
  { simp },
  rw [←card_pos, ←@nat.cast_pos α] at hs,
  rw [div_pow, div_le_div_iff (sq_pos_of_ne_zero _ hs.ne') hs, sq (s.card : α), mul_left_comm,
    ←mul_assoc],
  exact mul_le_mul_of_nonneg_right (sq_sum_le_card_mul_sum_sq) hs.le,
end
