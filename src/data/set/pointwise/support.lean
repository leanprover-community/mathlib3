/-
Copyright (c) 2022 Sébastien Gouëzel. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel
-/
import data.set.pointwise.smul
import algebra.support

/-!
# Support of a function composed with a scalar action

> THIS FILE IS SYNCHRONIZED WITH MATHLIB4.
> Any changes to this file require a corresponding PR to mathlib4.

We show that the support of `x ↦ f (c⁻¹ • x)` is equal to `c • support f`.
-/

open_locale pointwise
open function set

section group

variables {α β γ : Type*} [group α] [mul_action α β]

lemma mul_support_comp_inv_smul [has_one γ] (c : α) (f : β → γ) :
  mul_support (λ x, f (c⁻¹ • x)) = c • mul_support f :=
by { ext x, simp only [mem_smul_set_iff_inv_smul_mem, mem_mul_support] }

lemma support_comp_inv_smul [has_zero γ] (c : α) (f : β → γ) :
  support (λ x, f (c⁻¹ • x)) = c • support f :=
by { ext x, simp only [mem_smul_set_iff_inv_smul_mem, mem_support] }

attribute [to_additive support_comp_inv_smul] mul_support_comp_inv_smul

end group

section group_with_zero

variables {α β γ : Type*} [group_with_zero α] [mul_action α β]

lemma mul_support_comp_inv_smul₀ [has_one γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
  mul_support (λ x, f (c⁻¹ • x)) = c • mul_support f :=
by { ext x, simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_mul_support] }

lemma support_comp_inv_smul₀ [has_zero γ] {c : α} (hc : c ≠ 0) (f : β → γ) :
  support (λ x, f (c⁻¹ • x)) = c • support f :=
by { ext x, simp only [mem_smul_set_iff_inv_smul_mem₀ hc, mem_support] }

attribute [to_additive support_comp_inv_smul₀] mul_support_comp_inv_smul₀

end group_with_zero
